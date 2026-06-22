import Plausible.Arbitrary
import Specimen.DeriveArbitrary
import Specimen.Enumerators

/-! # Vendored, self-contained slice of Strata's Lambda dialect

This file is a faithful but minimized copy of the definitions from
`Strata/DL/Lambda/{LTy,Identifiers,LExpr}.lean` and
`Strata/DL/Lambda/Denote/LExprAnnotated.lean` that are needed to state the
`LExpr.HasTypeA` typing relation. It is vendored (rather than depended on via
Lake) because Strata pins a different `plausible` revision and a different Lean
toolchain than Specimen, and uses the experimental `module` / `public import`
system; reconciling those is out of scope for this experiment.

The definitions below are copied verbatim where possible, with only the
following mechanical changes:
  * the `module` header and `public`/`public section` markers are dropped;
  * imports are reduced to what `HasTypeA` transitively needs;
  * `deriving` clauses are used in place of Strata's hand-written
    `DecidableEq`/`Repr` instances where the derived instance suffices;
  * unrelated helpers, syntax, proofs, and theorems are omitted.

Provenance is noted per-section. Keep this in sync with upstream Strata. -/

namespace Lambda

/-! ## `LTy.lean` — monomorphic types (slice) -/

/-- Type identifiers. For now, these are just strings. -/
abbrev TyIdentifier := String

/-- Monomorphic types in Lambda. (`Strata/DL/Lambda/LTy.lean`) -/
inductive LMonoTy : Type where
  /-- A type variable. -/
  | ftvar (name : TyIdentifier)
  /-- A type constructor. -/
  | tcons (name : String) (args : List LMonoTy)
  /-- A bit vector type, parameterized by a size. -/
  | bitvec (size : Nat)
  deriving Inhabited, Repr, Hashable

/-- Custom induction principle for the nested inductive `LMonoTy`. -/
@[induction_eliminator]
theorem LMonoTy.induct {P : LMonoTy → Prop}
  (ftvar : ∀f, P (.ftvar f))
  (bitvec : ∀n, P (.bitvec n))
  (tcons : ∀name args, (∀ ty ∈ args, P ty) → P (.tcons name args)) :
  ∀ ty, P ty := by
  intro n
  apply LMonoTy.rec <;> try assumption
  case nil => simp
  case cons =>
    intro head tail h_head h_tail
    simp_all
  done

/-- Boolean equality for `LMonoTy`. (`Strata/DL/Lambda/LTy.lean`) -/
def LMonoTy.BEq (x y : LMonoTy) : Bool :=
  match x, y with
  | .ftvar i, .ftvar j => i == j
  | .bitvec i, .bitvec j => i == j
  | .tcons i1 j1, .tcons i2 j2 =>
    i1 == i2 && j1.length == j2.length && go j1 j2
  | _, _ => false
  where go j1 j2 :=
  match j1, j2 with
  | [], _ => true
  | _, [] => true
  | x :: xrest, y :: yrest =>
    LMonoTy.BEq x y && go xrest yrest

@[simp]
theorem LMonoTy.BEq_refl : LMonoTy.BEq ty ty := by
  induction ty <;> simp_all [LMonoTy.BEq]
  rename_i name args ih
  induction args
  case tcons.nil => simp [LMonoTy.BEq.go]
  case tcons.cons =>
    rename_i head tail ih'
    simp_all [LMonoTy.BEq.go]
  done

instance : DecidableEq LMonoTy :=
  fun x y =>
    if h: LMonoTy.BEq x y then
      isTrue (by
                induction x generalizing y
                case ftvar =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case bitvec =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case tcons =>
                  rename_i name args ih
                  cases y <;> try simp_all [LMonoTy.BEq]
                  rename_i name' args'
                  obtain ⟨⟨h1, h2⟩, h3⟩ := h
                  induction args generalizing args'
                  case nil => unfold List.length at h2; split at h2 <;> simp_all
                  case cons head' tail' ih' =>
                    unfold LMonoTy.BEq.go at h3 <;> split at h3 <;> try simp_all
                    rename_i j1 j2 x xrest y yrest heq
                    obtain ⟨h3_1, h3_2⟩ := h3
                    obtain ⟨ih1, ih2⟩ := ih
                    exact ⟨ih1 y h3_1, ih' ih2 yrest h3_2 rfl⟩)
    else
      isFalse (by induction x generalizing y
                  case ftvar =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case bitvec n =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case tcons name args ih =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                    rename_i name' args'
                    intro hname; simp [hname] at h
                    induction args generalizing args'
                    case tcons.nil =>
                      simp [LMonoTy.BEq.go] at h
                      unfold List.length at h; split at h <;> simp_all
                    case tcons.cons head tail ih' =>
                      cases args' <;> try simp_all
                      rename_i head' tail'; intro _
                      have ih'' := @ih' tail'
                      unfold LMonoTy.BEq.go at h
                      simp_all)

@[match_pattern] def LMonoTy.bool : LMonoTy := .tcons "bool" []
@[match_pattern] def LMonoTy.int : LMonoTy := .tcons "int" []
@[match_pattern] def LMonoTy.real : LMonoTy := .tcons "real" []
@[match_pattern] def LMonoTy.string : LMonoTy := .tcons "string" []

/-- An arrow (function) type. -/
@[match_pattern] def LMonoTy.arrow (t1 t2 : LMonoTy) : LMonoTy :=
  .tcons "arrow" [t1, t2]

/-- Return `some (dom, cod)` if the type is an arrow, `none` otherwise.
    (`Strata/DL/Lambda/LTy.lean`) -/
def LMonoTy.isArrow : LMonoTy → Option (LMonoTy × LMonoTy)
  | .tcons "arrow" [dom, cod] => some (dom, cod)
  | _ => none

/-! ## `Identifiers.lean` — identifiers (slice) -/

/-- Identifiers with a name and additional metadata. -/
structure Identifier (IDMeta : Type) : Type where
  /-- A unique name. -/
  name : String
  /-- Any additional metadata to attach to an identifier. -/
  metadata : IDMeta
  deriving Repr, DecidableEq, Inhabited

/-! ## `LExpr.lean` — expression parameters, constants, expressions (slice) -/

/-- Expected interface for pure expressions used to specialize the Lambda
dialect. (`Strata/DL/Lambda/LExpr.lean`) -/
structure LExprParams : Type 1 where
  /-- The type of metadata allowed on expressions. -/
  Metadata : Type
  /-- The type of metadata allowed on identifiers. -/
  IDMeta : Type
  deriving Inhabited

/-- Extended `LExprParams` that includes the `TypeType` parameter. -/
structure LExprParamsT : Type 1 where
  /-- The base parameters. -/
  base : LExprParams
  /-- The type of types used to annotate expressions. -/
  TypeType : Type
  deriving Inhabited

/-- `T.mono` transforms `LExprParams` into `LExprParamsT` with `LMonoTy`. -/
@[expose] abbrev LExprParams.mono (T : LExprParams) : LExprParamsT := ⟨T, LMonoTy⟩

/-- Whether a quantifier is universal or existential. -/
inductive QuantifierKind
  | all
  | exist
  deriving Repr, DecidableEq

/-- Lambda constants. -/
inductive LConst : Type where
  /-- An unbounded integer constant. -/
  | intConst (i : Int)
  /-- A string constant. -/
  | strConst (s : String)
  /-- A real constant, represented as a rational number. -/
  | realConst (r : Rat)
  /-- A bit vector constant. -/
  | bitvecConst (n : Nat) (b : BitVec n)
  /-- A Boolean constant. -/
  | boolConst (b : Bool)
  deriving Repr, DecidableEq, Hashable

/-- The type of a constant `c`. -/
@[expose] def LConst.ty (c : LConst) : LMonoTy :=
  match c with
  | .intConst _ => .int
  | .strConst _ => .string
  | .bitvecConst n _ => .bitvec n
  | .realConst _ => .real
  | .boolConst _ => .bool

/-- Lambda expressions with quantifiers, in locally-nameless form.
(`Strata/DL/Lambda/LExpr.lean`) -/
inductive LExpr (T : LExprParamsT) : Type where
  /-- A constant (a literal). -/
  | const   (m : T.base.Metadata) (c : LConst)
  /-- A built-in operation, referred to by name. -/
  | op      (m : T.base.Metadata) (o : Identifier T.base.IDMeta) (ty : Option T.TypeType)
  /-- A bound variable, in de Bruijn form. -/
  | bvar    (m : T.base.Metadata) (deBruijnIndex : Nat)
  /-- A free variable, with an optional type annotation. -/
  | fvar    (m : T.base.Metadata) (name : Identifier T.base.IDMeta) (ty : Option T.TypeType)
  /-- An abstraction. -/
  | abs     (m : T.base.Metadata) (prettyName : String) (ty : Option T.TypeType) (e : LExpr T)
  /-- A quantified expression. -/
  | quant   (m : T.base.Metadata) (k : QuantifierKind) (prettyName : String) (ty : Option T.TypeType)
              (trigger : LExpr T) (e : LExpr T)
  /-- A function application. -/
  | app     (m : T.base.Metadata) (fn e : LExpr T)
  /-- A conditional expression. -/
  | ite     (m : T.base.Metadata) (c t e : LExpr T)
  /-- An equality expression. -/
  | eq      (m : T.base.Metadata) (e1 e2 : LExpr T)

/-! ## `Denote/LExprAnnotated.lean` — type checking for annotated exprs -/

/-- Typecheck an annotated `LExpr`, returning `some τ` if well-typed, `none`
otherwise. `ctx` maps de Bruijn indices to their types from enclosing binders.
(`Strata/DL/Lambda/Denote/LExprAnnotated.lean`) -/
@[expose]
def LExpr.typeCheck {T : LExprParams} (ctx : List LMonoTy) : LExpr T.mono → Option LMonoTy
  | .const _ c => some c.ty
  | .op _ _ (some ty) => some ty
  | .op _ _ none => none
  | .fvar _ _ (some ty) => some ty
  | .fvar _ _ none => none
  | .bvar _ i => ctx[i]?
  | .abs _ _ (some aty) body => do
    let rty ← typeCheck (aty :: ctx) body
    some (.arrow aty rty)
  | .abs _ _ none _ => none
  | .quant _ _ _ (some qty) tr body => do
    let _ ← typeCheck (qty :: ctx) tr
    let bty ← typeCheck (qty :: ctx) body
    guard (bty == .bool)
    some .bool
  | .quant _ _ _ none _ _ => none
  | .app _ fn arg => do
    let fty ← typeCheck ctx fn
    let aty ← typeCheck ctx arg
    let (dom, cod) ← fty.isArrow
    guard (dom == aty)
    some cod
  | .ite _ c t e => do
    let cty ← typeCheck ctx c
    let tty ← typeCheck ctx t
    let ety ← typeCheck ctx e
    guard (cty == .bool)
    guard (tty == ety)
    some tty
  | .eq _ e1 e2 => do
    let ty1 ← typeCheck ctx e1
    let ty2 ← typeCheck ctx e2
    guard (ty1 == ty2)
    some .bool

/-- Declarative typing rules for annotated expressions.

The first argument (`List LMonoTy`) is the typing context for bound variables,
ordered by de Bruijn indices: the head is the type of the most recently bound
variable (index 0), and so on. (`Strata/DL/Lambda/Denote/LExprAnnotated.lean`) -/
inductive LExpr.HasTypeA {T : LExprParams} : List LMonoTy → LExpr T.mono → LMonoTy → Prop where
  | const : HasTypeA Δ (.const m c) c.ty
  | op    : HasTypeA Δ (.op m o (some ty)) ty
  | fvar  : HasTypeA Δ (.fvar m x (some ty)) ty
  | bvar  : Δ[i]? = some t → HasTypeA Δ (.bvar m i) t
  | abs   : HasTypeA (aty :: Δ) body rty →
            HasTypeA Δ (.abs m name (some aty) body) (.arrow aty rty)
  | quant : HasTypeA (qty :: Δ) tr τ_tr →
            HasTypeA (qty :: Δ) body .bool →
            HasTypeA Δ (.quant m k name (some qty) tr body) .bool
  | app   : HasTypeA Δ fn (.arrow aty rty) →
            HasTypeA Δ arg aty →
            HasTypeA Δ (.app m fn arg) rty
  | ite   : HasTypeA Δ c .bool →
            HasTypeA Δ t τ →
            HasTypeA Δ e τ →
            HasTypeA Δ (.ite m c t e) τ
  | eq    : HasTypeA Δ e1 τ →
            HasTypeA Δ e2 τ →
            HasTypeA Δ (.eq m e1 e2) .bool

end Lambda
