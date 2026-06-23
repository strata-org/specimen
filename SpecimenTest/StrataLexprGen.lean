import SpecimenTest.StrataDefs.LambdaCore
import Plausible.Gen
import Specimen.DecOpt
import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary
import Specimen.DeriveEnum

/-! # Deriving a Specimen generator for well-typed Strata `LExpr`s

Goal: produce a Specimen constrained generator for Strata `LExpr` values that
satisfy the `LExpr.HasTypeA` annotated-typing relation (for a given
bound-variable context `Δ` and result type `τ`). The faithful `LExpr`,
`LMonoTy`, etc. are vendored in `SpecimenTest/StrataDefs/LambdaCore.lean`.

This file demonstrates that, with two Specimen changes in place — (1) the
classifier tolerating function-application premises such as the `bvar` rule's
`Δ[i]? = some t` de-Bruijn lookup, and (2) the delegated-producer path that
routes such an equality premise to a user-supplied `ArbitrarySizedSuchThat`
instance — the full annotated-typing relation derives a *good* generator, given
one hand-written instance for the lookup.

## On the expression parameters

The real `LExpr` is parameterized by a *structure* `T : LExprParamsT` (the
metadata/identifier/type-annotation types), and that `Type 1` parameter rides
along as an argument of every constructor (`@LExpr.const T.mono m c`). The
constrained deriver does not yet handle such a structure parameter — it tries to
*generate* it — which is a separate, orthogonal limitation independent of the
two changes exercised here.

To keep this example focused on the typing relation, we use `LExprU`: the
*verbatim* shape of `LExpr` with that parameter inlined at its trivial,
fully-monomorphic instantiation (`Unit` expression metadata, `Unit` identifier
metadata, `LMonoTy` type annotations). I.e. `LExprU ≃ LExpr ⟨⟨Unit, Unit⟩, LMonoTy⟩`,
with the parameter erased so no `Type 1` argument appears in the constructors.
Likewise `HasTypeAU` is `LExpr.HasTypeA` transcribed verbatim over `LExprU`. -/

open Plausible
open ArbitrarySizedSuchThat
open Lambda

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

/-- Identifiers at `Unit` metadata (as in `LExpr` specialized to `⟨Unit, Unit⟩`). -/
abbrev IdentU := Identifier Unit

/-- The shape of Strata's `LExpr` with the `LExprParamsT` parameter inlined at
    `⟨⟨Unit, Unit⟩, LMonoTy⟩`: expression metadata is `Unit`, identifier metadata
    is `Unit`, and user type annotations are `LMonoTy`. A verbatim transcription
    of `Lambda.LExpr` (see `LambdaCore.lean`). -/
inductive LExprU : Type where
  | const   (m : Unit) (c : LConst)
  | op      (m : Unit) (o : IdentU) (ty : Option LMonoTy)
  | bvar    (m : Unit) (deBruijnIndex : Nat)
  | fvar    (m : Unit) (name : IdentU) (ty : Option LMonoTy)
  | abs     (m : Unit) (prettyName : String) (ty : Option LMonoTy) (e : LExprU)
  | quant   (m : Unit) (k : QuantifierKind) (prettyName : String) (ty : Option LMonoTy)
              (trigger : LExprU) (e : LExprU)
  | app     (m : Unit) (fn e : LExprU)
  | ite     (m : Unit) (c t e : LExprU)
  | eq      (m : Unit) (e1 e2 : LExprU)
  deriving Repr

/-! ## Unconstrained producers for the value types carried by `LExprU` -/

/-- `Rat` is carried by `LConst.realConst`; Plausible ships no `Arbitrary Rat`. -/
instance : Arbitrary Rat where
  arbitrary := do return (Rat.ofInt (← Arbitrary.arbitrary))

deriving instance Arbitrary for QuantifierKind
deriving instance Arbitrary for LConst
deriving instance Arbitrary for Identifier

/-- A *shallow*, terminating `Arbitrary LMonoTy`. The auto-derived generator for
    `LMonoTy` is unbounded (its `tcons` carries `List LMonoTy`, so it can recurse
    without limit and overflow the stack); since the constrained generator only
    needs occasional fresh types (e.g. the `app` argument type, binder
    annotations), a small fixed selection of base and first-order arrow types is
    both sufficient and well-behaved. -/
instance : Arbitrary LMonoTy where
  arbitrary := do
    let choices : List LMonoTy :=
      [.int, .bool, .string,
       .arrow .int .bool, .arrow .bool .bool, .arrow .int .int]
    let n ← Plausible.Gen.chooseNatLt 0 choices.length (by decide)
    return choices[n.val]!

deriving instance Arbitrary for LExprU

/-! ## The hand-written delegated producer for the de-Bruijn lookup

The `bvar` rule's premise is `Δ[i]? = some t` — list indexing, which the deriver
cannot invert to *produce* the index `i`. We supply a constrained producer for
exactly that equality; change (2) detects it and delegates production of `i` to
it (rather than generating `i` blindly and filtering, which has a poor hit rate).

It enumerates the indices `i` of `Δ` whose entry is `t` and picks one at random,
so it produces *well-typed, in-scope* de-Bruijn variables directly. -/
instance lookupProducer (Δ : List LMonoTy) (t : LMonoTy) :
    ArbitrarySizedSuchThat Nat (fun i => Δ[i]? = some t) where
  arbitrarySizedST _ := do
    let candidates := (List.range Δ.length).filter (fun i => Δ[i]? = some t)
    match candidates with
    -- No in-scope variable has type `t`: fail so the caller backtracks to another
    -- rule. Returning an arbitrary index here would fabricate an ill-typed `bvar`.
    | [] => throw Plausible.Gen.genericFailure
    | c :: cs =>
      let n ← Plausible.Gen.chooseNatLt 0 (c :: cs).length (by simp)
      return (c :: cs)[n.val]!

/-- The companion lookup producer for the *synthesis* direction, used when
    `derive_mutual` also derives "given a term, find its type": pick an index `i`
    into `Δ` and return both `i` and the entry `Δ[i]?` it points at. Producing
    both at once satisfies `Δ[i]? = vt`. -/
instance lookupProducerSyn (Δ : List LMonoTy) :
    ArbitrarySizedSuchThat (Nat × Option LMonoTy) (fun p => Δ[p.1]? = p.2) where
  arbitrarySizedST _ := do
    if h : 0 < Δ.length then
      let n ← Plausible.Gen.chooseNatLt 0 Δ.length h
      return (n.val, Δ[n.val]?)
    else
      return (0, none)

/-! ## The typing relation, transcribed verbatim from `LExpr.HasTypeA` -/
inductive HasTypeAU : List LMonoTy → LExprU → LMonoTy → Prop where
  | const : HasTypeAU Δ (.const m c) c.ty
  | op    : HasTypeAU Δ (.op m o (some ty)) ty
  | fvar  : HasTypeAU Δ (.fvar m x (some ty)) ty
  | bvar  : Δ[i]? = some t → HasTypeAU Δ (.bvar m i) t
  | abs   : HasTypeAU (aty :: Δ) body rty →
            HasTypeAU Δ (.abs m name (some aty) body) (.arrow aty rty)
  | quant : HasTypeAU (qty :: Δ) tr τ_tr →
            HasTypeAU (qty :: Δ) body .bool →
            HasTypeAU Δ (.quant m k name (some qty) tr body) .bool
  | app   : HasTypeAU Δ fn (.arrow aty rty) →
            HasTypeAU Δ arg aty →
            HasTypeAU Δ (.app m fn arg) rty
  | ite   : HasTypeAU Δ c .bool →
            HasTypeAU Δ t τ →
            HasTypeAU Δ e τ →
            HasTypeAU Δ (.ite m c t e) τ
  | eq    : HasTypeAU Δ e1 τ →
            HasTypeAU Δ e2 τ →
            HasTypeAU Δ (.eq m e1 e2) .bool

/- Derive a constrained generator that, given a context `Δ` and a type `τ`,
   produces a well-typed `LExprU` of type `τ`.

   With the two Specimen changes and the hand-written `lookupProducer` instance,
   this succeeds — the `bvar` rule's lookup premise is delegated to
   `lookupProducer`. We use `derive_mutual` so the recursive rules
   (`app`/`eq`/`abs`/`quant`), which must generate a subterm together with its
   type, get the needed `ArbitrarySizedSuchThat (LExprU × LMonoTy)` companion
   producer — exactly as in `DeriveArbitrarySuchThat/DeriveSTLCGenerator.lean`.

   (`derive_mutual` also explores synthesis-direction companions; the one for the
   `eq` rule has a fixed `bool` conclusion with nothing to synthesize, yielding a
   harmless "no output types" warning that we drop.) -/
#guard_msgs(drop info, drop warning) in
derive_mutual (fun Δ τ => ∃ e : LExprU, HasTypeAU Δ e τ)

/-! ## Pretty-printing -/

/-- Pretty-prints a monomorphic type. -/
def ppMonoTy : LMonoTy → String
  | .int => "int"
  | .bool => "bool"
  | .string => "string"
  | .real => "real"
  | .bitvec n => s!"bv<{n}>"
  | .arrow t1 t2 => s!"({ppMonoTy t1} → {ppMonoTy t2})"
  | .ftvar name => name
  | .tcons name _ => name

/-- Pretty-print an `LExprU` with minimal parenthesization. -/
def ppLExprU (e : LExprU) (prec : Nat := 0) : String :=
  let wrap (p : Nat) (s : String) := if prec ≥ p then s!"({s})" else s
  match e with
  | .const _ (.boolConst b) => s!"#{b}"
  | .const _ (.intConst i) => s!"#{i}"
  | .const _ (.strConst s) => s!"\"{s}\""
  | .const _ (.realConst r) => s!"#{r}"
  | .const _ (.bitvecConst _ b) => s!"#{b.toNat}"
  | .op _ o _ => s!"{o.name}"
  | .bvar _ i => s!"%{i}"
  | .fvar _ x ty => match ty with
    | some t => s!"{x.name} : {ppMonoTy t}"
    | none => s!"{x.name}"
  | .abs _ _ ty body => wrap 1 <| match ty with
    | some t => s!"λ{ppMonoTy t}. {ppLExprU body 0}"
    | none => s!"λ_. {ppLExprU body 0}"
  | .quant _ .all _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∀{ppMonoTy t}. {ppLExprU body 0}"
    | none => s!"∀_. {ppLExprU body 0}"
  | .quant _ .exist _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∃{ppMonoTy t}. {ppLExprU body 0}"
    | none => s!"∃_. {ppLExprU body 0}"
  | .app _ fn arg => wrap 3 <| s!"{ppLExprU fn 2} {ppLExprU arg 3}"
  | .ite _ c t e => wrap 1 <| s!"if {ppLExprU c 0} then {ppLExprU t 0} else {ppLExprU e 0}"
  | .eq _ e₁ e₂ => wrap 2 <| s!"{ppLExprU e₁ 2} == {ppLExprU e₂ 2}"

/-! ## Soundness check: sampled terms really are well-typed

A computable type-checker for `LExprU` (mirroring Strata's `LExpr.typeCheck`),
used to confirm that the derived generator produces *only* well-typed terms. -/

/-- Computable type-checker for `LExprU`; returns the type if well-typed. -/
def typeCheckU (ctx : List LMonoTy) : LExprU → Option LMonoTy
  | .const _ c => some c.ty
  | .op _ _ (some ty) => some ty
  | .op _ _ none => none
  | .fvar _ _ (some ty) => some ty
  | .fvar _ _ none => none
  | .bvar _ i => ctx[i]?
  | .abs _ _ (some aty) body => (typeCheckU (aty :: ctx) body).map (.arrow aty ·)
  | .abs _ _ none _ => none
  | .quant _ _ _ (some qty) tr body =>
      match typeCheckU (qty :: ctx) tr, typeCheckU (qty :: ctx) body with
      | some _, some (.tcons "bool" []) => some .bool
      | _, _ => none
  | .quant _ _ _ none _ _ => none
  | .app _ fn arg =>
      match typeCheckU ctx fn, typeCheckU ctx arg with
      | some (.tcons "arrow" [dom, cod]), some aty => if dom = aty then some cod else none
      | _, _ => none
  | .ite _ c t e =>
      match typeCheckU ctx c, typeCheckU ctx t, typeCheckU ctx e with
      | some (.tcons "bool" []), some tt, some et => if tt = et then some tt else none
      | _, _, _ => none
  | .eq _ a b =>
      match typeCheckU ctx a, typeCheckU ctx b with
      | some ta, some tb => if ta = tb then some .bool else none
      | _, _ => none

/- Sample the derived generator across several `(context, type)` requests and
   assert every produced term type-checks at the requested type. Throws (failing
   the build) on any ill-typed sample, so this doubles as a soundness test. -/
#guard_msgs(drop info) in
#eval show IO Unit from do
  let trials : List (List LMonoTy × LMonoTy) :=
    [([.int, .bool], .bool), ([.int], .int), ([],  .bool),
     ([.bool, .int, .string], .string), ([.arrow .int .bool, .int], .bool)]
  for (ctx, τ) in trials do
    let ctxStr := String.intercalate ", " (ctx.map ppMonoTy)
    IO.println s!"--- [{ctxStr}] ⊢ _ : {ppMonoTy τ} ---"
    for s in List.range 12 do
      let e ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun e => HasTypeAU ctx e τ) 4) (s * 7 + 1)
      IO.println s!"  {ppLExprU e}"
      unless typeCheckU ctx e == some τ do
        throw (IO.userError
          s!"ill-typed sample for {repr ctx} ⊢ _ : {ppMonoTy τ}: {ppLExprU e} : {repr (typeCheckU ctx e)}")
