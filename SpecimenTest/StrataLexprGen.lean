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

This exercises three Specimen capabilities working together on the *real*,
fully-parameterized relation:

1. The schedule classifier tolerates function-application premises such as the
   `bvar` rule's `Δ[i]? = some t` de-Bruijn lookup.
2. The delegated-producer path routes that equality premise to a user-supplied
   `ArbitrarySizedSuchThat` instance for the lookup.
3. The constrained deriver handles `LExpr`'s `LExprParamsT` *structure
   parameter*: it does not try to generate the parameter itself, and it emits
   the per-field `[Arbitrary T.base.Metadata]` …-style instance binders needed
   to generate the metadata fields carried by each constructor (mirroring the
   unconstrained `deriving Arbitrary` path's `expandStructBinders`).

Note the relation below is the genuine `@LExpr.HasTypeA T …` with `T` an
abstract `LExprParams` — no monomorphization. -/

open Plausible
open ArbitrarySizedSuchThat
open Lambda

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

/-! ## Unconstrained producers for the value types carried by `LExpr` -/

/-- `Rat` is carried by `LConst.realConst`; Plausible ships no `Arbitrary Rat`. -/
instance : Arbitrary Rat where
  arbitrary := do return (Rat.ofInt (← Arbitrary.arbitrary))

/-- A *shallow*, terminating `Arbitrary LMonoTy`. The auto-derived generator for
    `LMonoTy` is unbounded (its `tcons` carries `List LMonoTy`, so it can recurse
    without limit and overflow the stack); a small fixed selection of base and
    first-order arrow types is sufficient for the occasional fresh types the
    constrained generator needs (e.g. the `app` argument type). -/
instance : Arbitrary LMonoTy where
  arbitrary := do
    let choices : List LMonoTy :=
      [.int, .bool, .string, .arrow .int .bool, .arrow .bool .bool, .arrow .int .int]
    let n ← Plausible.Gen.chooseNatLt 0 choices.length (by decide)
    return choices[n.val]!

deriving instance Arbitrary for QuantifierKind
deriving instance Arbitrary for LConst
deriving instance Arbitrary for Identifier
-- The output ADT, via Specimen's structure-parameter-aware `Arbitrary` override.
deriving instance Arbitrary for LExpr

/-! ## The hand-written delegated producers for the de-Bruijn lookup

The `bvar` rule's premise is `Δ[i]? = some t` — list indexing, which the deriver
cannot invert to *produce* the index `i`. We supply constrained producers for
that equality; the delegated-producer machinery detects them and delegates
production of the lookup to them (rather than generating `i` blindly and
filtering, which has a poor hit rate).

The first instance produces an index of the requested type; the second is the
synthesis-direction companion (`derive_mutual` derives both directions), which
produces an index *and* the type it points at. Both fail when no in-scope
variable matches, so they never fabricate ill-typed `bvar`s. -/
instance lookupProducer (Δ : List LMonoTy) (t : LMonoTy) :
    ArbitrarySizedSuchThat Nat (fun i => Δ[i]? = some t) where
  arbitrarySizedST _ := do
    match (List.range Δ.length).filter (fun i => Δ[i]? = some t) with
    | [] => throw Plausible.Gen.genericFailure
    | c :: cs =>
      let n ← Plausible.Gen.chooseNatLt 0 (c :: cs).length (by simp)
      return (c :: cs)[n.val]!

instance lookupProducerSyn (Δ : List LMonoTy) :
    ArbitrarySizedSuchThat (Nat × Option LMonoTy) (fun p => Δ[p.1]? = p.2) where
  arbitrarySizedST _ := do
    if h : 0 < Δ.length then
      let n ← Plausible.Gen.chooseNatLt 0 Δ.length h
      return (n.val, Δ[n.val]?)
    else
      return (0, none)

/- Derive a constrained generator for well-typed `LExpr T.mono`, for an abstract
   structure parameter `T`. With the structure-parameter handling in place, the
   constructors' metadata fields (`m : T.base.Metadata`, identifiers, …) are
   generated via the auto-emitted per-field `Arbitrary` instance binders, and the
   `bvar` lookup is delegated to `lookupProducer`. `derive_mutual` also explores a
   synthesis companion whose `eq`-rule has a fixed `bool` conclusion (nothing to
   synthesize), producing a harmless "no output types" warning that we drop. -/
#guard_msgs(drop info, drop warning) in
derive_mutual (fun (T : LExprParams) (Δ : List LMonoTy) (τ : LMonoTy) =>
  ∃ e : LExpr T.mono, @LExpr.HasTypeA T Δ e τ)

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

/-! ## Soundness check: sampled terms really are well-typed

We instantiate the derived generator at the concrete, monomorphic parameters
`P := ⟨Unit, Unit⟩` and type-check sampled terms with a computable checker
mirroring Strata's `LExpr.typeCheck`. -/

/-- Concrete, monomorphic expression parameters for sampling. -/
abbrev P : LExprParams := ⟨Unit, Unit⟩

/-- Computable type-checker for `LExpr P.mono`; returns the type if well-typed. -/
def typeCheckP (ctx : List LMonoTy) : LExpr P.mono → Option LMonoTy
  | .const _ c => some c.ty
  | .op _ _ (some ty) => some ty
  | .op _ _ none => none
  | .fvar _ _ (some ty) => some ty
  | .fvar _ _ none => none
  | .bvar _ i => ctx[i]?
  | .abs _ _ (some aty) body => (typeCheckP (aty :: ctx) body).map (.arrow aty ·)
  | .abs _ _ none _ => none
  | .quant _ _ _ (some qty) tr body =>
      match typeCheckP (qty :: ctx) tr, typeCheckP (qty :: ctx) body with
      | some _, some (.tcons "bool" []) => some .bool
      | _, _ => none
  | .quant _ _ _ none _ _ => none
  | .app _ fn arg =>
      match typeCheckP ctx fn, typeCheckP ctx arg with
      | some (.tcons "arrow" [dom, cod]), some aty => if dom = aty then some cod else none
      | _, _ => none
  | .ite _ c t e =>
      match typeCheckP ctx c, typeCheckP ctx t, typeCheckP ctx e with
      | some (.tcons "bool" []), some tt, some et => if tt = et then some tt else none
      | _, _, _ => none
  | .eq _ a b =>
      match typeCheckP ctx a, typeCheckP ctx b with
      | some ta, some tb => if ta = tb then some .bool else none
      | _, _ => none

/-- Pretty-print an `LExpr P.mono` with minimal parenthesization. -/
def ppLExprP (e : LExpr P.mono) (prec : Nat := 0) : String :=
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
    | some t => s!"λ{ppMonoTy t}. {ppLExprP body 0}"
    | none => s!"λ_. {ppLExprP body 0}"
  | .quant _ .all _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∀{ppMonoTy t}. {ppLExprP body 0}"
    | none => s!"∀_. {ppLExprP body 0}"
  | .quant _ .exist _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∃{ppMonoTy t}. {ppLExprP body 0}"
    | none => s!"∃_. {ppLExprP body 0}"
  | .app _ fn arg => wrap 3 <| s!"{ppLExprP fn 2} {ppLExprP arg 3}"
  | .ite _ c t e => wrap 1 <| s!"if {ppLExprP c 0} then {ppLExprP t 0} else {ppLExprP e 0}"
  | .eq _ e₁ e₂ => wrap 2 <| s!"{ppLExprP e₁ 2} == {ppLExprP e₂ 2}"

/- Sample the derived generator (at `T := P`) across several `(context, type)`
   requests and assert every produced term type-checks at the requested type.
   Throws (failing the build) on any ill-typed sample. -/
#guard_msgs(drop info) in
#eval show IO Unit from do
  let trials : List (List LMonoTy × LMonoTy) :=
    [([.int, .bool], .bool), ([.int], .int), ([], .bool),
     ([.bool, .int, .string], .string), ([.arrow .int .bool, .int], .bool)]
  for (ctx, τ) in trials do
    let ctxStr := String.intercalate ", " (ctx.map ppMonoTy)
    IO.println s!"--- [{ctxStr}] ⊢ _ : {ppMonoTy τ} ---"
    for s in List.range 12 do
      let e ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun e => @LExpr.HasTypeA P ctx e τ) 4) (s * 7 + 1)
      IO.println s!"  {ppLExprP e}"
      unless typeCheckP ctx e == some τ do
        throw (IO.userError
          s!"ill-typed sample for {repr ctx} ⊢ _ : {ppMonoTy τ}: {ppLExprP e} : {repr (typeCheckP ctx e)}")
