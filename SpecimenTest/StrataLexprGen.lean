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
`LMonoTy`, `HasTypeA`, and the soundness oracle `LExpr.typeCheck` are vendored
verbatim in `SpecimenTest/StrataDefs/LambdaCore.lean`.

This file derives over the **genuine, structure-parameterized** relation — no
monomorphization. It exercises three Specimen capabilities together:

1. the classifier tolerating a function-application premise (the `bvar` rule's
   `Δ[i]? = some t` de-Bruijn lookup);
2. the **delegated-producer** path routing that equality to the hand-written
   `lookupProducer` below (and a synthesis-direction companion);
3. the **structure-parameter** handling: `LExpr` is parameterized by a
   *structure* `T : LExprParamsT` (metadata / identifier / type-annotation
   configuration types), and that `Type 1` parameter rides along as an implicit
   argument of every constructor (`@LExpr.const T.mono m c`). The constrained
   deriver keeps that fixed parameter in place rather than trying to generate
   it, and emits the per-field `[Arbitrary …]` binders the constructors need.

We derive with `T : LExprParams` kept abstract; the derived instances are
universally quantified over `T` with the structure-field binders synthesized by
the deriver. The soundness `#eval` then instantiates `T := ⟨Unit, Unit⟩` and
type-checks every sampled term with the vendored `LExpr.typeCheck` oracle. -/

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

-- The output ADT itself, via Specimen's structure-param-aware `Arbitrary`
-- deriving override (`Specimen.DeriveArbitrary`).
deriving instance Arbitrary for LExpr

/-! ## The hand-written delegated producer for the de-Bruijn lookup

The `bvar` rule's premise is `Δ[i]? = some t` — list indexing, which the deriver
cannot invert to *produce* the index `i`. We supply a constrained producer for
exactly that equality; the delegated-producer path detects it and delegates
production of `i` to it (rather than generating `i` blindly and filtering, which
has a poor hit rate).

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

/- Derive a constrained generator that, given a context `Δ` and a type `τ`,
   produces a well-typed `LExpr T.mono` of type `τ`, for abstract `T`.

   With the structure-parameter handling, the getElem?-premise classification,
   and the hand-written `lookupProducer` instance, this succeeds — the `bvar`
   rule's lookup premise is delegated to `lookupProducer`. We use `derive_mutual`
   so the recursive rules (`app`/`eq`/`abs`/`quant`), which must generate a
   subterm together with its type, get the needed
   `ArbitrarySizedSuchThat (LExpr T.mono × LMonoTy)` companion producer — exactly
   as in `DeriveArbitrarySuchThat/DeriveSTLCGenerator.lean`.

   (`derive_mutual` also explores synthesis-direction companions; the one for the
   `eq` rule has a fixed `bool` conclusion with nothing to synthesize, yielding a
   harmless "no output types" warning that we drop.) -/
#guard_msgs(drop info, drop warning) in
derive_mutual (fun (T : LExprParams) (Δ : List LMonoTy) (τ : LMonoTy) =>
  ∃ e : LExpr T.mono, @LExpr.HasTypeA T Δ e τ)

/-! ## Soundness check: sampled terms really are well-typed

Instantiate the abstract parameter at the trivial monomorphic point
(`Unit` expression metadata, `Unit` identifier metadata), sample the derived
generator across several `(context, type)` requests, and assert every produced
term type-checks at the requested type with the vendored `LExpr.typeCheck`
oracle. Throws (failing the build) on any ill-typed sample. -/

/-- The trivial monomorphic parameter: `Unit` metadata, `Unit` id-metadata. -/
abbrev P0 : LExprParams := ⟨Unit, Unit⟩

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

/-- Pretty-print an `LExpr P0.mono` with minimal parenthesization. -/
def ppLExpr (e : LExpr P0.mono) (prec : Nat := 0) : String :=
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
    | some t => s!"λ{ppMonoTy t}. {ppLExpr body 0}"
    | none => s!"λ_. {ppLExpr body 0}"
  | .quant _ .all _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∀{ppMonoTy t}. {ppLExpr body 0}"
    | none => s!"∀_. {ppLExpr body 0}"
  | .quant _ .exist _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∃{ppMonoTy t}. {ppLExpr body 0}"
    | none => s!"∃_. {ppLExpr body 0}"
  | .app _ fn arg => wrap 3 <| s!"{ppLExpr fn 2} {ppLExpr arg 3}"
  | .ite _ c t e => wrap 1 <| s!"if {ppLExpr c 0} then {ppLExpr t 0} else {ppLExpr e 0}"
  | .eq _ e₁ e₂ => wrap 2 <| s!"{ppLExpr e₁ 2} == {ppLExpr e₂ 2}"

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
        (fun e => @LExpr.HasTypeA P0 ctx e τ) 4) (s * 7 + 1)
      IO.println s!"  {ppLExpr e}"
      unless LExpr.typeCheck ctx e == some τ do
        throw (IO.userError
          s!"ill-typed sample for {repr ctx} ⊢ _ : {ppMonoTy τ}: {ppLExpr e} : {repr (LExpr.typeCheck ctx e)}")
