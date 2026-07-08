import Plausible.Gen
import Plausible.Arbitrary
import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary
import Specimen.DeriveEnum

/-! # Deriving producers for a *structure-parameterized* STLC

A small, self-contained regression witness for Specimen's support of inductive
relations whose output type is parameterized by a **structure** (rather than a
plain `Sort`/type parameter). The full-scale motivating case is Strata's
`LExpr T` / `LExpr.HasTypeA`; this reproduces the shape in miniature.

The two ingredients Strata relies on, distilled:

* A **structure parameter** `P : ExprParams` bundles the configuration types for
  the expression language. Here it has **two** fields, one of which is **itself a
  structure** — so the constructor fields are reached by projection chains like
  `P.info.Metadata` (nested) and `P.VarId` (direct). Exercising both is what
  checks the *recursive* field expansion in `expandStructInstBinders`.
* The typing relation `HasType` is stated over the genuine abstract `Tm P` (**no
  monomorphization**), so those projections ride along as implicit arguments of
  every constructor in the conclusion.

Deriving for this shape needs all three coordinated deriver changes: don't lift
the fixed, ungeneratable parameter projections; emit `[Arbitrary P.info.Metadata]`
/ `[Arbitrary P.VarId]` field binders (recursively); and drop the implicit
parameter from constructor outputs so Lean re-infers it.

The witness is simply that `derive_mutual` **elaborates** producers for this
relation. We ask it for both producer sorts at once — a generator and an
enumerator — so the struct-param field binders are exercised on both emission
paths (`[Arbitrary P.info.Metadata]` for the generator, the `[Enum …]`
counterparts for the enumerator). Tiny `#eval`s then draw from each derived
producer to confirm they actually run. -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

namespace StructParamSTLC

/-- Object-language types: naturals and functions. -/
inductive Ty where
  | nat : Ty
  | arrow : Ty → Ty → Ty
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A nested single-field structure, used as one field of `ExprParams`. Reaching
    its field from the parameter requires a **two-step** projection chain
    (`P.info.Metadata`), which is what checks the recursion in the field walk. -/
structure NodeInfo : Type 1 where
  /-- The type of metadata carried by each expression node. -/
  Metadata : Type
  deriving Inhabited

/-- The **structure parameter** bundling the language's configuration types. Two
    fields: a *nested structure* `info` (so metadata is `P.info.Metadata`) and a
    *direct* type field `VarId` (so variable labels are `P.VarId`). Lives in
    `Type 1` because it quantifies over `Type`. -/
structure ExprParams : Type 1 where
  /-- Per-node metadata configuration (itself a structure). -/
  info : NodeInfo
  /-- The type of the opaque label attached to variable occurrences. -/
  VarId : Type
  deriving Inhabited

/-- Expressions, parameterized by the structure `P`. Every constructor carries a
    metadata field `(m : P.info.Metadata)` — a *nested* projection — and `var`
    additionally carries a `(name : P.VarId)` — a *direct* projection — so both
    fields of the parameter appear in generated values. -/
inductive Tm (P : ExprParams) : Type where
  /-- A numeric literal. -/
  | lit (m : P.info.Metadata) (n : Nat)
  /-- A de-Bruijn–indexed bound variable, tagged with an opaque `name`. -/
  | var (m : P.info.Metadata) (name : P.VarId) (idx : Nat)
  /-- Addition of two naturals. -/
  | add (m : P.info.Metadata) (e1 e2 : Tm P)
  /-- A lambda abstraction annotated with its argument type. -/
  | lam (m : P.info.Metadata) (dom : Ty) (body : Tm P)
  /-- A function application. -/
  | app (m : P.info.Metadata) (fn arg : Tm P)

/-- Context lookup as an *invertible* inductive relation (de-Bruijn indexing).
    Keeping this a relation rather than `Γ[i]? = some τ` lets the deriver invert
    it to produce in-scope variables directly, so this example needs no
    hand-written delegated producer. -/
inductive Lookup : List Ty → Nat → Ty → Prop where
  | here  : Lookup (τ :: Γ) 0 τ
  | there : Lookup Γ n τ → Lookup (τ' :: Γ) (n + 1) τ

/-- The typing relation over the genuine abstract `Tm P` (no monomorphization).
    `Γ` is the de-Bruijn context (head = most recently bound variable). -/
inductive HasType {P : ExprParams} : List Ty → Tm P → Ty → Prop where
  | lit  : HasType Γ (.lit m n) .nat
  | var  : Lookup Γ i τ → HasType Γ (.var m x i) τ
  | add  : HasType Γ e1 .nat →
           HasType Γ e2 .nat →
           HasType Γ (.add m e1 e2) .nat
  | lam  : HasType (dom :: Γ) body cod →
           HasType Γ (.lam m dom body) (.arrow dom cod)
  | app  : HasType Γ fn (.arrow dom cod) →
           HasType Γ arg dom →
           HasType Γ (.app m fn arg) cod

/-- Shallow, terminating unconstrained producers for `Ty` (the `lam` binder
    annotation). Auto-derived ones could recurse without bound through `arrow`;
    a small fixed selection is enough for the constrained producers. -/
instance : Arbitrary Ty where
  arbitrary := do
    let choices : List Ty := [.nat, .arrow .nat .nat, .arrow .nat (.arrow .nat .nat)]
    let n ← Plausible.Gen.chooseNatLt 0 choices.length (by decide)
    return choices[n.val]!

instance : Enum Ty where
  enum := EnumeratorCombinators.oneOfWithDefault
    (pure .nat) (pure <$> [Ty.nat, .arrow .nat .nat, .arrow .nat (.arrow .nat .nat)])

/-! ## Deriving a generator and an enumerator together (abstract `P`)

One `derive_mutual` asks for both producer sorts from the same relation. Each
derived instance is universally quantified over `P` with the field binders
synthesized by walking the structure — `[Arbitrary P.info.Metadata]
[Arbitrary P.VarId]` for the generator, and the `[Enum …]` counterparts for the
enumerator. That this elaborates at all is the core regression witness. -/
#guard_msgs(drop info, drop warning) in
derive_mutual
  generator  (fun (P : ExprParams) (Γ : List Ty) (τ : Ty) => ∃ e : Tm P, @HasType P Γ e τ),
  enumerator (fun (P : ExprParams) (Γ : List Ty) (τ : Ty) => ∃ e : Tm P, @HasType P Γ e τ)

/-! ## The derived producers actually run

Monomorphize the parameter (both fields to `Unit`) and draw from each derived
producer, confirming they run and yield at least one term. -/
abbrev P0 : ExprParams := ⟨⟨Unit⟩, Unit⟩

#guard_msgs(drop info) in
#eval show IO Unit from do
  let mut n := 0
  for (Γ, τ) in [([], Ty.nat), ([.nat], .nat), ([], .arrow .nat .nat)] do
    for s in List.range 6 do
      let _ ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun e => @HasType P0 Γ e τ) 4) (s * 7 + 1)
      n := n + 1
  IO.println s!"derived generator produced {n} well-typed terms"

#guard_msgs(drop info) in
#eval do
  let results ← runSizedEnum
    (EnumSizedSuchThat.enumSizedST (fun e => @HasType P0 [] e .nat)) 3
  IO.println s!"derived enumerator produced {results.length} results at [] ⊢ _ : nat"

end StructParamSTLC
