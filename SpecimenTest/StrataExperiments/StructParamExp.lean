import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: structure-valued implicit type parameters, modelled on Strata's
    `HasType {T : LExprParams} [DecidableEq T.IDMeta] (C : LContext T) : ...`,
    whose generated term has type `LExpr T.mono` — a PROJECTION of the
    structure parameter `T`.

    Finding (pinpointed by the variants below): structure parameters work fine,
    INCLUDING `Type 1` structures with type-valued fields, UNTIL the generated
    *output's type is a projection of the structure parameter* (`x : p.Elem`).
    That case fails during derivation with `unknown free variable p_1` — the
    deriver freshens the parameter name (`p ↦ p_1`) but does not consistently
    re-bind it inside the projected output type. This is exactly Strata's shape
    (`e : LExpr T.mono`), so it is a genuine blocker, not a lesser issue. -/

open Plausible
set_option guard_msgs.diff true

/-! ### Baseline 1 — plain type parameter `α : Type`, output type IS `α`.
    Works (cf. the `Foo` example in DeriveSTLCGenerator.lean). -/
inductive BoxedA (α : Type) : α → Prop where
  | mk : ∀ (x : α), BoxedA α x

derive_generator (fun (α : Type) [Arbitrary α] => ∃ (x : α), BoxedA α x)

/-! ### Baseline 2 — `Type 1` structure with a type-valued field, but the
    indexed/output arg has a FIXED type (`Nat`), not the field. Works. -/
structure PC : Type 1 where
  Elem : Type
  k : Nat

inductive BoxedC (p : PC) : Nat → Prop where
  | mk : BoxedC p p.k

derive_generator (fun (p : PC) => ∃ (x : Nat), BoxedC p x)

/-! ### The failing case — output type is a projection `p.Elem` of the structure
    parameter. A `Type 0` structure suffices (so it is NOT a universe issue).
    Fails at derivation time:  `error: unknown free variable p_1`. -/
structure PE where
  Elem : Type

inductive BoxedE (p : PE) : p.Elem → Prop where
  | mk : ∀ (x : p.Elem), BoxedE p x

-- Expected (today): `error: unknown free variable p_1`
derive_generator (fun (p : PE) [Arbitrary p.Elem] => ∃ (x : p.Elem), BoxedE p x)
