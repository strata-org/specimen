import Specimen.DeriveArbitrary
import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: does the structure-parameter projection blocker live in the
    UNCONSTRAINED path (`deriving Arbitrary`, Specimen/DeriveArbitrary.lean) or
    the CONSTRAINED path (`derive_generator`, Specimen/DeriveConstrainedProducer.lean)?

    Hypothesis (per observation): `deriving Arbitrary` handles structure params
    with projected fields; `derive_generator` / derive_mutual do not. We exercise
    BOTH on the same structure-parameter type, where the data carried / generated
    has a type that is a projection `T.Elem`. -/

open Plausible
set_option guard_msgs.diff true

structure P where
  Elem : Type

/-! ### Path 1 — UNCONSTRAINED `deriving Arbitrary`.
    `Wrap T` carries a value of the projected type `T.Elem`. -/
inductive Wrap (T : P) where
  | mk : T.Elem → Wrap T

deriving instance Arbitrary for Wrap

#guard_msgs(drop info) in
#synth Arbitrary (Wrap ⟨Nat⟩)   -- expect: success


/-! ### Path 2 — CONSTRAINED `derive_generator` on a relation whose generated
    OUTPUT has the projected type `T.Elem`. Same structure parameter `T`. -/
inductive Boxed (T : P) : T.Elem → Prop where
  | mk : ∀ (x : T.Elem), Boxed T x

-- expect (today): `error: unknown free variable T_1`
derive_generator (fun (T : P) [Arbitrary T.Elem] => ∃ (x : T.Elem), Boxed T x)
