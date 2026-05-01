import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary
import Plausible.Arbitrary

open Plausible

set_option guard_msgs.diff true

/-! ## Output type depending on fun-bound variable

When the existential variable's type depends on a fun-bound variable
(e.g., `∃ (b : Box α), Wraps α x b` where `α` is bound by `fun`),
elaboration may replace the output variable with a metavar application
in the inductive's arguments. The deriver finds the output position by
elimination from the input fvars. -/

inductive Box (α : Type) where
  | mk : α → Box α
  deriving Repr

deriving instance Arbitrary for Box

inductive Wraps (α : Type) : α → Box α → Prop where
  | wrap : Wraps α x (.mk x)

set_option maxHeartbeats 400000

#guard_msgs(drop info, drop warning) in
derive_generator (fun (α : Type) (_inst : DecidableEq α) (x : α) =>
  ∃ (b : Box α), @Wraps α x b)

#guard_msgs(drop info, drop warning) in
#synth ArbitrarySizedSuchThat (Box Nat) (fun b => Wraps Nat 42 b)
