import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary
import Plausible.Arbitrary

/-! Test: derive constrained generators with multiple existential output variables. -/

open Plausible

set_option guard_msgs.diff true

-- A simple non-recursive relation where two outputs can be determined from one input
inductive Split : Nat → Nat → Nat → Prop where
  | zero : Split 0 0 0
  | left : Split n.succ n 1
  | right : Split n.succ 1 n

deriving instance Arbitrary for Nat

-- Multiple outputs: generate both a and b such that Split n a b holds (for a given n)
#guard_msgs(drop info) in
derive_generator (fun n => ∃ a b, Split n a b)

-- Verify the instance was created for the product type
#guard_msgs(drop info) in
#check (inferInstance : ArbitrarySizedSuchThat (Nat × Nat) (fun (a, b) => Split 5 a b))

set_option trace.plausible.deriving.results true

#guard_msgs(drop info) in
derive_generator (∃ a n b, Split n a b)
