import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveEnumSuchThat.DeriveBSTEnumerator

-- See `Test/DeriveArbitrarySuchThat/NonLinearPatternsTest.lean` for the definition of the inductive relations
import SpecimenTest.DeriveArbitrarySuchThat.NonLinearPatternsTest

/-! Snapshot test: derived constrained enumerator for relations with non-linear patterns. -/

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun in1 in2 => ∃ (t : BinaryTree), GoodTree in1 in2 t)
