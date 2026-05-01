import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

/-! Snapshot test: derived constrained enumerator for the `balancedTree` relation. -/

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun n => ∃ (t : BinaryTree), balancedTree n t)
