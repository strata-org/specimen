import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

/-! Snapshot test: derived constrained enumerator for the `balancedTree` relation. -/

set_option guard_msgs.diff true


set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

#guard_msgs(drop info) in
derive_mutual enumerator
  (fun n => ∃ (t : BinaryTree), balancedTree n t)

#guard_msgs(drop info) in
derive_enumerator (fun n => ∃ (t : BinaryTree), balancedTree n t)
