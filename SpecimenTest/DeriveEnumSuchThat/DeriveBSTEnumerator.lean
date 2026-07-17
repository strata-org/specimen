import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBSTGenerator

/-! Snapshot test: derived constrained enumerator for the `Between` and `BST` relations. -/

set_option guard_msgs.diff true

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

#guard_msgs(drop info, drop warning) in
derive_mutual enumerator
  (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)


#guard_msgs(drop info) in
derive_enumerator (fun lo hi => ∃ (x : Nat), Between lo x hi)

#guard_msgs(drop info) in
derive_enumerator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)
