import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.CommonDefinitions.Permutation

/-! Snapshot test: derived constrained enumerator for the `Permutation` relation. -/

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

#guard_msgs(drop info, drop warning) in
derive_mutual enumerator
  (∃ l l', Permutation l' l)



#guard_msgs(drop info) in
derive_enumerator (fun l' => ∃ (l : List Nat), Permutation l l')

#guard_msgs(drop info) in
derive_enumerator (fun l' => ∃ (l : List Nat), Permutation l' l)
