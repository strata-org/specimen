import Specimen.DeriveConstrainedProducer
import Specimen.ArbitrarySizedSuchThat
import SpecimenTest.CommonDefinitions.Permutation

/-! Snapshot test: derived constrained generator for list permutations. -/

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

derive_mutual
  (∃ l l', Permutation l' l)

#guard_msgs(drop info, drop warning) in
derive_generator (fun l' => ∃ (l : List Nat), Permutation l l')

#guard_msgs(drop info, drop warning) in
derive_generator (fun l' => ∃ (l : List Nat), Permutation l' l)
