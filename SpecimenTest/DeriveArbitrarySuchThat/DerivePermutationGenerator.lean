import Specimen.DeriveConstrainedProducer
import Specimen.ArbitrarySizedSuchThat
import SpecimenTest.CommonDefinitions.Permutation

/-! Snapshot test: derived constrained generator for list permutations. -/

#guard_msgs(drop info) in
derive_generator (fun l' => ∃ (l : List Nat), Permutation l l')

#guard_msgs(drop info) in
derive_generator (fun l' => ∃ (l : List Nat), Permutation l' l)
