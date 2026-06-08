import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.CommonDefinitions.Permutation

/-! Snapshot test: derived constrained enumerator for the `Permutation` relation. -/


#guard_msgs(drop info) in
derive_enumerator (fun l' => ∃ (l : List Nat), Permutation l l')

#guard_msgs(drop info) in
derive_enumerator (fun l' => ∃ (l : List Nat), Permutation l' l)
