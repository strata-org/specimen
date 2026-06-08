import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveDecOpt.SimultaneousMatchingTests

-- See `Test/CommonDefinitions/ListRelations.lean` for the definition of the inductive relations
import SpecimenTest.CommonDefinitions.ListRelations

/-! Snapshot test: derived constrained enumerator for relations with simultaneous matching. -/

set_option guard_msgs.diff true

#guard_msgs(drop info) in
derive_enumerator (fun x => ∃ (l : List Nat), InList x l)

#guard_msgs(drop info) in
derive_enumerator (fun a => ∃ (l: List Nat), MinOk l a)

#guard_msgs(drop info) in
derive_enumerator (fun n a => ∃ (l: List Nat), MinEx n l a)
