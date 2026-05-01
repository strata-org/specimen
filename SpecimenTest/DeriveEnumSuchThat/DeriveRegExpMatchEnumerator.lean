import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

/-! Snapshot test: derived constrained enumerator for the `ExpMatch` regex-matching relation. -/

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun r0 => ∃ (s : List Nat), ExpMatch s r0)

-- To sample from this enumerator, we can run the following:
#guard_msgs(drop info) in
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun s => ExpMatch s r)) 10
