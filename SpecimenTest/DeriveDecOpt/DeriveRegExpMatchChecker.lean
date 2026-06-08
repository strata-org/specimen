import Specimen.DecOpt
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.DeriveEnum
import SpecimenTest.DeriveArbitrary.DeriveRegExpGenerator
import SpecimenTest.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator
import SpecimenTest.DeriveEnum.DeriveRegExpEnumerator
import SpecimenTest.DeriveEnumSuchThat.DeriveRegExpMatchEnumerator

import Plausible.Attr

/-! Snapshot test: derived `DecOpt` checker for the `ExpMatch` regex-matching relation. -/


open DecOpt

set_option guard_msgs.diff true

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

derive_mutual checker
  (fun s r0 => ExpMatch s r0)


#guard_msgs(drop info) in
derive_checker (fun s r0 => ExpMatch s r0)
