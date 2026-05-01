import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.DeriveEnum
import SpecimenTest.DeriveArbitrary.DeriveRegExpGenerator

/-! Snapshot test: derived `Enum` instance for regular expressions. -/

set_option guard_msgs.diff true

deriving instance Enum for RegExp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

#guard_msgs(drop info, drop warning) in
#synth EnumSized RegExp

#guard_msgs(drop info, drop warning) in
#synth Enum RegExp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(drop info, drop warning) in
derive_enum RegExp

end CommandElaboratorTest
