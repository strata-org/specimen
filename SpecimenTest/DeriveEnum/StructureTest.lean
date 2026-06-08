import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.DeriveEnum
import SpecimenTest.DeriveArbitrary.StructureTest

/-! Snapshot test: derived `Enum` instance for structures with named fields. -/

set_option guard_msgs.diff true

deriving instance Enum for Foo

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

#guard_msgs(drop info) in
#synth EnumSized Foo

#guard_msgs(drop info) in
#synth Enum Foo

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(drop info) in
derive_enum Foo

end CommandElaboratorTest
