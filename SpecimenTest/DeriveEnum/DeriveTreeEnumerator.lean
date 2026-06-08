import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.DeriveEnum
import SpecimenTest.CommonDefinitions.BinaryTree

/-! Snapshot test: derived `Enum` instance for binary trees. -/

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Enum for BinaryTree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

#guard_msgs(drop info) in
#synth EnumSized BinaryTree

#guard_msgs(drop info) in
#synth Enum BinaryTree

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(drop info) in
derive_enum BinaryTree

end CommandElaboratorTest
