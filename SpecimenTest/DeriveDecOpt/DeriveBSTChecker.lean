import Specimen.DecOpt
import Specimen.DeriveChecker
import Specimen.EnumeratorCombinators
import SpecimenTest.CommonDefinitions.BinaryTree
import Plausible.Attr

/-! Snapshot test: derived `DecOpt` checker for the `Between` and `BST` relations. -/

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info) in
derive_checker (fun lo x hi => Between lo x hi)

#guard_msgs(drop info) in
derive_checker (fun lo hi t => BST lo hi t)
