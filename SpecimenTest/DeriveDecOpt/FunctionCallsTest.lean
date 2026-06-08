import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveChecker
import Specimen.EnumeratorCombinators
import SpecimenTest.CommonDefinitions.FunctionCallInConclusion

/-! Snapshot test: derived checker for relations with function calls in constructor conclusions. -/

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info) in
derive_checker (fun n m => square_of n m)
