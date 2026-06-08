import Specimen.DecOpt
import Specimen.DeriveChecker
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveArbitrarySuchThat.NonLinearPatternsTest

/-! Snapshot test: derived checker for relations with non-linear (repeated-variable) patterns. -/

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info) in
derive_checker (fun in1 in2 t => GoodTree in1 in2 t)
