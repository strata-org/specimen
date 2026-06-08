import Specimen.DecOpt
import Specimen.DeriveChecker
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

/-! Snapshot test: derived `DecOpt` checker for the `balancedTree` relation. -/

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info) in
derive_checker (fun n t => balancedTree n t)
