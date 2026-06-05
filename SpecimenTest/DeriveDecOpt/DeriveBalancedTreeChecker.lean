import Specimen.DecOpt
import Specimen.DeriveChecker
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

/-! Snapshot test: derived `DecOpt` checker for the `balancedTree` relation. -/

open DecOpt

set_option guard_msgs.diff true

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

derive_mutual checker
  (fun n t => balancedTree n t)


#guard_msgs(drop info, drop warning) in
derive_checker (fun n t => balancedTree n t)
