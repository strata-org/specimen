import Specimen.DecOpt
import Specimen.DeriveChecker
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.CommonDefinitions.ListRelations

/-! Snapshot test: derived checker for relations requiring simultaneous matching on multiple inputs. -/

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun x l => InList x l)

#guard_msgs(drop info, drop warning) in
derive_checker (fun l a => MinOk l a)

#guard_msgs(drop info, drop warning) in
derive_checker (fun n l a => MinEx n l a)
