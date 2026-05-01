import Specimen.DecOpt
import Specimen.DeriveChecker
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveEnumSuchThat.DeriveSTLCEnumerator
import SpecimenTest.CommonDefinitions.STLCDefinitions

/-! Snapshot test: derived `DecOpt` checker for the STLC typing relation. -/

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun Γ e τ => typing Γ e τ)
