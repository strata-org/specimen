import Specimen.DecOpt
import Specimen.DeriveChecker
import Specimen.EnumeratorCombinators
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveEnumSuchThat.DeriveSTLCEnumerator
import SpecimenTest.CommonDefinitions.STLCDefinitions

/-! Snapshot test: derived `DecOpt` checker for the STLC typing relation. -/

open DecOpt

set_option guard_msgs.diff true

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

derive_mutual checker
  (fun Γ e τ => typing Γ e τ)


#guard_msgs(drop info, drop warning) in
derive_checker (fun Γ e τ => typing Γ e τ)
