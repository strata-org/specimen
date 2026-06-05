import Specimen.DeriveChecker
import Specimen.EnumeratorCombinators
import SpecimenTest.CommonDefinitions.Permutation
import SpecimenTest.DeriveEnumSuchThat.DerivePermutationEnumerator

/-! Snapshot test: derived `DecOpt` checker for the `Permutation` relation. -/

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

derive_mutual checker
  (fun l l' => Permutation l l')



#guard_msgs(drop info, drop warning) in
derive_checker (fun l l' => Permutation l l')


-- Example: to run the derived checker, you can uncomment the following
def l := [1, 2, 3, 4]
def l' := [2, 1, 3, 4]
/--info: true-/
#guard_msgs in
#eval (DecOpt.decOpt (Permutation l l')) 0
