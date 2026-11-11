import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace SuiteF.Perm
inductive Permutation : List Nat → List Nat → Prop where
  | PermNil : Permutation [] []
  | PermSkip : ∀ (x : Nat) (l l' : List Nat), Permutation l l' → Permutation (x :: l) (x :: l')
  | PermSwap : ∀ (x y : Nat) (l : List Nat), Permutation (y :: x :: l) (x :: y :: l)
  | PermTrans : ∀ (l l' l'' : List Nat), Permutation l l' → Permutation l' l'' → Permutation l l''

set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun l' => ∃ (l : List Nat), Permutation l l'),
  checker (fun l l' => Permutation l l')

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end SuiteF.Perm
