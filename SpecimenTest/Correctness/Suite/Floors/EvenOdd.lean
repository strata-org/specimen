import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace SuiteF.EvenOdd
mutual
  inductive Even : Nat → Prop where
    | zero_is_even : Even .zero
    | succ_of_odd_is_even : ∀ n : Nat, Odd n → Even (.succ n)
  inductive Odd : Nat → Prop where
    | succ_of_even_is_odd : ∀ n : Nat, Even n → Odd (.succ n)
end

set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (∃ (n : Nat), Even n), enumerator (∃ (n : Nat), Odd n),
  checker (fun n => Even n)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end SuiteF.EvenOdd
