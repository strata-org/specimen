import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace SuiteF.Split
inductive Split : Nat → Nat → Nat → Prop where
  | zero : Split 0 0 0
  | left : Split n.succ n 1
  | right : Split n.succ 1 n

set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun n => ∃ a b, Split n a b), generator (∃ a n b, Split n a b),
  enumerator (fun n => ∃ a b, Split n a b)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end SuiteF.Split
