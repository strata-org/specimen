import Specimen
import Specimen.Basalt
import Specimen.Correctness.FloorOf

/-! Mutual floors: two typing relations calling each other, floors derived and proved together. -/

namespace Specimen.Correctness.FloorOfMutualTest
open Basalt Specimen.Correctness

inductive Ty where
  | nat
  | prod (a b : Ty)

inductive Tm where
  | z
  | s (t : Tm)
  | mk (a b : Tm)

mutual
inductive TA : Tm → Ty → Prop where
  | z : TA .z .nat
  | s : ∀ t, TB t .nat → TA (.s t) .nat
  | mk : ∀ a b A B, TA a A → TB b B → TA (.mk a b) (.prod A B)
inductive TB : Tm → Ty → Prop where
  | z : TB .z .nat
  | s : ∀ t, TA t .nat → TB (.s t) .nat
  | mk : ∀ a b A B, TB a A → TA b B → TB (.mk a b) (.prod A B)
end

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.sizeSplit true
set_option specimen.deriveFloors true
set_option specimen.emitSound true
set_option specimen.reportPhaseTimers true

derive_mutual generator (fun τ => ∃ t, TA t τ)

#check @specimen_gen_Specimen_Correctness_FloorOfMutualTest_TA_0__Specimen_Correctness_FloorOfMutualTest_Specimen_Correctness_FloorOfMutualTest.floorSound
#print axioms specimen_gen_Specimen_Correctness_FloorOfMutualTest_TA_0__Specimen_Correctness_FloorOfMutualTest_Specimen_Correctness_FloorOfMutualTest.floorSound
#check @specimen_gen_Specimen_Correctness_FloorOfMutualTest_TB_0__Specimen_Correctness_FloorOfMutualTest_Specimen_Correctness_FloorOfMutualTest.floorSound
#print axioms specimen_gen_Specimen_Correctness_FloorOfMutualTest_TB_0__Specimen_Correctness_FloorOfMutualTest_Specimen_Correctness_FloorOfMutualTest.floorSound
#print specimen_gen_Specimen_Correctness_FloorOfMutualTest_TA_0__Specimen_Correctness_FloorOfMutualTest_Specimen_Correctness_FloorOfMutualTest.floor

end Specimen.Correctness.FloorOfMutualTest
