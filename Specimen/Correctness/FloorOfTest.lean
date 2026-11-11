import Specimen
import Specimen.Basalt
import Specimen.Correctness.FloorOf

/-! `specimen.deriveFloors` with `specimen.emitSound`: the floor derived, used, and proved a lower bound. -/

namespace Specimen.Correctness.FloorOfTest
open Basalt Specimen.Correctness

inductive Ty where
  | nat
  | prod (a b : Ty)

inductive Tm where
  | z
  | s (t : Tm)
  | mk (a b : Tm)

inductive HasTy : Tm → Ty → Prop where
  | z : HasTy .z .nat
  | s : ∀ t, HasTy t .nat → HasTy (.s t) .nat
  | mk : ∀ a b A B, HasTy a A → HasTy b B → HasTy (.mk a b) (.prod A B)

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.sizeSplit true
set_option specimen.deriveFloors true
set_option specimen.emitSound true

derive_mutual generator (fun τ => ∃ t, HasTy t τ)

#check @specimen_gen_Specimen_Correctness_FloorOfTest_HasTy_0__Specimen_Correctness_FloorOfTest_Specimen_Correctness_FloorOfTest.floorSound
#print axioms specimen_gen_Specimen_Correctness_FloorOfTest_HasTy_0__Specimen_Correctness_FloorOfTest_Specimen_Correctness_FloorOfTest.floorSound
#print axioms specimen_gen_Specimen_Correctness_FloorOfTest_HasTy_0__Specimen_Correctness_FloorOfTest_Specimen_Correctness_FloorOfTest.sound

end Specimen.Correctness.FloorOfTest
