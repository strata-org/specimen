import Specimen
import Specimen.Basalt
import Specimen.Correctness.FloorOf
import Specimen.Correctness.CompleteOf

/-! Derived floors with soundness, the floor's lower bound, and completeness, all emitted. -/

namespace Specimen.Correctness.FloorCompleteTest
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
set_option specimen.emitComplete true

derive_mutual generator (fun τ => ∃ t, HasTy t τ)

example (τ : Ty) (t : Tm) (h : HasTy t τ) :
    ∃ n, ∀ s l, n ≤ s → n ≤ l → Produces (BacktrackGenFor.gen (P := fun t => HasTy t τ) (G := SGen) s l) t :=
  BacktrackGenForComplete.complete t h

#print axioms specimen_gen_Specimen_Correctness_FloorCompleteTest_HasTy_0__Specimen_Correctness_FloorCompleteTest_Specimen_Correctness_FloorCompleteTest.complete
#print axioms specimen_gen_Specimen_Correctness_FloorCompleteTest_HasTy_0__Specimen_Correctness_FloorCompleteTest_Specimen_Correctness_FloorCompleteTest.floorSound

end Specimen.Correctness.FloorCompleteTest
