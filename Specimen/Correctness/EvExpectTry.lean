import Specimen.Correctness.WalkSGenExpect
import Specimen.Correctness.SizeMeasureExamples
open Basalt ENNReal
namespace Specimen.Correctness

/-- Success with `0`. -/
noncomputable def isZero : Option (Except Exhaustion Nat) → ℝ≥0∞ := fun o =>
  if o = some (.ok 0) then 1 else 0

theorem ev_zero_half (sz' : Nat) : (2 : ℝ≥0∞)⁻¹ ≤ SPMF.expectObs.spec (fixGen evStepS (sz' + 1) () : SGen Nat) isZero := by
  rw [fixGen_eq evStepS_sizeDecreasing]
  unfold evStepS stepBacktrackB evBranchesS
  have h0 : ∀ m post, (0 : ℝ≥0∞) ≤ SPMF.expectObs.spec (fixGen evStepS m () : SGen Nat) post :=
    fun _ _ => zero_le
  walk [h0]
  · simp [isZero]
  · intro o ho; simp only [isZero]; rw [if_neg fun h => ho 0 h]
  · simp [Backtrack.sumWeights]
end Specimen.Correctness

/-- info: 'Specimen.Correctness.ev_zero_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specimen.Correctness.ev_zero_half
