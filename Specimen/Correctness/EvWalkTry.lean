import Specimen.Correctness.WalkSGen
import Specimen.Correctness.SizeMeasureExamples
open Basalt
namespace Specimen.Correctness
open Specimen.Correctness.EvSlice

/-- The rules' own goals: a failure, or one constructor. -/
macro "ev_close" : tactic => `(tactic| first
    | assumption
    | (intro x hx; exact absurd hx (‹IsFailure _› x))
    | (intro x hx; cases hx; exact Ev.z)
    | (intro x hx; cases hx; exact Ev.ss (‹SoundPost _ _ _› _ rfl)))

/-- `Ev`'s step obligation, by `walk`: the previous level's soundness is the only fact, and what is
left is one goal per rule, closed by that rule's constructor. -/
theorem evStepS_sound_walk : StepGenSoundB evStepS (fun _ n => Ev n) := by
  refine stepGenSoundB_of_obs fun prev hprev sz i => ?_
  cases i
  unfold evStepS stepBacktrackB evBranchesS
  cases sz with
  | zero => walk; all_goals ev_close
  | succ sz' => walk [hprev sz' ()]; all_goals ev_close

/-- **Soundness**, as a Basalt law, from the generic theorem. -/
theorem evS_isSoundFor (sz : Nat) :
    IsSoundFor (fixGen evStepS sz ()).run.run (fun o => ∀ x, o = some (.ok x) → Ev x) :=
  fixGen_isSoundFor evStepS_sound_walk sz ()

end Specimen.Correctness

/-- info: 'Specimen.Correctness.evS_isSoundFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specimen.Correctness.evS_isSoundFor

namespace Specimen.Correctness
open Specimen.Correctness.EvSlice

theorem evStepS_complete_walk : StepGenCompleteS evStepS (fun _ n => Ev n) (fun _ n => n / 2) := by
  refine stepGenCompleteS_of_obs fun prev sz i a hEv hσ hrec => ?_
  cases i
  unfold evStepS stepBacktrackB evBranchesS
  have hok : OkOnly fun o : Option (Except Exhaustion Nat) => o = some (.ok a) := fun _ h => ⟨a, h⟩
  cases sz with
  | zero =>
    walk
    refine ⟨hok, ?_⟩
    cases hEv with
    | z => exact Or.inl ⟨Nat.one_pos, rfl⟩
    | ss => simp at hσ
  | succ sz' =>
    walk
    refine ⟨hok, ?_⟩
    cases hEv with
    | z => exact Or.inl ⟨Nat.one_pos, rfl⟩
    | @ss m hm =>
      obtain ⟨o, ho, rfl⟩ := hrec sz' (by omega) () m hm (by omega)
      exact Or.inr (Or.inl ⟨Nat.one_pos, _, ho, rfl⟩)

theorem treeStep_complete_walk :
    StepGenCompleteS treeStep (fun _ _ => True) (fun _ t => t.nodes) := by
  refine stepGenCompleteS_of_obs fun prev sz i a _ hσ hrec => ?_
  cases i
  unfold treeStep stepBacktrackB treeBranches
  have hok : OkOnly fun o : Option (Except Exhaustion BTree) => o = some (.ok a) := fun _ h => ⟨a, h⟩
  cases sz with
  | zero =>
    walk
    refine ⟨hok, ?_⟩
    cases a with
    | leaf => exact Or.inl ⟨Nat.one_pos, rfl⟩
    | node => simp [BTree.nodes] at hσ
  | succ sz' =>
    walk
    refine ⟨hok, ?_⟩
    cases a with
    | leaf => exact Or.inl ⟨Nat.one_pos, rfl⟩
    | node l r =>
      simp only [BTree.nodes] at hσ
      refine Or.inr (Or.inl ⟨Nat.one_pos, _, produces_arbitrarySized_nat sz' l.nodes (by omega), ?_⟩)
      obtain ⟨ol, hol, rfl⟩ := hrec (min l.nodes sz') (by omega) () l trivial (by omega)
      obtain ⟨or_, hor, rfl⟩ := hrec (sz' - l.nodes) (by omega) () r trivial (by omega)
      exact ⟨_, hol, _, hor, rfl⟩

/-- **Completeness for the node count**, as a Basalt law, from the generic theorem. -/
theorem tree_isCompleteFor (sz : Nat) :
    IsCompleteFor (fixGen treeStep sz ()).run.run
      (fun o => ∃ t, o = some (.ok t) ∧ True ∧ t.nodes ≤ sz) :=
  fixGen_isCompleteFor treeStep_sizeDecreasing treeStep_complete_walk sz ()

end Specimen.Correctness

/-- info: 'Specimen.Correctness.tree_isCompleteFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specimen.Correctness.tree_isCompleteFor
