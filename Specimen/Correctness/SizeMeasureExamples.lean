import Specimen.Correctness.SizeMeasure
import Specimen.Correctness.LeafSPMF
import Specimen.Correctness.EvSlice

/-!
# Size as the measure: two generators in the emitted shape

`Ev`'s generator as the emitter writes it (`match size with | 0 => … | size' + 1 => …`, recursion at
`size'`), proved sound and complete by induction on the size: no fuel appears in either statement.

Then a binary tree generator whose node splits its budget *arbitrarily* between the children, drawing
the left child's share. It is complete for the natural measure, the number of nodes: every tree of `n`
nodes is produced at size `n`. With a fixed split (`size' / 2` to each child) the size a tree needs grows
with its depth instead, so a lopsided tree of few nodes needs a large size.
-/

open Basalt

namespace Specimen.Correctness

open Specimen.Correctness.EvSlice

/-! ## `Ev` -/

/-- The branches as emitted: at size `0` only the base rule, above it both, the recursive one at `size'`. -/
noncomputable def evBranchesS : BranchList Unit Nat :=
  fun prev sz _ => match sz with
    | 0 => [(1, fun () => pure 0)]
    | sz' + 1 => [(1, fun () => pure 0), (1, fun () => do let n ← prev sz' (); pure (n + 2))]

noncomputable def evStepS : SGenStep Unit Nat := stepBacktrackB evBranchesS

theorem evStepS_sizeDecreasing : SizeDecreasing evStepS :=
  stepBacktrackB_sizeDecreasing fun prev prev' sz i h => by
    cases sz with
    | zero => rfl
    | succ sz' => simp only [evBranchesS, h sz' (Nat.lt_succ_self _) ()]

theorem evStepS_sound : StepGenSoundB evStepS (fun _ n => Ev n) := by
  refine stepBacktrackB_sound (fun prev hprev sz i p hp x hx => ?_)
  cases sz with
  | zero =>
    simp only [evBranchesS, List.mem_singleton] at hp; subst hp
    cases produces_pure_iff.mp hx; exact Ev.z
  | succ sz' =>
    simp only [evBranchesS, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · cases produces_pure_iff.mp hx; exact Ev.z
    · obtain ⟨n, hn, hx⟩ := produces_bind_iff.mp hx
      cases produces_pure_iff.mp hx; exact Ev.ss (hprev sz' () n hn)

theorem evStepS_complete : StepGenCompleteS evStepS (fun _ n => Ev n) (fun _ n => n / 2) := by
  refine stepBacktrackB_completeS (fun prev sz i a hEv hsz hrec => ?_)
  cases hEv with
  | z =>
    cases sz with
    | zero => exact ⟨_, List.Mem.head _, Nat.one_pos, produces_pure_iff.mpr rfl⟩
    | succ sz' => exact ⟨_, List.Mem.head _, Nat.one_pos, produces_pure_iff.mpr rfl⟩
  | @ss m hm =>
    cases sz with
    | zero => simp at hsz
    | succ sz' =>
      refine ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.one_pos, ?_⟩
      exact produces_bind_of (hrec sz' (Nat.lt_succ_self _) () m hm (by simp at hsz ⊢; omega))
        (produces_pure_iff.mpr rfl)

/-- **Soundness** at every size. -/
theorem evGenS_sound (sz : Nat) (x : Nat) (h : Produces (fixGen evStepS sz ()) x) : Ev x :=
  fixGen_sound evStepS_sound sz () x h

/-- **Completeness**: `n` is produced at size `n / 2`, and at every larger size. -/
theorem evGenS_complete (n : Nat) (h : Ev n) (sz : Nat) (hsz : n / 2 ≤ sz) :
    Produces (fixGen evStepS sz ()) n :=
  fixGen_complete evStepS_sizeDecreasing evStepS_complete sz () n h hsz

/-! ## Binary trees, with the budget split arbitrarily -/

inductive BTree where
  | leaf
  | node (l r : BTree)
  deriving DecidableEq

def BTree.nodes : BTree → Nat
  | .leaf => 0
  | .node l r => l.nodes + r.nodes + 1

/-- At size `sz' + 1` a node draws the left child's share `k ≤ sz'` and gives the right `sz' - k`. -/
noncomputable def treeBranches : BranchList Unit BTree :=
  fun prev sz _ => match sz with
    | 0 => [(1, fun () => pure .leaf)]
    | sz' + 1 => [(1, fun () => pure .leaf), (1, fun () => do
        let k ← (ArbitrarySized.arbitrarySized sz' : SGen Nat)
        let l ← prev (min k sz') ()
        let r ← prev (sz' - k) ()
        pure (.node l r))]

noncomputable def treeStep : SGenStep Unit BTree := stepBacktrackB treeBranches

theorem treeStep_sizeDecreasing : SizeDecreasing treeStep :=
  stepBacktrackB_sizeDecreasing fun prev prev' sz i h => by
    cases sz with
    | zero => rfl
    | succ sz' =>
      have hl : ∀ k, prev (min k sz') () = prev' (min k sz') () :=
        fun k => h _ (by omega) ()
      have hr : ∀ k, prev (sz' - k) () = prev' (sz' - k) () := fun k => h _ (by omega) ()
      simp only [treeBranches, hl, hr]

/-- **Completeness for the node count**: every tree of `n` nodes is produced at size `n` and above. -/
theorem treeStep_complete :
    StepGenCompleteS treeStep (fun _ _ => True) (fun _ t => t.nodes) := by
  refine stepBacktrackB_completeS (fun prev sz i a _ hsz hrec => ?_)
  cases a with
  | leaf =>
    cases sz with
    | zero => exact ⟨_, List.Mem.head _, Nat.one_pos, produces_pure_iff.mpr rfl⟩
    | succ sz' => exact ⟨_, List.Mem.head _, Nat.one_pos, produces_pure_iff.mpr rfl⟩
  | node l r =>
    cases sz with
    | zero => simp [BTree.nodes] at hsz
    | succ sz' =>
      simp only [BTree.nodes] at hsz
      refine ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.one_pos, ?_⟩
      -- Draw exactly the left child's node count.
      refine produces_bind_of (produces_arbitrarySized_nat sz' l.nodes (by omega)) ?_
      refine produces_bind_of (hrec _ (by omega) () l trivial (by omega)) ?_
      refine produces_bind_of (hrec _ (by omega) () r trivial (by omega)) ?_
      exact produces_pure_iff.mpr rfl

theorem treeGen_complete (t : BTree) (sz : Nat) (hsz : t.nodes ≤ sz) :
    Produces (fixGen treeStep sz ()) t :=
  fixGen_complete treeStep_sizeDecreasing treeStep_complete sz () t trivial hsz

end Specimen.Correctness

/-- info: 'Specimen.Correctness.treeGen_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specimen.Correctness.treeGen_complete
