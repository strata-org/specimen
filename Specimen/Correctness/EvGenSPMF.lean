import Specimen.Correctness.GenInterpSPMF
import Specimen.Correctness.EvSlice

/-!
# The `Ev` slice's generator, via the generic interpreter

`EvSlice.lean` proves the `Ev` checker and enumerator sound and complete, and its generator sound at
the real `Plausible.Gen`. This file proves the generator sound and complete at Basalt's `SPMF` through
`GenInterpSPMF`, so all three producers for `Ev` are sound and complete. Only Lean's standard axioms
are used: `SPMF` is classical, so `Classical.choice` joins `propext` and `Quot.sound`.

It doubles as the validation that the generic interpreter is usable: the two `Step*` obligations are
discharged from per-branch facts only, with no reasoning about `backtrack` or about the support monad.

The branch weights are modelled faithfully rather than conveniently. The recursive branch gets weight
`size`, which is `0` exactly when `size = 0` — that is what `Scoring.balancedCtorWeight` does, and it
is the reason completeness needs a size measure at all. Give the branch a constant positive weight
instead and the `σ` hypothesis stops being needed, which would make the exercise vacuous.
-/

open Basalt

namespace Specimen.Correctness

open Specimen.Correctness.EvSlice

/-- The two constructor branches for `∃ n, Ev n`: `z` returns `0`; `ss` draws from the previous fuel
level at one less size and adds 2.

`Ev` takes no inputs, so the input index is `Unit` here. (`lookup` and `typing` are where that index
does real work — see `GenInterpSPMF`'s note on why it has to exist at all.) -/
noncomputable def evBranches : BranchList Unit Nat :=
  fun prev sz _ =>
    [ (1, fun () => pure 0),
      (sz, fun () => do let n ← prev (sz - 1) (); pure (n + 2)) ]

noncomputable def evGenStep : SGenStep Unit Nat := stepBacktrackB evBranches

/-- The specification, ignoring the trivial input. -/
def evSpec : Unit → Nat → Prop := fun _ n => Ev n

/-- Fuel measure: one level per `ss`. -/
def evPhi : Unit → Nat → Nat := fun _ n => n / 2

/-- Size measure: also one per `ss`, since this relation's recursion is linear. A halving constructor
would double here — cf. `budget` in `StlcCompleteness.lean`. -/
def evSigma : Unit → Nat → Nat := fun _ n => n / 2

theorem evGenStep_sound : StepGenSoundB evGenStep evSpec := by
  refine stepBacktrackB_sound (fun prev hprev sz i p hp x hx => ?_)
  -- Only two branches, and each is sound on its own; nothing about `backtrack` appears.
  rcases List.mem_cons.mp hp with rfl | hp
  · cases produces_pure_iff.mp hx; exact Ev.z
  · rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨n, hn, hx⟩ := produces_bind_iff.mp hx
      rw [produces_pure_iff] at hx
      cases hx; exact Ev.ss (hprev (sz - 1) () n hn)
    · exact absurd hp (by simp)

theorem evGenStep_complete : StepGenCompleteB evGenStep evSpec evPhi evSigma := by
  refine stepBacktrackB_complete (fun prev sz i a hEv hsz hrec => ?_)
  cases hEv with
  | z =>
    -- The base branch has constant weight 1, so it is live at every size.
    exact ⟨_, List.Mem.head _, Nat.zero_lt_one, produces_pure_iff.mpr rfl⟩
  | @ss m hm =>
    -- The recursive branch is live only because `evSigma (m + 2) ≤ sz` forces `sz ≥ 1`.
    have hsz1 : 0 < sz := by
      simp only [evSigma] at hsz; omega
    have hmsz : evSigma () m ≤ sz - 1 := by
      simp only [evSigma] at hsz ⊢; omega
    have hlt : evPhi () m < evPhi () (m + 2) := by simp only [evPhi]; omega
    refine ⟨_, List.Mem.tail _ (List.Mem.head _), hsz1, ?_⟩
    exact produces_bind_of (hrec () m hm hlt (sz - 1) hmsz) (produces_pure_iff.mpr rfl)

/-- **Soundness**: the generator only produces even numbers. -/
theorem evGen_sound : ∀ x, semGenRelB evGenStep () x → Ev x :=
  genRelB_sound evGenStep_sound ()

/-- **Completeness**: every even number is produced, at the fuel and size the measures predict. -/
theorem evGen_complete (n : Nat) (h : Ev n) :
    Produces (genRelB evGenStep (evPhi () n + 1) (evSigma () n) ()) n :=
  genRelB_complete' evGenStep_complete () n h

end Specimen.Correctness

-- Pinned: the `Ev` generator leg uses only Lean's standard axioms. `Classical.choice` comes from `SPMF`.
/-- info: 'Specimen.Correctness.evGen_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specimen.Correctness.evGen_sound

/-- info: 'Specimen.Correctness.evGen_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specimen.Correctness.evGen_complete
