import Specimen.Correctness.Semantics
import Specimen.GeneratorCombinators

/-!
# Support laws for the real `Plausible.Gen`

What a generator built with `pure`, `>>=` and `backtrack` can produce, stated with `genSupportAt` (some
seed produces the value). Only the soundness direction holds, and it is proved here from the
definitions: a value produced by `m >>= k` comes from some value `m` produces and the state `m` leaves
behind, and a value produced by `backtrack` comes from one of its branches.

The reverse direction, that every combination of `m`'s and `k a`'s outcomes is reachable, is not
available. `Plausible.Gen` threads a single `StdGen` through `>>=` rather than splitting it as
QuickChick's `bindGen` does, so the seed `k a` sees is whatever `m` leaves, and not every pair need
occur. Generator completeness is therefore proved at Basalt's `SPMF` instead (`GenInterpSPMF`), where
both support laws are theorems.
-/

open Plausible GeneratorCombinators

namespace Specimen.Correctness

/-- Support of `pure` is a singleton. -/
theorem genSupportAt_pure {α : Type} (a x : α) (sz : Nat) :
    genSupportAt (pure a) sz x ↔ x = a := by
  unfold genSupportAt
  have key : ∀ seed, Gen.runPure (pure a) seed sz = Except.ok a := fun _ => rfl
  constructor
  · rintro ⟨seed, h⟩; rw [key] at h; exact (Except.ok.inj h).symm
  · rintro rfl; exact ⟨mkStdGen 0, key _⟩

/-- A value produced by `m >>= k` comes from a value `a` that `m` produces, and `k a` produces it from
    the state `m` leaves behind. -/
theorem genSupportAt_bind_sub {α β : Type} (m : Gen α) (k : α → Gen β) (sz : Nat) (x : β) :
    genSupportAt (m >>= k) sz x → ∃ a, genSupportAt m sz a ∧ genSupportAt (k a) sz x := by
  rintro ⟨seed, h⟩
  unfold Gen.runPure at h
  simp only [StateT.run_bind, ReaderT.run_bind] at h
  cases hm : ReaderT.run (StateT.run m { down := seed }) { down := sz } with
  | error e =>
    rw [hm] at h; exact absurd h (by simp [Except.map, bind, Except.bind])
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hm] at h
    refine ⟨a, ⟨seed, ?_⟩, ⟨s'.down, ?_⟩⟩
    · simp [Gen.runPure, hm, Except.map]
    · simpa [Gen.runPure, bind, Except.bind] using h

/-- The generator `pickDrop` selects is one of the list's, or the failing default once the list runs
    out. -/
private theorem pickDrop_gen {α : Type} (xs : List (Nat × Gen α)) (n : Nat) :
    (∃ p ∈ xs, (pickDrop xs n).2.1 = p.2) ∨
      (pickDrop xs n).2.1 = throw (.genError "Plausible.Specimen.GeneratorCombinators: failure.") := by
  induction xs generalizing n with
  | nil => right; rfl
  | cons hd tl ih =>
    obtain ⟨k, g⟩ := hd
    unfold pickDrop
    by_cases hn : n < k
    · left; exact ⟨(k, g), List.mem_cons_self, by simp [hn]⟩
    · simp only [hn, ite_false]
      rcases ih (n - k) with ⟨p, hp, he⟩ | he
      · left; exact ⟨p, List.mem_cons_of_mem _ hp, he⟩
      · right; exact he

/-- What `pickDrop` leaves is drawn from the list it was given. -/
private theorem pickDrop_rest {α : Type} (xs : List (Nat × Gen α)) (n : Nat) :
    ∀ q ∈ (pickDrop xs n).2.2, q ∈ xs := by
  induction xs generalizing n with
  | nil => intro q hq; simp [pickDrop] at hq
  | cons hd tl ih =>
    obtain ⟨k, g⟩ := hd
    intro q hq
    unfold pickDrop at hq
    by_cases hn : n < k
    · simp only [hn, ite_true] at hq; exact List.mem_cons_of_mem _ hq
    · simp only [hn, ite_false] at hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (n - k) q hq')


/-- A thrown error produces nothing. -/
private theorem throw_not_ok {α : Type} (e : GenError) (seed : StdGen) (sz : Nat) (x : α) :
    Gen.runPure (throw e : Gen α) seed sz ≠ .ok x := by
  intro h
  have he : Gen.runPure (throw e : Gen α) seed sz = Except.error e := rfl
  rw [he] at h; cases h


/-- A value produced by `backtrackFuel` comes from one of the branches it was given. Each attempt runs
    the picked branch from the state after the weighted draw; a failure retries the rest from that same
    state. -/
private theorem backtrackFuel_sub {α : Type} (fuel : Nat) :
    ∀ (total : Nat) (gs : List (Nat × Gen α)) (inc : Bool) (seed : StdGen) (sz : Nat) (x : α),
      Gen.runPure (backtrackFuel fuel total gs inc) seed sz = .ok x →
      ∃ p ∈ gs, genSupportAt p.2 sz x := by
  induction fuel with
  | zero =>
    intro total gs inc seed sz x h
    unfold backtrackFuel at h
    split at h <;> exact absurd h (throw_not_ok _ _ _ _)
  | succ fuel ih =>
    intro total gs inc seed sz x h
    unfold backtrackFuel at h
    unfold Gen.runPure at h
    simp only [StateT.run_bind, ReaderT.run_bind] at h
    cases hc : (StateT.run (Gen.choose Nat 0 (total - 1) (by omega)) { down := seed }).run { down := sz } with
    | error e => rw [hc] at h; simp [Except.map, bind, Except.bind] at h
    | ok r =>
      obtain ⟨⟨n, _⟩, s1⟩ := r
      rw [hc] at h
      simp only [bind, Except.bind] at h
      simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, StateT.run, ReaderT.run,
        Except.tryCatch] at h
      split at h
      · rename_i v hv
        simp only [Except.map, Except.ok.injEq] at h
        have hsup : genSupportAt (pickDrop gs n).2.1 sz x :=
          ⟨s1.down, by simp only [Gen.runPure, StateT.run, ReaderT.run]; rw [hv]; simp [Except.map, h]⟩
        rcases pickDrop_gen gs n with ⟨p, hp, he⟩ | he
        · exact ⟨p, hp, he ▸ hsup⟩
        · obtain ⟨sd, hsd⟩ := hsup
          rw [he] at hsd; exact absurd hsd (throw_not_ok _ _ _ _)
      · rename_i e he
        obtain ⟨p, hp, hsup⟩ := ih _ _ _ s1.down sz x h
        exact ⟨p, pickDrop_rest gs n p hp, hsup⟩

/-- A value produced by `backtrack gs` comes from one of the branches in `gs`. -/
theorem genSupportAt_backtrack_sub {α : Type} (gs : List (Nat × Gen α)) (sz : Nat) (x : α) :
    genSupportAt (backtrack gs) sz x → ∃ p ∈ gs, genSupportAt p.2 sz x := by
  rintro ⟨seed, h⟩
  exact backtrackFuel_sub _ _ _ _ seed sz x h

end Specimen.Correctness
