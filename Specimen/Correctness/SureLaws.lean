import Specimen.Correctness.CondMean
import Specimen.Correctness.SplitLaws

/-!
# Generators that succeed surely

`sok g = 1`: every run of `g` succeeds. A bind does where its continuation does on what the first part
can produce; a search does where one of its live branches does and none loses mass; the size split
always does.
-/

open ENNReal Basalt

namespace Specimen.Correctness

open Specimen.Backtrack Specimen.SizeSplit

variable {A B : Type}

theorem sok_bind_one_of_support {g : SGen A} {k : A → SGen B} (hg : sok g = 1)
    (hk : ∀ a, Produces g a → sok (k a) = 1) : sok (g >>= k) = 1 := by
  rw [sok_bind]
  unfold sexpect
  rw [show SPMF.expect g.run.run (succVal fun a => sok (k a)) = SPMF.expect g.run.run (succVal fun _ => 1) from
    SPMF.expect_congr_support fun o ho => by
      rcases o with _ | _ | a
      · rfl
      · rfl
      · exact hk a ho]
  exact hg

theorem chooseNat_range {lo hi : Nat} {h : lo ≤ hi} {n : Nat} (hn : Produces (chooseNat lo hi h : SGen Nat) n) :
    lo ≤ n ∧ n ≤ hi := by
  have : succObs.spec (chooseNat lo hi h : SGen Nat) (fun n => lo ≤ n ∧ n ≤ hi) := by walk <;> omega
  exact this n hn

theorem sok_chooseNat (lo hi : Nat) (h : lo ≤ hi) : sok (chooseNat lo hi h : SGen Nat) = 1 := by
  unfold sok
  rw [sexpect_chooseNat]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [show hi + 1 - lo = hi - lo + 1 by omega]
  exact ENNReal.div_self (by simp) (by simp)

theorem sok_frequencyAux {gs : List (Nat × (Unit → SGen A))} (hall : ∀ p ∈ gs, 0 < p.1 → sok (p.2 ()) = 1) :
    ∀ (n : Nat) (h : n < (gs.map Prod.fst).sum), sok (frequencyAux gs n h) = 1 := by
  induction gs with
  | nil => intro n h; simp at h
  | cons q gs ih =>
    intro n h
    obtain ⟨k, x⟩ := q
    simp only [frequencyAux]
    split
    · rename_i hlt
      exact hall _ List.mem_cons_self (by simp only; omega)
    · exact ih (fun p hp => hall p (List.mem_cons_of_mem _ hp)) _ _

theorem sok_frequency {gs : List (Nat × (Unit → SGen A))} (h : 0 < (gs.map Prod.fst).sum)
    (hall : ∀ p ∈ gs, 0 < p.1 → sok (p.2 ()) = 1) : sok (frequency gs h) = 1 := by
  unfold frequency
  refine sok_bind_one_of_support (sok_chooseNat _ _ _) fun n hn => ?_
  have := (chooseNat_range hn).2
  rw [dite_cond_eq_true (eq_true (by omega))]
  exact sok_frequencyAux hall _ _

theorem sok_vectorOf {g : SGen A} (hg : sok g = 1) : ∀ n, sok (vectorOf n g) = 1
  | 0 => sok_pure _
  | n + 1 => by
    rw [vectorOf_succ]
    exact sok_bind_one hg fun _ => sok_bind_one (sok_vectorOf hg n) fun _ => sok_pure _

theorem sok_uniform : ∀ (k r : Nat), sok (uniform k r : SGen (List Nat)) = 1
  | 0, _ => sok_pure _
  | 1, _ => sok_pure _
  | k + 2, r => by
    show sok (do
      let j ← frequency ((List.range (r + 1)).map fun j => (count (r - j) k, fun _ => pure j))
        (weights_pos k r)
      let rest ← uniform (k + 1) (r - j)
      pure (j :: rest) : SGen (List Nat)) = 1
    refine sok_bind_one (sok_frequency _ fun p hp _ => ?_) fun _ =>
      sok_bind_one (sok_uniform (k + 1) _) fun _ => sok_pure _
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    exact sok_pure _

/-- **The size split always draws.** -/
theorem sok_draw (fs : List Nat) (total : Nat) : sok (draw fs total : SGen (List Nat)) = 1 := by
  unfold draw
  split
  · exact sok_bind_one (sok_uniform _ _) fun _ => sok_pure _
  · exact sok_pure _

/-! ## The search -/

theorem pickDrop_some_of_lt' {β : Type} : ∀ {gs : List (Nat × β)} {n : Nat}, n < sumWeights gs →
    ∃ k b rest, pickDrop gs n = some (k, b, rest)
  | [], _, h => by simp [sumWeights] at h
  | (k, b) :: gs, n, h => by
    by_cases hn : n < k
    · exact ⟨k, b, gs, by simp [pickDrop, hn]⟩
    · obtain ⟨k', b', r', h'⟩ := pickDrop_some_of_lt' (gs := gs) (n := n - k)
        (by simp only [sumWeights_cons] at h; omega)
      exact ⟨k', b', (k, b) :: r', by simp [pickDrop, hn, h']⟩

/-- What `pickDrop` leaves is the list without what it drew. -/
theorem pickDrop_mem_or {β : Type} : ∀ {gs : List (Nat × β)} {n k b rest},
    pickDrop gs n = some (k, b, rest) → rest.length + 1 = gs.length ∧ ∀ p ∈ gs, p = (k, b) ∨ p ∈ rest
  | [], _, _, _, _, h => by simp [pickDrop] at h
  | (k', b') :: gs, n, k, b, rest, h => by
    simp only [pickDrop] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun p hp => (List.mem_cons.mp hp).imp id id⟩
    · cases hp : pickDrop gs (n - k') with
      | none => simp [hp] at h
      | some t =>
        obtain ⟨k₀, b₀, r₀⟩ := t
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hl, hm⟩ := pickDrop_mem_or hp
        refine ⟨by simp [hl], fun p hp' => ?_⟩
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact Or.inr List.mem_cons_self
        · exact (hm p hp').imp id (List.mem_cons_of_mem _)

/-- A search succeeds surely where one of its live branches does and no branch loses mass: the drawn
branch either is that one, or fails into a search that still holds it. -/
theorem expect_searchWith_sure : ∀ (fuel : Nat) (gs : List (Nat × (Unit → SGen A))) (acc : Option Exhaustion),
    gs.length ≤ fuel → (∀ p ∈ gs, sok (p.2 ()) + sfail (p.2 ()) = 1) →
    (∃ p ∈ gs, 0 < p.1 ∧ sok (p.2 ()) = 1) →
    SPMF.expect (searchWith fuel gs acc).run (succVal fun _ => 1) = 1
  | _, [], _, _, _, ⟨_, h, _⟩ => absurd h (List.not_mem_nil)
  | 0, _ :: _, _, hl, _, _ => by simp at hl
  | fuel + 1, q :: gs, acc, hl, htot, ⟨p, hp, hw, hsure⟩ => by
    have hW : 0 < sumWeights (q :: gs) := Nat.lt_of_lt_of_le hw (by
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [sumWeights_cons]
      · have := le_sum_of_mem (f := Prod.fst) hp
        simp only [sumWeights, List.map_cons, List.sum_cons]; omega)
    rw [searchWith_succ_run, SPMF.expect_bind, SPMF.expect_chooseNat_zero hW]
    rw [show ∑ m ∈ Finset.range (sumWeights (q :: gs)), SPMF.expect (searchStep fuel (q :: gs) acc m)
        (succVal fun _ => 1) = ∑ _m ∈ Finset.range (sumWeights (q :: gs)), (1 : ℝ≥0∞) from
      Finset.sum_congr rfl fun m hm => ?_]
    · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact ENNReal.div_self (by exact_mod_cast hW.ne') (by simp)
    obtain ⟨k, g, rest, hpd⟩ := pickDrop_some_of_lt' (Finset.mem_range.mp hm)
    obtain ⟨hlen, hmem⟩ := pickDrop_mem_or hpd
    have hV := fun a => (profile_searchWith_congr fuel rest rest a none (BranchesAlike.refl rest)).1
    have hU := fun a => (profile_searchWith_congr fuel rest rest a none (BranchesAlike.refl rest)).2
    rw [(expect_searchStep_some hpd hV hU).1]
    have hg := htot _ (pickDrop_mem hpd)
    rcases hmem p hp with rfl | hpr
    · rw [hsure, sfail_eq_zero_of_sok hsure, mul_zero, add_zero]
    · rw [expect_searchWith_sure fuel rest none (by simp only [List.length_cons] at hl hlen; omega)
        (fun p' hp' => htot p' (pickDrop_rest_sub hpd p' hp')) ⟨p, hpr, hw, hsure⟩, one_mul]
      exact hg

/-- **A search succeeds surely** where one of its live branches does and no branch loses mass. -/
theorem sok_backtrack_of_sure {gs : List (Nat × (Unit → SGen A))}
    (htot : ∀ p ∈ gs, sok (p.2 ()) + sfail (p.2 ()) = 1) (h : ∃ p ∈ gs, 0 < p.1 ∧ sok (p.2 ()) = 1) :
    sok (Specimen.Backtrack.backtrack gs) = 1 :=
  expect_searchWith_sure gs.length gs none (Nat.le_refl _) htot h

theorem total_of_sok {g : SGen A} (h : sok g = 1) : sok g + sfail g = 1 := by
  rw [h, sfail_eq_zero_of_sok h, add_zero]

theorem total_failWith (e : Exhaustion) : sok (FailWith.failWith e : SGen A) + sfail (FailWith.failWith e : SGen A) = 1 := by
  simp [sok, sfail, sexpect, FailWith.failWith, OptionT.run_pure, SPMF.expect_pure, failVal, succVal]

theorem total_truncations (ls : List (Specimen.Label A)) :
    sok (Specimen.truncations ls : SGen A) + sfail (Specimen.truncations ls : SGen A) = 1 := by
  unfold Specimen.truncations
  split
  · simp [sok, sfail, sexpect, Fail.fail, Specimen.refute, ExceptT.lift, OptionT.run_failure,
      SPMF.expect_pure, failVal, succVal]
  · exact total_failWith _

/-- A generator that can produce nothing succeeds with probability `0`. -/
theorem sok_eq_zero {g : SGen A} (h : ∀ x, ¬ Produces g x) : sok g = 0 := by
  unfold sok sexpect
  rw [show SPMF.expect g.run.run (succVal fun _ => 1) = SPMF.expect g.run.run (fun _ => 0) from
    SPMF.expect_congr_support fun o ho => by
      rcases o with _ | _ | a
      · rfl
      · rfl
      · exact absurd ho (h a)]
  simp [SPMF.expect_const]

end Specimen.Correctness
