import Specimen.Correctness.GenInterpSPMF
import Basalt.SPMF.Expect.Obs

/-!
# Expectations over a derived generator's successes

`Produces` says what a generator at the sampler's monad `SGen` can succeed with; `sexpect g f` says
how much: the expectation of `f` over `g`'s successful runs, a refutation or a labelled failure
counting nothing, so `sprob g E` is the probability that `g` succeeds with a value in `E`. The rules
are Basalt's SPMF expectation (`SPMF.expect`) under the two transformers: exact for `pure` and
`bind`, zero for the failures, and for `backtrack` a lower bound by its first draw
(`sexpect_backtrack_ge`): whichever branch is drawn first, its successes are the search's, and a
retry after a failure only adds. That bound is the one a derived generator's distribution facts
need: that it succeeds with probability one where some branch always applies, and that a rule is
taken with at least its share of the weight.
-/

open ENNReal

namespace Specimen.Correctness

variable {A B : Type}

/-- What a run's outcome contributes to `f`: its value's, if it succeeded. -/
def succVal (f : A → ℝ≥0∞) : Option (Except Exhaustion A) → ℝ≥0∞
  | some (.ok a) => f a
  | _ => 0

/-- The expectation of `f` over the successes of `g`. -/
noncomputable def sexpect (g : SGen A) (f : A → ℝ≥0∞) : ℝ≥0∞ :=
  SPMF.expect g.run.run (succVal f)

/-- The probability that `g` succeeds with a value in `E`. -/
noncomputable def sprob (g : SGen A) (E : Set A) : ℝ≥0∞ :=
  sexpect g (E.indicator 1)

/-- The probability that `g` succeeds. -/
noncomputable def sok (g : SGen A) : ℝ≥0∞ := sexpect g fun _ => 1

theorem sexpect_pure (a : A) (f : A → ℝ≥0∞) : sexpect (pure a : SGen A) f = f a := by
  simp [sexpect, ExceptT.run_pure, OptionT.run_pure, SPMF.expect_pure, succVal]

theorem sexpect_bind (g : SGen A) (k : A → SGen B) (f : B → ℝ≥0∞) :
    sexpect (g >>= k) f = sexpect g fun a => sexpect (k a) f := by
  simp only [sexpect]
  rw [ExceptT.run_bind, OptionT.run_bind, Option.elimM, SPMF.expect_bind]
  congr 1
  funext o
  rcases o with _ | _ | a
  · simp [Option.elim, SPMF.expect_pure, succVal]
  · simp [Option.elim, OptionT.run_pure, SPMF.expect_pure, succVal]
  · rfl

theorem sexpect_map (g : SGen A) (h : A → B) (f : B → ℝ≥0∞) :
    sexpect (h <$> g) f = sexpect g (f ∘ h) := by
  rw [map_eq_bind_pure_comp, sexpect_bind]
  simp only [Function.comp_apply, sexpect_pure]
  rfl

@[simp] theorem sexpect_refute (f : A → ℝ≥0∞) : sexpect (Specimen.refute : SGen A) f = 0 := by
  simp [sexpect, Specimen.refute, Fail.fail, ExceptT.lift, OptionT.run_failure, SPMF.expect_pure,
    succVal]

@[simp] theorem sexpect_failWith (e : Exhaustion) (f : A → ℝ≥0∞) :
    sexpect (FailWith.failWith e : SGen A) f = 0 := by
  simp [sexpect, FailWith.failWith, OptionT.run_pure, SPMF.expect_pure, succVal]

@[simp] theorem sexpect_truncated (f : A → ℝ≥0∞) : sexpect (Specimen.truncated : SGen A) f = 0 :=
  sexpect_failWith _ f

@[simp] theorem sexpect_outOfFuel (f : A → ℝ≥0∞) : sexpect (Specimen.outOfFuel : SGen A) f = 0 :=
  sexpect_failWith _ f

@[simp] theorem sexpect_inconclusive (f : A → ℝ≥0∞) :
    sexpect (Specimen.inconclusive : SGen A) f = 0 :=
  sexpect_failWith _ f

theorem sexpect_mono (g : SGen A) {f f' : A → ℝ≥0∞} (h : ∀ a, f a ≤ f' a) :
    sexpect g f ≤ sexpect g f' :=
  SPMF.expect_mono fun o => by rcases o with _ | _ | a <;> simp [succVal, h]

/-! ## `backtrack`: a lower bound by the first draw -/

open Specimen.Backtrack

/-- What the drawn branch contributes to `F`, nothing past the total weight. -/
def drawn (F : (Unit → SGen A) → ℝ≥0∞) (o : Option (Nat × (Unit → SGen A) × List (Nat × (Unit → SGen A)))) :
    ℝ≥0∞ :=
  match o with
  | some (_, g, _) => F g
  | none => 0

/-- Over all draws below the total weight, each branch is drawn as often as its weight. -/
theorem sum_drawn_pickDrop (F : (Unit → SGen A) → ℝ≥0∞) : ∀ gs : List (Nat × (Unit → SGen A)),
    ∑ n ∈ Finset.range (sumWeights gs), drawn F (pickDrop gs n) =
      (gs.map fun p => (p.1 : ℝ≥0∞) * F p.2).sum
  | [] => by simp [sumWeights]
  | (k, g) :: rest => by
    rw [sumWeights_cons, Finset.sum_range_add]
    have h1 : ∀ n ∈ Finset.range k, drawn F (pickDrop ((k, g) :: rest) n) = F g := by
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [pickDrop, hn, drawn]
    have h2 : ∀ n, drawn F (pickDrop ((k, g) :: rest) (k + n)) = drawn F (pickDrop rest n) := by
      intro n
      simp only [pickDrop, show ¬ (k + n < k) by omega, ite_false, Nat.add_sub_cancel_left]
      cases pickDrop rest n <;> rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [h2, sum_drawn_pickDrop F rest, List.map_cons, List.sum_cons]

theorem expect_choose_down (W : Nat) (h : 0 ≤ W - 1) (F : Nat → ℝ≥0∞) :
    SPMF.expect (RandomChoice.choose 0 (W - 1) h : SPMF (ULift.{0} {x : Nat // 0 ≤ x ∧ x ≤ W - 1}))
      (fun n => F n.down.val) =
      SPMF.expect (chooseNat 0 (W - 1) h : SPMF Nat) F := by
  simp only [chooseNat, SPMF.expect_map]
  rfl

/-- The search's successes include those of the branch it draws first. -/
theorem expect_searchWith_ge (f : A → ℝ≥0∞) : ∀ (fuel : Nat) (gs : List (Nat × (Unit → SGen A)))
    (acc : Option Exhaustion), 0 < fuel → 0 < sumWeights gs →
    (gs.map fun p => (p.1 : ℝ≥0∞) * sexpect (p.2 ()) f).sum / (sumWeights gs : ℝ≥0∞) ≤
      SPMF.expect (searchWith fuel gs acc).run (succVal f)
  | 0, _, _, h, _ => absurd h (Nat.lt_irrefl _)
  | _, [], _, _, h => by simp [sumWeights] at h
  | fuel + 1, p :: gs, acc, _, hW => by
    simp only [searchWith, OptionT.run_mk]
    rw [SPMF.expect_bind]
    refine le_trans ?_ (SPMF.expect_mono (f := fun n => drawn (fun g => sexpect (g ()) f)
      (pickDrop (p :: gs) n.down.val)) fun n => ?_)
    · rw [expect_choose_down _ _ (fun m => drawn (fun g => sexpect (g ()) f) (pickDrop (p :: gs) m)),
        SPMF.expect_chooseNat_zero hW, sum_drawn_pickDrop]
    · split
      · rename_i heq
        simp only [heq, drawn]
        exact zero_le
      · rename_i g rest heq
        simp only [heq, drawn, sexpect]
        rw [SPMF.expect_bind]
        refine SPMF.expect_mono fun o => ?_
        rcases o with _ | _ | a
        · exact zero_le
        · exact zero_le
        · simp [SPMF.expect_pure, succVal]

/-- `backtrack`'s successes include those of the branch it draws first: each branch counts with its
    share of the weight. -/
theorem sexpect_backtrack_ge (gs : List (Nat × (Unit → SGen A))) (f : A → ℝ≥0∞)
    (hW : 0 < sumWeights gs) :
    (gs.map fun p => (p.1 : ℝ≥0∞) * sexpect (p.2 ()) f).sum / (sumWeights gs : ℝ≥0∞) ≤
      sexpect (Specimen.Backtrack.backtrack gs) f := by
  have hlen : 0 < gs.length := by
    cases gs with
    | nil => simp [sumWeights] at hW
    | cons => simp
  exact expect_searchWith_ge f gs.length gs none hlen hW

/-! ## Certain success -/

theorem sexpect_le_one (g : SGen A) {f : A → ℝ≥0∞} (hf : ∀ a, f a ≤ 1) : sexpect g f ≤ 1 := by
  unfold sexpect
  calc SPMF.expect g.run.run (succVal f) ≤ SPMF.expect g.run.run (fun _ => 1) :=
        SPMF.expect_mono fun o => by rcases o with _ | _ | a <;> simp [succVal, hf]
    _ = g.run.run.mass := SPMF.expect_one _
    _ ≤ 1 := SPMF.mass_le_one _

theorem sok_le_one (g : SGen A) : sok g ≤ 1 := sexpect_le_one g fun _ => le_rfl

@[simp] theorem sok_pure (a : A) : sok (pure a : SGen A) = 1 := sexpect_pure a _

theorem sok_bind_one {g : SGen A} {k : A → SGen B} (hg : sok g = 1) (hk : ∀ a, sok (k a) = 1) :
    sok (g >>= k) = 1 := by
  unfold sok at *
  rw [sexpect_bind]
  simp only [hk]
  exact hg

theorem sok_map_one {g : SGen A} (h : A → B) (hg : sok g = 1) : sok (h <$> g) = 1 := by
  unfold sok at *
  rw [sexpect_map]
  exact hg

/-- Branches that succeed surely, weighted, sum to the total weight. -/
theorem sum_weight_sok (gs : List (Nat × (Unit → SGen A))) (h : ∀ p ∈ gs, sok (p.2 ()) = 1) :
    (gs.map fun p => (p.1 : ℝ≥0∞) * sexpect (p.2 ()) (fun _ => 1)).sum = (sumWeights gs : ℝ≥0∞) := by
  induction gs with
  | nil => simp [sumWeights]
  | cons q gs ih =>
    have hq : sexpect (q.2 ()) (fun _ => 1) = 1 := h q List.mem_cons_self
    rw [List.map_cons, List.sum_cons, hq, mul_one, ih (fun p hp => h p (List.mem_cons_of_mem _ hp)),
      sumWeights_cons, Nat.cast_add]

/-- Where every branch succeeds surely, so does the search. -/
theorem sok_backtrack_one (gs : List (Nat × (Unit → SGen A))) (hW : 0 < sumWeights gs)
    (h : ∀ p ∈ gs, sok (p.2 ()) = 1) : sok (Specimen.Backtrack.backtrack gs) = 1 := by
  refine le_antisymm (sok_le_one _) ?_
  have hb := sexpect_backtrack_ge gs (fun _ => 1) hW
  rw [sum_weight_sok gs h, ENNReal.div_self (by exact_mod_cast hW.ne') (ENNReal.natCast_ne_top _)] at hb
  exact hb

end Specimen.Correctness
