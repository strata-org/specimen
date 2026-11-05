import Specimen.Correctness.WalkSGen
import Specimen.Correctness.GenExpectSPMF
import Basalt.Walk.Average

/-!
# Teaching Basalt's walk the expectation of a search

`SPMF.expectObs.spec g post` is `g`'s expectation of `post` over its outcomes. Where `post` counts only
successes (it is `0` on a refutation and on a labelled failure), `backtrack` is at least its first
draw: whichever branch is drawn, its successes are the search's, and a retry after it fails only adds
(`sexpect_backtrack_ge`). These are the lower-bound rules that turn into, for the literal branch list
and for the emitter's guarded one, and for the failures, which contribute `post`'s value at them.
-/

open Basalt Basalt.Walk ENNReal

namespace Specimen.Correctness

variable {α : Type}

/-- `post` counts only successes. -/
def SuccOnly (post : Option (Except Exhaustion α) → ℝ≥0∞) : Prop := ∀ o, IsFailure o → post o = 0

theorem post_eq_succVal {post : Option (Except Exhaustion α) → ℝ≥0∞} (h : SuccOnly post) :
    post = succVal (fun a => post (some (.ok a))) := by
  funext o
  rcases o with _ | (e | a)
  · exact h none fun x hx => nomatch hx
  · exact h _ fun x hx => nomatch hx
  · rfl

theorem expect_eq_sexpect {g : SGen α} {post : Option (Except Exhaustion α) → ℝ≥0∞}
    (h : SuccOnly post) :
    SPMF.expectObs.spec (g : SGen α) post = sexpect g (fun a => post (some (.ok a))) := by
  show SPMF.expect g.run.run post = SPMF.expect g.run.run _
  rw [← post_eq_succVal h]

theorem weighted_sum_le {gs : List (Nat × (Unit → SGen α))} {F : (Unit → SGen α) → ℝ≥0∞}
    {cs : List (Nat × ℝ≥0∞)} (h : Mix.Weighted (· ≥ ·) F cs gs) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum ≤ (gs.map fun p => (p.1 : ℝ≥0∞) * F p.2).sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simp only [List.map_cons, List.sum_cons]; gcongr

/-! ## The emitter's guarded branch list -/

/-- A guarded branch's weight: its own, or `0` where the guard dropped it. -/
def optW {β : Type} : Option (Nat × β) → Nat
  | some q => q.1
  | none => 0

/-- Branch-wise lower bounds for a guarded branch list, each with the branch's weight. -/
@[gen_branches]
inductive OptWeighted {β : Type} (F : Option (Nat × β) → ℝ≥0∞) :
    List (Nat × ℝ≥0∞) → List (Option (Nat × β)) → Prop
  | nil : OptWeighted F [] []
  | cons {o : Option (Nat × β)} {c : ℝ≥0∞} {cs os} (h : c ≤ F o) (hs : OptWeighted F cs os) :
      OptWeighted F ((optW o, c) :: cs) (o :: os)

theorem optWeighted_weights {β : Type} {F : Option (Nat × β) → ℝ≥0∞} {cs os}
    (h : OptWeighted F cs os) :
    (cs.map Prod.fst).sum = ((os.filterMap fun o => o).map Prod.fst).sum := by
  induction h with
  | nil => rfl
  | @cons o _ _ _ _ _ ih => cases o <;> simp_all [optW]

theorem optWeighted_sum_le {os : List (Option (Nat × (Unit → SGen α)))}
    {post : Option (Except Exhaustion α) → ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)}
    (h : OptWeighted (fun o => SPMF.expectObs.spec (optGen o : SGen α) post) cs os) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum ≤
      ((os.filterMap fun o => o).map fun p =>
        (p.1 : ℝ≥0∞) * SPMF.expectObs.spec (p.2 () : SGen α) post).sum := by
  induction h with
  | nil => simp
  | @cons o _ _ _ hc _ ih =>
    cases o with
    | none => simpa [optW] using ih
    | some q =>
      simp only [List.filterMap_cons, List.map_cons, List.sum_cons, optW]
      gcongr
      exact hc

/-- `backtrack` over the emitter's guarded branch list is at least its first draw. -/
@[gen_rule]
theorem le_expect_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen α)))}
    {post : Option (Except Exhaustion α) → ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)}
    (h : OptWeighted (fun o => SPMF.expectObs.spec (optGen o : SGen α) post) cs os)
    (hpost : SuccOnly post) (hW : 0 < Backtrack.sumWeights (os.filterMap fun o => o)) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞) ≤
      SPMF.expectObs.spec
        (Specimen.Backtrack.backtrack (os.filterMap fun o => o) : SGen α) post := by
  rw [expect_eq_sexpect hpost, optWeighted_weights h]
  refine le_trans ?_ (sexpect_backtrack_ge _ _ hW)
  simp only [Backtrack.sumWeights]
  gcongr
  refine (optWeighted_sum_le h).trans (le_of_eq ?_)
  congr 1
  exact List.map_congr_left fun p _ => by rw [expect_eq_sexpect hpost]

/-- `backtrack` over a literal branch list is at least its first draw. -/
@[gen_rule]
theorem le_expect_backtrack {gs : List (Nat × (Unit → SGen α))}
    {post : Option (Except Exhaustion α) → ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)}
    (h : Mix.Weighted (· ≥ ·) (fun g => SPMF.expectObs.spec (g () : SGen α) post) cs gs)
    (hpost : SuccOnly post) (hW : 0 < Backtrack.sumWeights gs) :
    (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞) ≤
      SPMF.expectObs.spec (Specimen.Backtrack.backtrack gs : SGen α) post := by
  rw [expect_eq_sexpect hpost, h.weights]
  refine le_trans ?_ (sexpect_backtrack_ge gs _ hW)
  simp only [Backtrack.sumWeights]
  gcongr
  refine (weighted_sum_le h).trans (le_of_eq ?_)
  congr 1
  exact List.map_congr_left fun p _ => by rw [expect_eq_sexpect hpost]

@[gen_rule]
theorem le_expect_optGen_some {q : Nat × (Unit → SGen α)}
    {post : Option (Except Exhaustion α) → ℝ≥0∞} {c : ℝ≥0∞}
    (h : c ≤ SPMF.expectObs.spec (q.2 () : SGen α) post) :
    c ≤ SPMF.expectObs.spec (optGen (some q) : SGen α) post := h

/-- A dropped branch has weight `0`, so its bound does not matter. -/
@[gen_rule]
theorem le_expect_optGen_ite {b : Prop} [Decidable b] {q : Nat × (Unit → SGen α)}
    {post : Option (Except Exhaustion α) → ℝ≥0∞} {c : ℝ≥0∞}
    (h : b → c ≤ SPMF.expectObs.spec (q.2 () : SGen α) post) :
    (if b then c else 0) ≤ SPMF.expectObs.spec (optGen (if b then some q else none) : SGen α) post := by
  by_cases hb : b
  · simp only [hb, ite_true, optGen]; exact h hb
  · simp only [hb, ite_false]; exact zero_le

/-! ## Failures -/

@[gen_rule]
theorem le_expect_fail {post : Option (Except Exhaustion α) → ℝ≥0∞} :
    (0 : ℝ≥0∞) ≤ SPMF.expectObs.spec (Specimen.Fail.fail : SGen α) post := zero_le

@[gen_rule]
theorem le_expect_failWith {e : Exhaustion} {post : Option (Except Exhaustion α) → ℝ≥0∞} :
    (0 : ℝ≥0∞) ≤ SPMF.expectObs.spec (Specimen.FailWith.failWith e : SGen α) post := zero_le

@[gen_rule]
theorem le_expect_truncations {ls : List (Specimen.Label α)}
    {post : Option (Except Exhaustion α) → ℝ≥0∞} :
    (0 : ℝ≥0∞) ≤ SPMF.expectObs.spec (Specimen.truncations ls : SGen α) post := zero_le

end Specimen.Correctness
