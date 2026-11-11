import Batteries.Tactic.PermuteGoals
import Specimen.Correctness.CondMean
import Specimen.Correctness.SureWalk

/-! # Conditional means, by their structure

`MeanLeW g F W c`: `g`'s mean of `F` over its successes, weighted by `W`, is at most `c`. It holds of a
search when it holds of each branch, of a bind when it holds of each continuation, and of a bind
whose first part satisfies it when the continuation only scales `F` and `W` (`meanLeW_tail`).
`MeanLe` is the case `W = 1`, and a lower bound on a mean (`MeanGe`) the case with `F` and `W` swapped.
`mean_walk [facts]` applies these rules, and the facts, as far as they go. -/

namespace Specimen.Correctness
open Basalt ENNReal Specimen.Backtrack

variable {A B : Type}

/-! ## Means over a weighted event -/

/-- `g`'s mean of `F` over its successes, weighted by `W`, is at most `c`. With `W = 1`, `MeanLe`. -/
def MeanLeW (g : SGen A) (F W : A → ℝ≥0∞) (c : ℝ≥0∞) : Prop := sexpect g F ≤ c * sexpect g W

/-- Each success of the search is one of a branch's: `expect_searchWith_meanLe`, weighted. -/
theorem expect_searchWith_meanLeW (F W : A → ℝ≥0∞) (c : ℝ≥0∞) : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → SGen A))) (acc : Option Specimen.Exhaustion),
    (∀ p ∈ gs, MeanLeW (p.2 ()) F W c) →
    SPMF.expect (searchWith fuel gs acc).run (succVal F) ≤
      c * SPMF.expect (searchWith fuel gs acc).run (succVal W)
  | _, [], acc, _ => by simp only [searchWith, expect_finish_succ]; exact zero_le
  | 0, _ :: _, acc, _ => by simp only [searchWith, expect_finish_succ]; exact zero_le
  | fuel + 1, p :: gs, acc, hall => by
    simp only [searchWith, OptionT.run_mk]
    rw [SPMF.expect_bind, SPMF.expect_bind, ← SPMF.expect_mul_left]
    refine SPMF.expect_mono fun n => ?_
    split
    · simp only [expect_finish_succ]; exact zero_le
    next g rest heq =>
      have hg : MeanLeW (g ()) F W c := hall _ (pickDrop_mem heq)
      have hrest : ∀ q ∈ rest, MeanLeW (q.2 ()) F W c := fun q hq => hall q (pickDrop_rest_sub heq q hq)
      let R (F : A → ℝ≥0∞) : Option (Except Specimen.Exhaustion A) → ℝ≥0∞ := fun o => match o with
        | some (.ok _) => 0
        | some (.error e) => SPMF.expect (searchWith fuel rest (some (acc.elim e fun x => x ⊔ e))).run
            (succVal F)
        | none => SPMF.expect (searchWith fuel rest acc).run (succVal F)
      rw [SPMF.expect_bind, SPMF.expect_bind]
      refine le_of_eq_of_le (b := sexpect (g ()) F + SPMF.expect (g ()).run.run (R F)) ?_
        (le_of_le_of_eq (b := c * (sexpect (g ()) W + SPMF.expect (g ()).run.run (R W))) ?_ ?_)
      · rw [sexpect, ← SPMF.expect_add]
        congr 1; funext o
        rcases o with _ | _ | a <;> simp [R, SPMF.expect_pure, succVal]
      · rw [mul_add, ← SPMF.expect_mul_left]
        gcongr
        · exact hg
        · refine SPMF.expect_mono fun o => ?_
          rcases o with _ | _ | a
          · exact expect_searchWith_meanLeW F W c fuel rest acc hrest
          · exact expect_searchWith_meanLeW F W c fuel rest _ hrest
          · simp [R]
      · rw [sexpect, ← SPMF.expect_add]
        congr 2; funext o
        rcases o with _ | _ | a <;> simp [R, SPMF.expect_pure, succVal]


/-- **The search keeps the weighted mean.** -/
theorem meanLeW_backtrack {gs : List (Nat × (Unit → SGen A))} {F W : A → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ p ∈ gs, MeanLeW (p.2 ()) F W c) : MeanLeW (Specimen.Backtrack.backtrack gs) F W c :=
  expect_searchWith_meanLeW F W c gs.length gs none h

theorem meanLeW_bind_const {g : SGen A} {k : A → SGen B} {F W : B → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, MeanLeW (k a) F W c) : MeanLeW (g >>= k) F W c := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind, ← sexpect_mul_left]
  exact sexpect_mono g h

theorem sexpect_mono_support {g : SGen A} {f f' : A → ℝ≥0∞} (h : ∀ a, Produces g a → f a ≤ f' a) :
    sexpect g f ≤ sexpect g f' := by
  have : sexpect g f = sexpect g (fun a => min (f a) (f' a)) := by
    unfold sexpect
    exact SPMF.expect_congr_support fun o ho => by
      rcases o with _ | _ | a
      · rfl
      · rfl
      · exact (min_eq_left (h a ho)).symm
  rw [this]; exact sexpect_mono g fun a => min_le_right _ _

/-- A bind keeps the weighted mean where the continuation does on what the first part produces. -/
theorem meanLeW_bind_support {g : SGen A} {k : A → SGen B} {F W : B → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, Produces g a → MeanLeW (k a) F W c) : MeanLeW (g >>= k) F W c := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind, ← sexpect_mul_left]
  exact sexpect_mono_support h

/-- A continuation that keeps both functions, scaled alike. -/
theorem meanLeW_bind_tail {g : SGen A} {k : A → SGen B} {F W : A → ℝ≥0∞} {F' W' : B → ℝ≥0∞}
    {c q : ℝ≥0∞} (hg : MeanLeW g F W c) (hF : ∀ a, sexpect (k a) F' = q * F a)
    (hW : ∀ a, sexpect (k a) W' = q * W a) : MeanLeW (g >>= k) F' W' c := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind, sexpect_congr g hF, sexpect_congr g hW, sexpect_mul_left,
    sexpect_mul_left]
  calc q * sexpect g F ≤ q * (c * sexpect g W) := by gcongr
    _ = c * (q * sexpect g W) := by ring

theorem meanLeW_pure {a : A} {F W : A → ℝ≥0∞} {c : ℝ≥0∞} (h : F a ≤ c * W a) :
    MeanLeW (pure a : SGen A) F W c := by
  unfold MeanLeW; rw [sexpect_pure, sexpect_pure]; exact h

theorem meanLeW_of_meanLe_zero {g : SGen A} {F W : A → ℝ≥0∞} {c : ℝ≥0∞} (h : MeanLe g F 0) :
    MeanLeW g F W c := by
  unfold MeanLe MeanLeW at *; rw [zero_mul] at h; exact h.trans zero_le

theorem meanLeW_of_zero {g : SGen A} {F W : A → ℝ≥0∞} {c : ℝ≥0∞} (h : sexpect g F = 0) :
    MeanLeW g F W c := by
  unfold MeanLeW; rw [h]; exact zero_le

theorem sexpect_const' (g : SGen A) (a : ℝ≥0∞) : sexpect g (fun _ => a) = sok g * a := by
  rw [sok, mul_comm, ← sexpect_mul_left]; simp

theorem meanLeW_iff_meanLe {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} :
    MeanLeW g f (fun _ => 1) c ↔ MeanLe g f c := by
  unfold MeanLeW MeanLe; rw [sexpect_const', mul_one]

/-- **A continuation that at most scales `F` and at least scales `W`, alike.** -/
theorem meanLeW_tail {g : SGen A} {k : A → SGen B} {F W : A → ℝ≥0∞} {F' W' : B → ℝ≥0∞}
    {c c' q : ℝ≥0∞} (hg : MeanLeW g F W c) (hF : ∀ a, sexpect (k a) F' ≤ q * F a)
    (hW : ∀ a, q * W a ≤ sexpect (k a) W') (hc : c ≤ c') : MeanLeW (g >>= k) F' W' c' := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind]
  calc sexpect g (fun a => sexpect (k a) F') ≤ sexpect g (fun a => q * F a) := sexpect_mono g hF
    _ = q * sexpect g F := sexpect_mul_left _ _ _
    _ ≤ q * (c' * sexpect g W) := by gcongr; exact hg.trans (by gcongr)
    _ = c' * sexpect g (fun a => q * W a) := by rw [sexpect_mul_left]; ring
    _ ≤ _ := by gcongr; exact sexpect_mono g hW

theorem meanLeW_tail_of_meanLe {g : SGen A} {k : A → SGen B} {F : A → ℝ≥0∞} {F' W' : B → ℝ≥0∞}
    {c c' : ℝ≥0∞} (hg : MeanLe g F c) (hF : ∀ a, sexpect (k a) F' ≤ F a)
    (hW : ∀ a, 1 ≤ sexpect (k a) W') (hc : c ≤ c') : MeanLeW (g >>= k) F' W' c' :=
  meanLeW_tail (q := 1) (meanLeW_iff_meanLe.mpr hg) (by simpa using hF) (by simpa using hW) hc

/-- **A first part whose mean of a potential is at most `c₀`, then continuations, each of mean at most
the potential at its input and all with the same weight.** -/
theorem meanLeW_bind_uniform {g : SGen A} {k : A → SGen B} {F W : B → ℝ≥0∞} {c : A → ℝ≥0∞} {c₀ q : ℝ≥0∞}
    (hk : ∀ a, MeanLeW (k a) F W (c a)) (hq : ∀ a, sexpect (k a) W = q) (hg : MeanLe g c c₀) :
    MeanLeW (g >>= k) F W c₀ := by
  unfold MeanLeW MeanLe at *
  rw [sexpect_bind, sexpect_bind]
  calc sexpect g (fun a => sexpect (k a) F) ≤ sexpect g (fun a => q * c a) :=
        sexpect_mono g fun a => (hk a).trans_eq (by rw [hq, mul_comm])
    _ = q * sexpect g c := sexpect_mul_left _ _ _
    _ ≤ q * (c₀ * sok g) := by gcongr
    _ = c₀ * sexpect g (fun a => sexpect (k a) W) := by
        rw [sexpect_congr g hq, sexpect_const']; ring

/-! ### Lower bounds

A lower bound `c` on the mean of `f` is `MeanLeW g (fun _ => c) f 1`. -/

/-- Where every success is in the event, the mean is at least any `c ≤ 1`. -/
theorem meanLeW_const_of_all {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≤ 1)
    (h : ∀ a, Produces g a → 1 ≤ f a) : MeanLeW g (fun _ => c) f 1 := by
  unfold MeanLeW
  rw [sexpect_const', one_mul]
  calc sok g * c ≤ sok g * 1 := by gcongr
    _ = sexpect g (fun _ => 1) := by rw [mul_one, sok]
    _ ≤ sexpect g f := sexpect_mono_support h

theorem sok_bind_eq {g : SGen A} {k : A → SGen B} {q : ℝ≥0∞} (h : ∀ a, sok (k a) = q) :
    sok (g >>= k) = sok g * q := by
  rw [sok_bind, sexpect_congr g h, sexpect_const']

theorem sok_bind_sure {g : SGen A} {k : A → SGen B} {q : ℝ≥0∞} (hg : sok g = 1) (h : ∀ a, sok (k a) = q) :
    sok (g >>= k) = q := by
  rw [sok_bind_eq h, hg, one_mul]

/-- **A sure draw with a chance `c` of an event, then a continuation that succeeds equally often after
any draw and, after one in the event, only into `f`:** the mean of `f` is at least `c`. -/
theorem meanLeW_bind_event {g : SGen A} {k : A → SGen B} {f : B → ℝ≥0∞} {V : Set A} {c q : ℝ≥0∞}
    (hg : sok g = 1) (hV : c ≤ sprob g V) (hq : ∀ a, Produces g a → sok (k a) = q)
    (hk : ∀ a, Produces g a → a ∈ V → ∀ o, Produces (k a) o → 1 ≤ f o) :
    MeanLeW (g >>= k) (fun _ => c) f 1 := by
  unfold MeanLeW
  have hsok : sok (g >>= k) = q := by
    rw [sok_bind]
    calc sexpect g (fun a => sok (k a)) = sexpect g (fun _ => q) :=
          le_antisymm (sexpect_mono_support fun a ha => (hq a ha).le)
            (sexpect_mono_support fun a ha => (hq a ha).ge)
      _ = q := by rw [sexpect_const', hg, one_mul]
  rw [sexpect_const', hsok, one_mul, sexpect_bind]
  calc q * c ≤ q * sprob g V := by gcongr
    _ = sexpect g (fun a => V.indicator 1 a * q) := by
        unfold sprob; rw [← sexpect_mul_left]; exact sexpect_congr g fun a => mul_comm _ _
    _ ≤ sexpect g (fun a => sexpect (k a) f) := sexpect_mono_support fun a ha => by
        by_cases hv : a ∈ V
        · simp only [Set.indicator, hv, ↓reduceIte, Pi.one_apply, one_mul]
          rw [← hq a ha, sok]; exact sexpect_mono_support (hk a ha hv)
        · simp [Set.indicator, hv]

theorem meanLeW_truncations {ls : List (Specimen.Label A)} {F W : A → ℝ≥0∞} {c : ℝ≥0∞} :
    MeanLeW (Specimen.truncations ls : SGen A) F W c :=
  meanLeW_of_meanLe_zero meanLe_truncations

/-- A mean of what is constant on `g`'s successes is at most the constant. -/
theorem sexpect_le_const {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, f a = c) : sexpect g f ≤ c := by
  rw [sexpect_congr g h, sexpect_const']
  exact (mul_le_of_le_one_left zero_le (sok_add_sfail_le g |>.trans' le_self_add))

/-- …and at least it, if `g` succeeds surely. -/
theorem const_le_sexpect {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (hg : sok g = 1) (h : ∀ a, f a = c) :
    c ≤ sexpect g f := by
  rw [sexpect_congr g h, sexpect_const', hg, one_mul]

theorem sexpect_one (g : SGen A) : sexpect g (fun _ => 1) = sok g := rfl

theorem sok_map_eq (g : SGen A) (h : A → B) : sok (h <$> g) = sok g := by
  unfold sok; rw [sexpect_map]; rfl

/-- One rule of `mean_walk`. -/
syntax "mean_step" : tactic
macro_rules
  | `(tactic| mean_step) => `(tactic| first
      | with_reducible exact Specimen.Correctness.meanLeW_truncations
      | exact Specimen.Correctness.meanLeW_of_zero (Specimen.Correctness.sexpect_outOfFuel _)
      | exact Specimen.Correctness.meanLeW_of_zero (Specimen.Correctness.sexpect_inconclusive _)
      | exact Specimen.Correctness.meanLeW_of_zero (Specimen.Correctness.sexpect_refute _)
      | (with_reducible refine Specimen.Correctness.meanLeW_backtrack ?_
         simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte, Bool.or_self,
           List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.not_mem_nil,
           false_imp_iff, imp_true_iff, implies_true])
      | (apply And.intro)
      | (intro _)
      | (with_reducible refine Specimen.Correctness.meanLeW_bind_support fun _ _ => ?_)
      | (with_reducible refine Specimen.Correctness.meanLeW_pure ?_)
      | split)

/-- `mean_walk [facts]`: `MeanLeW` by the structure of the generator. A fact (`MeanLeW` or `MeanLe` of a
part) is used for a whole goal, or for the first part of a bind (`meanLeW_tail`, the continuation's
side goals left); everything else by `mean_step`. Leaves the side goals and the leaves'
inequalities. -/
syntax "mean_walk" " [" term,* "]" : tactic
macro_rules
  | `(tactic| mean_walk [$ts,*]) => do
    -- each fact elaborated once, up front, so that one that does not elaborate is an error
    let mut haves : Lean.TSyntax `tactic ← `(tactic| skip)
    let mut names : Array Lean.Ident := #[]
    for t in ts.getElems do
      let h : Lean.Ident ← Lean.Macro.withFreshMacroScope `(h)
      haves ← `(tactic| ($haves:tactic; have $h:ident := $t))
      names := names.push h
    let mut factTac : Lean.TSyntax `tactic ← `(tactic| fail "no fact")
    for h in names.reverse do
      factTac ← `(tactic| first
        | (with_reducible apply $h:ident)
        | (with_reducible apply Specimen.Correctness.meanLeW_tail_of_meanLe; (on_goal 1 => with_reducible apply $h:ident))
        | (with_reducible apply Specimen.Correctness.meanLeW_tail (q := 1); (on_goal 1 => with_reducible apply $h:ident))
        | ($factTac:tactic))
    `(tactic| ($haves:tactic; (try unfold_gen_instances); repeat' (first | ($factTac:tactic) | mean_step)))

/-- `mean_close [lemmas]`: a side goal or leaf `mean_walk` leaves: an arithmetic bound, a mean of what
is constant on the successes (with a `sok … = 1` lemma for a lower bound), or a lemma, or `simp`. -/
syntax "mean_close" " [" term,* "]" : tactic
macro_rules
  | `(tactic| mean_close [$ts,*]) => do
    let mut app : Lean.TSyntax `tactic ← `(tactic| fail "no lemma")
    for t in ts.getElems.reverse do
      app ← `(tactic| first | (with_reducible apply $t; done) | ($app:tactic))
    let simps ← ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    let simps : Lean.Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems simps
    let simpAll ← if simps.elemsAndSeps.isEmpty then `(tactic| simp [*]) else `(tactic| simp [$simps,*, *])
    let norm ← `(tactic| simp only [Specimen.Correctness.sok, Specimen.Correctness.sexpect_bind,
        Specimen.Correctness.sexpect_pure, Specimen.Correctness.sexpect_map, Function.comp_def, one_mul, zero_mul])
    `(tactic| ((try $norm:tactic); (try simp only [Specimen.Correctness.sexpect_one]); first
        | omega
        | (simp only [List.length_cons, List.length_nil]; omega)
        | exact le_rfl
        | exact Specimen.Correctness.sexpect_le_const fun _ => rfl
        | (refine Specimen.Correctness.const_le_sexpect ?_ fun _ => rfl; $app:tactic)
        | (refine le_of_eq (Eq.symm ?_); $app:tactic)
        | ($app:tactic)
        | ($simpAll:tactic; first | done | (refine Specimen.Correctness.const_le_sexpect ?_ fun _ => rfl; $app:tactic))))

end Specimen.Correctness
