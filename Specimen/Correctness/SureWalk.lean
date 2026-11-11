import Specimen.Correctness.CondMean
import Specimen.Correctness.SureLaws
import Specimen.Correctness.WalkSGenExpect
import Specimen.Enum.Laws.BacktrackWithWeight

/-! # Walking sure-success and exact bounds at `SGen`

Facts and rules for `walk` on `SPMF.expectObs` at the sampler's monad, beyond Specimen's
`WalkSGenExpect`: the fact a generator that succeeds surely gives (`le_spec_of_sok`), the upper-bound
fact any generator gives (`spec_le_sup`), an upper bound through a search whose live branches succeed
surely (`expect_backtrack_filterMap_le`), and a draw's exact average both ways. The closers settle the
arithmetic `walk` leaves. -/

namespace Specimen.Correctness
open Basalt ENNReal

/-- A generator that succeeds surely has, for every `post`, an expectation at least `post`'s least
value on a success: the law `walk` takes as a fact about it. -/
theorem le_spec_of_sok {α : Type} {g : SGen α} (h : sok g = 1)
    (post : Option (Except Specimen.Exhaustion α) → ℝ≥0∞) :
    (⨅ a, post (some (.ok a))) ≤ SPMF.expectObs.spec g post := by
  have hc : sexpect g (fun _ => ⨅ a, post (some (.ok a))) ≤ sexpect g (fun a => post (some (.ok a))) :=
    sexpect_mono g fun a => iInf_le _ a
  have hconst : sexpect g (fun _ => ⨅ a, post (some (.ok a))) = (⨅ a, post (some (.ok a))) * sok g := by
    simp only [sok, sexpect]; rw [← SPMF.expect_mul_left]; congr 1; funext o
    rcases o with _ | (e | a) <;> simp [succVal]
  rw [hconst, h, mul_one] at hc
  refine hc.trans (SPMF.expect_mono fun o => ?_)
  rcases o with _ | (e | a) <;> simp [succVal]

/-- `sok g = 1` from a lower bound of `1` on its success observation. -/
theorem sok_eq_one_of_le {α : Type} {g : SGen α}
    (h : 1 ≤ SPMF.expectObs.spec g (succVal fun _ => 1)) : sok g = 1 :=
  le_antisymm (sok_le_one g) h

/-- A weighted average of values each at least `c`, with some weight, is at least `c`. -/
theorem le_wavg {c : ℝ≥0∞} : ∀ {cs : List (Nat × ℝ≥0∞)}, (∀ p ∈ cs, 0 < p.1 → c ≤ p.2) →
    0 < (cs.map Prod.fst).sum → c ≤ (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞) := by
  intro cs h hw
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hw.ne')) (Or.inl (ENNReal.natCast_ne_top _))]
  have : ∀ cs : List (Nat × ℝ≥0∞), (∀ p ∈ cs, 0 < p.1 → c ≤ p.2) →
      c * ((cs.map Prod.fst).sum : ℝ≥0∞) ≤ (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum := by
    intro cs h
    induction cs with
    | nil => simp
    | cons p cs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add]
      refine add_le_add ?_ (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
      rcases Nat.eq_zero_or_pos p.1 with h0 | h0
      · simp [h0]
      · rw [mul_comm]; gcongr; exact h p List.mem_cons_self h0
  exact this cs h

/-- `⨅ a, post (ok a) ≤ t`, where `t` is `post` at some success, under any binders and infima. -/
syntax "inf_close" : tactic
macro_rules
  | `(tactic| inf_close) => `(tactic| first
      | exact iInf_le _ _
      | exact le_rfl
      | (intro _; inf_close)
      | (refine le_iInf fun _ => ?_; inf_close)
      | (simp_all; done))

/-- `c ≤ (w₁ * b₁ + …) / (w₁ + …)` with each `c ≤ bᵢ`: the division cleared, and term by term. -/
macro "avg_close" : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    Bool.false_eq_true, Specimen.Correctness.optW, Specimen.Correctness.succVal, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_zero, add_zero, zero_add, mul_zero]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
  try simp only [mul_add]
  repeat' apply add_le_add
  all_goals (rw [mul_comm]; first | done | (refine mul_le_mul_of_nonneg_left ?_ zero_le; inf_close))))

/-- The goals `walk` leaves on a sure-success law. -/
macro "sure_close" : tactic => `(tactic| first
  | assumption
  | (intro h; exact absurd rfl h)
  | (intro o ho; rcases o with _ | (e | a) <;> simp_all [Specimen.Correctness.succVal, Specimen.Correctness.IsFailure])
  | (simp [Specimen.Backtrack.sumWeights, Specimen.Correctness.optW]; done)
  | (avg_close; done)
  | (simp [Specimen.Correctness.succVal]; rw [ENNReal.div_self (by simp) (by simp)])
  | inf_close)

/-! ## An upper bound through a search, every live branch succeeding surely -/

/-- Branch-wise upper bounds for a guarded branch list, each live branch succeeding surely. -/
@[gen_branches]
inductive OptUpperSure {β : Type} (F : Option (Nat × (Unit → SGen β)) → ℝ≥0∞) :
    List (Nat × ℝ≥0∞) → List (Option (Nat × (Unit → SGen β))) → Prop
  | nil : OptUpperSure F [] []
  | cons {o : Option (Nat × (Unit → SGen β))} {c : ℝ≥0∞} {cs os} (h : F o ≤ c)
      (hs : ∀ q, o = some q → sok (q.2 ()) = 1) (hs' : OptUpperSure F cs os) :
      OptUpperSure F ((optW o, c) :: cs) (o :: os)

theorem OptUpperSure.weights {β : Type} {F : Option (Nat × (Unit → SGen β)) → ℝ≥0∞} {cs os}
    (h : OptUpperSure F cs os) :
    (cs.map Prod.fst).sum = ((os.filterMap fun o => o).map Prod.fst).sum := by
  induction h with
  | nil => rfl
  | @cons o _ _ _ _ _ _ ih => cases o <;> simp_all [optW]

theorem OptUpperSure.sure {β : Type} {F : Option (Nat × (Unit → SGen β)) → ℝ≥0∞} {cs os}
    (h : OptUpperSure F cs os) : ∀ p ∈ os.filterMap (fun o => o), sok (p.2 ()) = 1 := by
  induction h with
  | nil => simp
  | @cons o _ _ _ _ hs _ ih =>
    intro p hp
    cases o with
    | none => exact ih p (by simpa using hp)
    | some q =>
      simp only [List.filterMap_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hs _ rfl
      · exact ih p hp

theorem OptUpperSure.sum_le {β : Type} {post : Option (Except Specimen.Exhaustion β) → ℝ≥0∞} {cs os}
    (h : OptUpperSure (fun o => SPMF.expectObs.spec (optGen o : SGen β) post) cs os) :
    ((os.filterMap fun o => o).map fun p => (p.1 : ℝ≥0∞) * SPMF.expectObs.spec (p.2 () : SGen β) post).sum ≤
      (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum := by
  induction h with
  | nil => simp
  | @cons o _ _ _ hc _ _ ih =>
    cases o with
    | none => simpa [optW] using ih
    | some q =>
      simp only [List.filterMap_cons, List.map_cons, List.sum_cons, optW]
      exact add_le_add (mul_le_mul_of_nonneg_left hc zero_le) ih

@[gen_rule]
theorem expect_optGen_some_le {β : Type} {q : Nat × (Unit → SGen β)}
    {post : Option (Except Specimen.Exhaustion β) → ℝ≥0∞} {c : ℝ≥0∞}
    (h : SPMF.expectObs.spec (q.2 () : SGen β) post ≤ c) :
    SPMF.expectObs.spec (optGen (some q) : SGen β) post ≤ c := h

/-- A dropped branch has weight `0`, so its bound does not matter. -/
@[gen_rule]
theorem expect_optGen_ite_le {b : Prop} [Decidable b] {β : Type} {q : Nat × (Unit → SGen β)}
    {post : Option (Except Specimen.Exhaustion β) → ℝ≥0∞} {c : ℝ≥0∞}
    (h : b → SPMF.expectObs.spec (q.2 () : SGen β) post ≤ c) :
    SPMF.expectObs.spec (optGen (if b then some q else none) : SGen β) post ≤
      (if b then c else SPMF.expectObs.spec (Specimen.refute : SGen β) post) := by
  by_cases hb : b
  · simp only [hb, ite_true, optGen]; exact h hb
  · simp only [hb, ite_false, optGen]; exact le_rfl

/-! Failures: `post` at the outcome. -/

@[gen_rule]
theorem expect_fail_le {β : Type} {post : Option (Except Specimen.Exhaustion β) → ℝ≥0∞} :
    SPMF.expectObs.spec (Specimen.Fail.fail : SGen β) post ≤ post none := spec_fail.le

@[gen_rule]
theorem expect_failWith_le {β : Type} {e : Specimen.Exhaustion}
    {post : Option (Except Specimen.Exhaustion β) → ℝ≥0∞} :
    SPMF.expectObs.spec (Specimen.FailWith.failWith e : SGen β) post ≤ post (some (.error e)) :=
  spec_failWith.le

/-! A draw at `SGen`: the uniform average over its range, as an upper and a lower rule. -/

/-- `chooseNat` never fails, so its expectation of any `post` is the average over its successes. -/
theorem spec_chooseNat_any {lo hi : Nat} {h : lo ≤ hi} (post : Option (Except Specimen.Exhaustion Nat) → ℝ≥0∞) :
    SPMF.expectObs.spec (chooseNat lo hi h : SGen Nat) post =
      sexpect (chooseNat lo hi h : SGen Nat) (fun x => post (some (.ok x))) := by
  show SPMF.expect (chooseNat lo hi h : SGen Nat).run.run post = SPMF.expect (chooseNat lo hi h : SGen Nat).run.run (succVal _)
  have hc : (RandomChoice.choose lo hi h : SGen _) = ExceptT.lift (OptionT.lift (RandomChoice.choose lo hi h : SPMF _)) := rfl
  rw [chooseNat, hc, ExceptT.run_map, ExceptT.run_lift, OptionT.run_map, OptionT.run_map, OptionT.run_lift]
  simp only [SPMF.expect_map, Function.comp_def, succVal]
  rw [SPMF.expect_bind, SPMF.expect_bind]
  simp only [SPMF.expect_pure, Option.map_some, Except.map]

@[gen_rule]
theorem expect_chooseNat_le {lo hi : Nat} {h : lo ≤ hi}
    {post : Option (Except Specimen.Exhaustion Nat) → ℝ≥0∞} :
    SPMF.expectObs.spec (chooseNat lo hi h : SGen Nat) post ≤
      (∑ x ∈ Finset.Icc lo hi, post (some (.ok x))) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  rw [spec_chooseNat_any, sexpect_chooseNat]

@[gen_rule]
theorem le_expect_chooseNat {lo hi : Nat} {h : lo ≤ hi}
    {post : Option (Except Specimen.Exhaustion Nat) → ℝ≥0∞} :
    (∑ x ∈ Finset.Icc lo hi, post (some (.ok x))) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) ≤
      SPMF.expectObs.spec (chooseNat lo hi h : SGen Nat) post := by
  rw [spec_chooseNat_any, sexpect_chooseNat]

/-- `backtrack` over the emitter's guarded branch list, every live branch succeeding surely, is at most
the average of its branches' bounds: it never retries. -/
@[gen_rule]
theorem expect_backtrack_filterMap_le {β : Type} {os : List (Option (Nat × (Unit → SGen β)))}
    {post : Option (Except Specimen.Exhaustion β) → ℝ≥0∞} {cs : List (Nat × ℝ≥0∞)}
    (h : OptUpperSure (fun o => SPMF.expectObs.spec (optGen o : SGen β) post) cs os)
    (hpost : SuccOnly post) (hW : 0 < Specimen.Backtrack.sumWeights (os.filterMap fun o => o)) :
    SPMF.expectObs.spec (Specimen.Backtrack.backtrack (os.filterMap fun o => o) : SGen β) post ≤
      (cs.map fun p => (p.1 : ℝ≥0∞) * p.2).sum / ((cs.map Prod.fst).sum : ℝ≥0∞) := by
  rw [expect_eq_sexpect hpost, sexpect_backtrack_eq _ _ hW h.sure, h.weights]
  simp only [Specimen.Backtrack.sumWeights]
  gcongr
  refine le_trans (le_of_eq ?_) h.sum_le
  congr 1
  exact List.map_congr_left fun p _ => by rw [expect_eq_sexpect hpost]

@[simp] theorem spec_refute_succVal {β : Type} (f : β → ℝ≥0∞) :
    SPMF.expectObs.spec (Specimen.refute : SGen β) (succVal f) = 0 := sexpect_refute f

/-- An expectation is at most `post`'s supremum over the outcomes, split by kind so that each part
is `post` at a constructor: the upper-bound fact `walk` takes about any generator. -/
theorem spec_le_sup {β : Type} (g : SGen β) (post : Option (Except Specimen.Exhaustion β) → ℝ≥0∞) :
    SPMF.expectObs.spec g post ≤
      (⨆ a, post (some (.ok a))) ⊔ (post none ⊔ ⨆ e, post (some (.error e))) := by
  show SPMF.expect g.run.run post ≤ _
  calc SPMF.expect g.run.run post
      ≤ SPMF.expect g.run.run (fun _ => (⨆ a, post (some (.ok a))) ⊔ (post none ⊔ ⨆ e, post (some (.error e)))) :=
        SPMF.expect_mono fun o => by
          rcases o with _ | (e | a)
          · exact le_sup_of_le_right (le_sup_left)
          · exact le_sup_of_le_right (le_sup_of_le_right (le_iSup (fun e => post (some (.error e))) e))
          · exact le_sup_of_le_left (le_iSup (fun a => post (some (.ok a))) a)
    _ = _ * g.run.run.mass := by rw [SPMF.expect_const, mul_comm]
    _ ≤ _ := by
        calc _ ≤ ((⨆ a, post (some (.ok a))) ⊔ (post none ⊔ ⨆ e, post (some (.error e)))) * 1 := by
              gcongr; exact SPMF.mass_le_one _
          _ = _ := mul_one _

/-- `sok g = 1` for a live branch: `pure`, binds and maps of what succeeds surely. -/
macro "sok_close" : tactic => `(tactic| (
  intros
  simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  subst_vars
  solve_by_elim (maxDepth := 12) [Specimen.Correctness.sok_pure, Specimen.Correctness.sok_bind_one,
    Specimen.Correctness.sok_map_one]))

/-- An exact bound, evaluated: weights, guards, indicators and failures to numerals. -/
macro "num_close" : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, Bool.false_eq_true,
    Specimen.Correctness.optW, Specimen.Correctness.succVal, Specimen.Correctness.spec_refute_succVal, Set.indicator,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, Pi.one_apply, reduceCtorEq, not_false_eq_true,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, add_zero, zero_add, mul_zero, mul_one,
    List.length_nil, pow_zero]
  first
    | (rw [ENNReal.div_self (by norm_num) (by norm_num)])
    | norm_num))

/-! ## Mass

`Tot g`: `g` succeeds or fails surely. `tot_walk` proves it by `walk` on the constant post `1`;
`sok_walk` proves `sok g = 1` by `walk` on a success-only post. A search that `walk` averages over
its first try is handled by `tot_search` (every branch total) and `sok_search` (one branch sure). -/

section Mass
variable {A B : Type}

theorem sexpect_add (g : SGen A) (f h : A → ENNReal) :
    sexpect g (fun a => f a + h a) = sexpect g f + sexpect g h := by
  unfold sexpect
  rw [show succVal (fun a => f a + h a) = fun o => succVal f o + succVal h o from
    funext fun o => by rcases o with _ | _ | a <;> simp [succVal], SPMF.expect_add]

theorem sexpect_zero (g : SGen A) : sexpect g (fun _ => 0) = 0 := by
  simpa using sexpect_mul_left g 0 (fun _ => 1)

theorem sexpect_list_sum {ι : Type} (l : List ι) (g : SGen A) (F : ι → A → ℝ≥0∞) :
    sexpect g (fun a => (l.map (F · a)).sum) = (l.map fun i => sexpect g (F i)).sum := by
  induction l with
  | nil => simpa using sexpect_zero g
  | cons i l ih => simp only [List.map_cons, List.sum_cons]; rw [sexpect_add, ih]

/-- `g` loses no mass: it succeeds or fails, surely. -/
abbrev Tot (g : SGen A) : Prop := sok g + sfail g = 1

theorem tot_eq_mass (g : SGen A) : sok g + sfail g = g.run.run.mass := by
  unfold sok sexpect sfail
  rw [← SPMF.expect_add]
  calc _ = SPMF.expect g.run.run (fun _ => 1) := by
        congr 1; funext o; rcases o with _ | _ | a <;> simp [succVal, failVal]
    _ = g.run.run.mass := SPMF.expect_one _

theorem tot_backtrack {gs : List (Nat × (Unit → SGen A))} (h : ∀ p ∈ gs, Tot (p.2 ())) :
    Tot (Specimen.Backtrack.backtrack gs) := by
  unfold Tot; rw [tot_eq_mass]
  exact Specimen.Backtrack.mass_searchWith gs.length gs none fun p hp _ => by
    rw [← tot_eq_mass]; exact h p hp

theorem tot_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen A)))}
    (h : ∀ q ∈ os, ∀ p, q = some p → Tot (p.2 ())) :
    Tot (Specimen.Backtrack.backtrack (os.filterMap fun o => o)) :=
  tot_backtrack fun p hp => by
    obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp hp
    exact h q hq p hqp

theorem tot_pure (a : A) : Tot (pure a : SGen A) := total_of_sok (sok_pure a)
theorem tot_bind {g : SGen A} {k : A → SGen B} (hg : Tot g) (hk : ∀ a, Tot (k a)) : Tot (g >>= k) := by
  unfold Tot at *
  rw [sok_bind, sfail_bind, add_comm (sfail g), ← add_assoc, ← sexpect_add]
  simp only [hk]
  exact hg
theorem tot_refute : Tot (Specimen.refute : SGen A) := by
  simp [Tot, sok, sfail, sexpect, Specimen.Fail.fail, Specimen.refute, ExceptT.lift, OptionT.run_failure,
    SPMF.expect_pure, failVal, succVal]
theorem tot_fail : Tot (Specimen.Fail.fail : SGen A) := tot_refute
theorem tot_failWith (e : Specimen.Exhaustion) : Tot (Specimen.FailWith.failWith e : SGen A) := total_failWith e
theorem tot_truncations (ls : List (Specimen.Label A)) : Tot (Specimen.truncations ls : SGen A) := total_truncations ls
theorem tot_outOfFuel : Tot (Specimen.outOfFuel : SGen A) := total_failWith _
theorem tot_inconclusive : Tot (Specimen.inconclusive : SGen A) := total_failWith _
theorem tot_of_sok {g : SGen A} (h : sok g = 1) : Tot g := total_of_sok h


/-- A total generator's expectation of any `post` is at least `post`'s least value. -/
theorem le_spec_of_tot {α : Type} {g : SGen α} (h : Tot g)
    (post : Option (Except Specimen.Exhaustion α) → ℝ≥0∞) : (⨅ o, post o) ≤ SPMF.expectObs.spec g post := by
  show _ ≤ SPMF.expect g.run.run post
  have hm : g.run.run.mass = 1 := by rw [← tot_eq_mass]; exact h
  calc (⨅ o, post o) = (⨅ o, post o) * g.run.run.mass := by rw [hm, mul_one]
    _ = SPMF.expect g.run.run (fun _ => ⨅ o, post o) := by rw [SPMF.expect_const, mul_comm]
    _ ≤ _ := SPMF.expect_mono fun o => iInf_le post o

theorem tot_of_le {α : Type} {g : SGen α} (h : 1 ≤ SPMF.expectObs.spec g fun _ => 1) : Tot g := by
  unfold Tot; rw [tot_eq_mass]
  exact le_antisymm (SPMF.mass_le_one _) (h.trans_eq (SPMF.expect_one _))

/-- `1 ≤ b`, `b` a bound `walk` computed for the mass: infima over outcomes, each case `1`. -/
syntax "mass_close" : tactic
macro_rules
  | `(tactic| mass_close) => `(tactic| first
      | exact le_rfl
      | (simp only [iInf_const, le_refl]; done)
      | (refine le_iInf fun o => ?_; rcases o with _ | (_ | _) <;> (try simp only) <;> mass_close)
      | (split_ifs <;> mass_close)
      | (rw [ENNReal.div_self (by simp) (by simp)])
      | (simp; done)
      | (simp [Specimen.Correctness.succVal]; rw [ENNReal.div_self (by simp) (by simp)])
      | (simp; split_ifs <;> mass_close))

open Lean Elab Term Meta in
/-- For `e : ∀ xs, P (g xs)`, the walk fact `fun xs => law (e xs)`, its statement with the abbreviations
it names unfolded: `walk` matches a fact by the constants it mentions, and the derived code names the
worker itself. -/
def mkWalkFact (law : Option Lean.Name) (e : Lean.Expr) : MetaM Lean.Expr := do
  forallTelescopeReducing (← inferType e) fun xs _ => do
    let body ← match law with
      | some law => mkAppM law #[mkAppN e xs]
      | none => pure (mkAppN e xs)
    let ty ← Meta.transform (← inferType body) (pre := fun t => do
      -- a derived instance, as `unfold_gen_instances` opens it: to the worker it runs
      if t.isAppOf ``BacktrackGenFor.gen || t.isAppOf ``EnumFor.enum then
        if let some t' ← unfoldProjInst? t then
          let t' := t'.headBeta
          if let some n := t'.getAppFn.constName? then
            if Specimen.isDerivedWorker (← getEnv) n [.Generator, .Enumerator] then
              return .visit t'
      if let some c := t.getAppFn.constName? then
        if (← getReducibilityStatus c) == .reducible && !(← isProp t) then
          if let some t' ← unfoldDefinition? t then return .visit t'.headBeta
      return .continue)
    mkLambdaFVars xs (← mkExpectedTypeHint body ty)

open Lean Elab Term Meta in
/-- `unfold_fact% e`: `e`, its statement about derived instances restated about the workers they run, as
`unfold_gen_instances` opens them. -/
elab "unfold_fact% " e:term:max : term => do mkWalkFact none (← elabTerm e none)

open Lean Elab Term Meta in
/-- `tot_fact% e`: for `e : ∀ xs, Tot (g xs)`, the walk fact `⨅ o, post o ≤ spec (g xs) post`. -/
elab "tot_fact% " e:term:max : term => do mkWalkFact (some ``le_spec_of_tot) (← elabTerm e none)

open Lean Elab Term Meta in
/-- `sok_fact% e`: for `e : ∀ xs, sok (g xs) = 1`, the walk fact `⨅ a, post (ok a) ≤ spec (g xs) post`. -/
elab "sok_fact% " e:term:max : term => do mkWalkFact (some ``le_spec_of_sok) (← elabTerm e none)

/-- A branch is total: its mass by `walk`, with `facts` about what it calls. -/
macro "tot_walk" " [" ts:term,* "]" : tactic => `(tactic| (apply tot_of_le; (try unfold_gen_instances); walk [$ts,*]; all_goals mass_close))

/-- `g` succeeds surely: a lower bound by `walk`, with `facts` about what it calls. -/
macro "sok_walk" " [" ts:term,* "]" : tactic => `(tactic| (apply sok_eq_one_of_le; (try unfold_gen_instances); walk [$ts,*]; all_goals sure_close))

/-- A derived worker's search at `fuel + 1` is total: every live branch by `tot_walk`. -/
macro "tot_search" " [" ts:term,* "]" : tactic => `(tactic| (
  simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte, Bool.or_self]
  refine tot_backtrack ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.not_mem_nil,
    false_imp_iff, imp_true_iff, implies_true]
  repeat' apply And.intro
  all_goals tot_walk [$ts,*]))

theorem exists_mem_cons_of_tail {α : Type} {a : α} {l : List α} {q : α → Prop} (h : ∃ p ∈ l, q p) :
    ∃ p ∈ a :: l, q p :=
  let ⟨p, hp, hq⟩ := h; ⟨p, List.mem_cons_of_mem _ hp, hq⟩

/-- One branch of a search succeeds surely: the first that `sok_walk` proves. -/
syntax "sure_branch" " [" term,* "]" : tactic
macro_rules
  | `(tactic| sure_branch [$ts,*]) => `(tactic| first
      | (refine ⟨_, List.mem_cons_self, by norm_num, ?_⟩; sok_walk [$ts,*]; done)
      | (refine exists_mem_cons_of_tail ?_; sure_branch [$ts,*]))

/-- A derived worker's search at `fuel + 1` succeeds surely: its branches are total (`tot`), and one
of them succeeds surely (by `sure` and `tot`). -/
syntax "sok_search" " [" term,* "]" (&" sure" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| sok_search [$ts,*] $[sure [$ss,*]]?) => do
    let all : Lean.Syntax.TSepArray `term "," := .ofElems ((ss.map (·.getElems)).getD #[] ++ ts.getElems)
    `(tactic| (
      try simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte, Bool.or_self]
      refine sok_backtrack_of_sure ?_ ?_
      · try simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.not_mem_nil,
          false_imp_iff, imp_true_iff, implies_true]
        repeat' apply And.intro
        all_goals tot_walk [$ts,*]
      · sure_branch [$all,*]))

end Mass

end Specimen.Correctness
