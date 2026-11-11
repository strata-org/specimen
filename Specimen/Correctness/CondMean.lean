import Specimen.Correctness.GenExpectSPMF

/-!
# Upper bounds through a search

An upper bound on `sexpect g f` does not survive `backtrack`: a branch that fails is retried, and the
retry's successes add to the first draw's. What survives is a bound on the mean over successes,
`MeanLe g f c : sexpect g f ≤ c * sok g`. Each success of the search is a success of one branch, run
afresh, so where every branch's mean is at most `c`, so is the search's (`meanLe_backtrack`), whatever
the branches' chances of failing.

A bind keeps the mean where the continuation's bound is one constant (`meanLe_bind_const`). Where the
bound depends on the drawn value, the continuation's chance of success must not: otherwise the
successes over-sample the values it succeeds on, and the mean of the bound is the wrong one
(`meanLe_bind_uniform`). That chance, for a whole derived generator, is had by its outcome profile
(`sok`, `sfail`), which binds and searches compute from their parts' (`profile_backtrack_congr`).
-/

open ENNReal

namespace Specimen.Correctness

open Specimen.Backtrack

variable {A B C : Type}

/-- `g`'s mean of `f` over its successes is at most `c`. -/
def MeanLe (g : SGen A) (f : A → ℝ≥0∞) (c : ℝ≥0∞) : Prop := sexpect g f ≤ c * sok g

theorem succVal_mul (c : ℝ≥0∞) (f : A → ℝ≥0∞) (o : Option (Except Exhaustion A)) :
    succVal (fun a => c * f a) o = c * succVal f o := by
  rcases o with _ | _ | a <;> simp [succVal]

theorem sexpect_mul_left (g : SGen A) (c : ℝ≥0∞) (f : A → ℝ≥0∞) :
    sexpect g (fun a => c * f a) = c * sexpect g f := by
  unfold sexpect
  rw [show succVal (fun a => c * f a) = fun o => c * succVal f o from funext (succVal_mul c f),
    SPMF.expect_mul_left]

theorem sexpect_congr (g : SGen A) {f f' : A → ℝ≥0∞} (h : ∀ a, f a = f' a) :
    sexpect g f = sexpect g f' := congrArg _ (funext h)

/-! ## Failures -/

/-- What a run's outcome contributes to its chance of failing. -/
def failVal : Option (Except Exhaustion A) → ℝ≥0∞
  | some (.ok _) => 0
  | _ => 1

/-- The probability that `g` fails, with a refutation or a label. -/
noncomputable def sfail (g : SGen A) : ℝ≥0∞ := SPMF.expect g.run.run failVal

/-! ## The search -/

theorem expect_finish_succ (acc : Option Exhaustion) (f : A → ℝ≥0∞) :
    SPMF.expect (Backtrack.finish acc : OptionT SPMF (Except Exhaustion A)).run (succVal f) = 0 := by
  cases acc <;> simp [Backtrack.finish, OptionT.run_failure, SPMF.expect_pure, succVal]

theorem pickDrop_rest_sub {β : Type} : ∀ {gs : List (Nat × β)} {n k b rest},
    pickDrop gs n = some (k, b, rest) → ∀ p ∈ rest, p ∈ gs
  | [], _, _, _, _, h => by simp [pickDrop] at h
  | (k', b') :: gs, n, k, b, rest, h => by
    simp only [pickDrop] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact fun p hp => List.mem_cons_of_mem _ hp
    · cases hp : pickDrop gs (n - k') with
      | none => simp [hp] at h
      | some t =>
        obtain ⟨k₀, b₀, r₀⟩ := t
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        intro p hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (pickDrop_rest_sub hp p hp')

/-- Each success of the search is one of a branch's: where every branch's mean is at most `c`, so is
the search's. -/
theorem expect_searchWith_meanLe (f : A → ℝ≥0∞) (c : ℝ≥0∞) : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → SGen A))) (acc : Option Exhaustion),
    (∀ p ∈ gs, MeanLe (p.2 ()) f c) →
    SPMF.expect (searchWith fuel gs acc).run (succVal f) ≤
      c * SPMF.expect (searchWith fuel gs acc).run (succVal fun _ => 1)
  | _, [], acc, _ => by simp only [searchWith, expect_finish_succ]; exact zero_le
  | 0, _ :: _, acc, _ => by simp only [searchWith, expect_finish_succ]; exact zero_le
  | fuel + 1, p :: gs, acc, hall => by
    simp only [searchWith, OptionT.run_mk]
    rw [SPMF.expect_bind, SPMF.expect_bind, ← SPMF.expect_mul_left]
    refine SPMF.expect_mono fun n => ?_
    split
    · simp only [expect_finish_succ]; exact zero_le
    · rename_i g rest heq
      have hg : MeanLe (g ()) f c := hall _ (pickDrop_mem heq)
      have hrest : ∀ q ∈ rest, MeanLe (q.2 ()) f c := fun q hq => hall q (pickDrop_rest_sub heq q hq)
      -- The search's value past the first draw, at each outcome of it.
      let R (F : A → ℝ≥0∞) : Option (Except Exhaustion A) → ℝ≥0∞ := fun o => match o with
        | some (.ok _) => 0
        | some (.error e) => SPMF.expect (searchWith fuel rest (some (acc.elim e fun x => x ⊔ e))).run
            (succVal F)
        | none => SPMF.expect (searchWith fuel rest acc).run (succVal F)
      rw [SPMF.expect_bind, SPMF.expect_bind]
      refine le_of_eq_of_le (b := sexpect (g ()) f + SPMF.expect (g ()).run.run (R f)) ?_
        (le_of_le_of_eq (b := c * (sok (g ()) + SPMF.expect (g ()).run.run (R fun _ => 1))) ?_ ?_)
      · rw [sexpect, ← SPMF.expect_add]
        congr 1; funext o
        rcases o with _ | _ | a <;> simp [R, SPMF.expect_pure, succVal]
      · rw [mul_add, ← SPMF.expect_mul_left]
        gcongr
        · exact hg
        · refine SPMF.expect_mono fun o => ?_
          rcases o with _ | _ | a
          · exact expect_searchWith_meanLe f c fuel rest acc hrest
          · exact expect_searchWith_meanLe f c fuel rest _ hrest
          · simp [R]
      · rw [sok, sexpect, ← SPMF.expect_add]
        congr 2; funext o
        rcases o with _ | _ | a <;> simp [R, SPMF.expect_pure, succVal]

/-- **The search keeps the mean.** Where every branch's mean over its successes is at most `c`, so is
`backtrack`'s, however often the branches fail. -/
theorem meanLe_backtrack {gs : List (Nat × (Unit → SGen A))} {f : A → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ p ∈ gs, MeanLe (p.2 ()) f c) : MeanLe (Specimen.Backtrack.backtrack gs) f c :=
  expect_searchWith_meanLe f c gs.length gs none h

theorem meanLe_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen A)))} {f : A → ℝ≥0∞}
    {c : ℝ≥0∞} (h : ∀ q ∈ os, ∀ p, q = some p → MeanLe (p.2 ()) f c) :
    MeanLe (Specimen.Backtrack.backtrack (os.filterMap fun o => o)) f c :=
  meanLe_backtrack fun p hp => by
    obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp hp
    exact h q hq p hqp

/-! ## The other combinators -/

theorem meanLe_mono {g : SGen A} {f : A → ℝ≥0∞} {c c' : ℝ≥0∞} (hc : c ≤ c') (h : MeanLe g f c) :
    MeanLe g f c' := h.trans (by gcongr)

theorem meanLe_pure {a : A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (h : f a ≤ c) : MeanLe (pure a : SGen A) f c := by
  unfold MeanLe sok; rw [sexpect_pure, sexpect_pure, mul_one]; exact h

theorem meanLe_refute {f : A → ℝ≥0∞} {c : ℝ≥0∞} : MeanLe (Specimen.refute : SGen A) f c := by
  unfold MeanLe; rw [sexpect_refute]; exact zero_le

theorem meanLe_fail {f : A → ℝ≥0∞} {c : ℝ≥0∞} : MeanLe (Specimen.Fail.fail : SGen A) f c :=
  meanLe_refute

theorem meanLe_failWith {e : Exhaustion} {f : A → ℝ≥0∞} {c : ℝ≥0∞} :
    MeanLe (Specimen.FailWith.failWith e : SGen A) f c := by
  unfold MeanLe; rw [sexpect_failWith]; exact zero_le

theorem meanLe_truncations {ls : List (Specimen.Label A)} {f : A → ℝ≥0∞} {c : ℝ≥0∞} :
    MeanLe (Specimen.truncations ls : SGen A) f c := by
  unfold Specimen.truncations
  split
  · exact meanLe_fail
  · exact meanLe_failWith

theorem sok_bind (g : SGen A) (k : A → SGen B) : sok (g >>= k) = sexpect g fun a => sok (k a) :=
  sexpect_bind g k _

/-- A bind keeps a mean bounded by one constant. -/
theorem meanLe_bind_const {g : SGen A} {k : A → SGen B} {f : B → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, MeanLe (k a) f c) : MeanLe (g >>= k) f c := by
  unfold MeanLe
  rw [sexpect_bind, sok_bind, ← sexpect_mul_left]
  exact sexpect_mono g h

/-- **A bind keeps a mean bounded by a function of the draw, where the continuation succeeds equally
often whatever is drawn.** The successes then weigh the draws as `g` does, and the mean of the
bound is `g`'s. -/
theorem meanLe_bind_uniform {g : SGen A} {k : A → SGen B} {f : B → ℝ≥0∞} {c : A → ℝ≥0∞} {c₀ q : ℝ≥0∞}
    (hk : ∀ a, MeanLe (k a) f (c a)) (hq : ∀ a, sok (k a) = q) (hg : MeanLe g c c₀) :
    MeanLe (g >>= k) f c₀ := by
  unfold MeanLe at *
  rw [sexpect_bind, sok_bind]
  calc sexpect g (fun a => sexpect (k a) f) ≤ sexpect g (fun a => q * c a) :=
        sexpect_mono g fun a => (hk a).trans_eq (by rw [hq, mul_comm])
    _ = q * sexpect g c := sexpect_mul_left g q c
    _ ≤ q * (c₀ * sok g) := by gcongr
    _ = c₀ * sexpect g (fun a => sok (k a)) := by
        rw [sexpect_congr g hq, show (fun _ : A => q) = fun _ => q * 1 from funext fun _ => (mul_one q).symm,
          sexpect_mul_left, sok]; ring

theorem meanLe_map {g : SGen A} {h : A → B} {f : B → ℝ≥0∞} {c : ℝ≥0∞} (hg : MeanLe g (f ∘ h) c) :
    MeanLe (h <$> g) f c := by
  unfold MeanLe sok at *; rw [sexpect_map, sexpect_map]; exact hg

theorem meanLe_congr {g : SGen A} {f f' : A → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, f a = f' a)
    (hg : MeanLe g f c) : MeanLe g f' c := by
  unfold MeanLe at *; rwa [← sexpect_congr g h]

/-! ## Outcome profiles

Whether a search succeeds depends on whether each branch it tries succeeds, not on what with. So a
generator's chances of success and of failure, `(sok, sfail)`, are computed from its parts'. -/

theorem sfail_bind (g : SGen A) (k : A → SGen B) :
    sfail (g >>= k) = sfail g + sexpect g fun a => sfail (k a) := by
  unfold sfail sexpect
  rw [ExceptT.run_bind, OptionT.run_bind, Option.elimM, SPMF.expect_bind, ← SPMF.expect_add]
  congr 1; funext o
  rcases o with _ | _ | a <;> simp [Option.elim, SPMF.expect_pure, OptionT.run_pure, failVal, succVal]

@[simp] theorem sfail_pure (a : A) : sfail (pure a : SGen A) = 0 := by
  simp [sfail, ExceptT.run_pure, OptionT.run_pure, SPMF.expect_pure, failVal]

/-- Successes and failures share the mass. -/
theorem sok_add_sfail_le (g : SGen A) : sok g + sfail g ≤ 1 := by
  unfold sok sexpect sfail
  rw [← SPMF.expect_add]
  calc _ = SPMF.expect g.run.run (fun _ => 1) := by
        congr 1; funext o; rcases o with _ | _ | a <;> simp [succVal, failVal]
    _ = g.run.run.mass := SPMF.expect_one _
    _ ≤ 1 := SPMF.mass_le_one _

/-- A generator that succeeds surely never fails. -/
theorem sfail_eq_zero_of_sok {g : SGen A} (h : sok g = 1) : sfail g = 0 := by
  have := sok_add_sfail_le g
  rw [h] at this
  by_contra hne
  exact absurd (lt_of_lt_of_le (ENNReal.lt_add_right ENNReal.one_ne_top hne) this) (lt_irrefl 1)

/-- Two generators that succeed and fail equally often. -/
def SameProfile (g : SGen A) (g' : SGen B) : Prop := sok g = sok g' ∧ sfail g = sfail g'

/-- After the same draw, continuations that succeed and fail equally often. -/
theorem sameProfile_bind {g : SGen A} {k : A → SGen B} {k' : A → SGen B}
    (h : ∀ a, SameProfile (k a) (k' a)) : SameProfile (g >>= k) (g >>= k') :=
  ⟨by rw [sok_bind, sok_bind]; exact sexpect_congr g fun a => (h a).1,
   by rw [sfail_bind, sfail_bind]; congr 1; exact sexpect_congr g fun a => (h a).2⟩

/-- A continuation whose profile is one constant: the bind's profile is the draw's, scaled. -/
theorem profile_bind_const {g : SGen A} {k : A → SGen B} {s r : ℝ≥0∞}
    (hs : ∀ a, sok (k a) = s) (hr : ∀ a, sfail (k a) = r) :
    sok (g >>= k) = s * sok g ∧ sfail (g >>= k) = sfail g + r * sok g := by
  refine ⟨?_, ?_⟩
  · rw [sok_bind, sexpect_congr g hs, sok, ← sexpect_mul_left g s (fun _ => 1)]; simp only [mul_one]
  · rw [sfail_bind, sexpect_congr g hr, sok, ← sexpect_mul_left g r (fun _ => 1)]; simp only [mul_one]

/-- Different draws, each followed by a continuation of one profile: equal profiles where the draws
have. -/
theorem sameProfile_bind_const {g : SGen A} {g' : SGen B} {k : A → SGen C} {k' : B → SGen C}
    {s r : ℝ≥0∞} (hg : SameProfile g g') (hs : ∀ a, sok (k a) = s) (hr : ∀ a, sfail (k a) = r)
    (hs' : ∀ a, sok (k' a) = s) (hr' : ∀ a, sfail (k' a) = r) : SameProfile (g >>= k) (g' >>= k') := by
  obtain ⟨h1, h2⟩ := profile_bind_const (g := g) hs hr
  obtain ⟨h1', h2'⟩ := profile_bind_const (g := g') hs' hr'
  exact ⟨by rw [h1, h1', hg.1], by rw [h2, h2', hg.1, hg.2]⟩

/-- Different draws of one profile, then continuations all of one profile. -/
theorem sameProfile_bind_uniform [Inhabited A] {g g' : SGen A} {k k' : A → SGen C}
    (hg : SameProfile g g') (hk : ∀ a b, SameProfile (k a) (k' b)) :
    SameProfile (g >>= k) (g' >>= k') :=
  sameProfile_bind_const (s := sok (k default)) (r := sfail (k default)) hg
    (fun a => (hk a default).1.trans (hk default default).1.symm)
    (fun a => (hk a default).2.trans (hk default default).2.symm)
    (fun b => (hk default b).1.symm) (fun b => (hk default b).2.symm)

@[simp] theorem sok_pure' (a : A) : sok (pure a : SGen A) = 1 := sok_pure a

theorem sameProfile_refl (g : SGen A) : SameProfile g g := ⟨rfl, rfl⟩

theorem expect_finish_fail (acc : Option Exhaustion) :
    SPMF.expect (Backtrack.finish acc : OptionT SPMF (Except Exhaustion A)).run failVal = 1 := by
  cases acc <;> simp [Backtrack.finish, OptionT.run_failure, SPMF.expect_pure, failVal]

/-- The search after drawing `m`. -/
noncomputable def searchStep (fuel : Nat) (gs : List (Nat × (Unit → SGen A))) (acc : Option Exhaustion) (m : Nat) :
    SPMF (Option (Except Exhaustion A)) :=
  match pickDrop gs m with
  | none => (Backtrack.finish acc).run
  | some (_, g, rest) => do
    match ← (g ()).run.run with
    | some (.ok a) => pure (some (.ok a))
    | some (.error e) => (searchWith fuel rest (some (acc.elim e (max · e)))).run
    | none => (searchWith fuel rest acc).run

theorem searchWith_succ_run (fuel : Nat) (p : Nat × (Unit → SGen A)) (gs : List (Nat × (Unit → SGen A)))
    (acc : Option Exhaustion) :
    (searchWith (fuel + 1) (p :: gs) acc).run =
      chooseNat 0 (sumWeights (p :: gs) - 1) (Nat.zero_le _) >>= searchStep fuel (p :: gs) acc := by
  simp only [searchWith, OptionT.run_mk, chooseNat, bind_map_left]
  congr 1; funext n
  unfold searchStep
  split <;> (rename_i heq; simp only [heq])
  congr 1; funext o
  rcases o with _ | _ | _ <;> rfl

theorem expect_searchStep_none {fuel : Nat} {gs : List (Nat × (Unit → SGen A))} {acc : Option Exhaustion}
    {m : Nat} (h : pickDrop gs m = none) :
    SPMF.expect (searchStep fuel gs acc m) (succVal fun _ => 1) = 0 ∧
      SPMF.expect (searchStep fuel gs acc m) failVal = 1 := by
  simp [searchStep, h, expect_finish_succ, expect_finish_fail]

/-- Past a drawn branch: its successes, and the rest's at its failures. -/
theorem expect_searchStep_some {fuel : Nat} {gs : List (Nat × (Unit → SGen A))} {acc : Option Exhaustion}
    {m k : Nat} {g : Unit → SGen A} {rest : List (Nat × (Unit → SGen A))}
    (h : pickDrop gs m = some (k, g, rest)) {V U : ℝ≥0∞}
    (hV : ∀ a, SPMF.expect (searchWith fuel rest a).run (succVal fun _ => 1) = V)
    (hU : ∀ a, SPMF.expect (searchWith fuel rest a).run failVal = U) :
    SPMF.expect (searchStep fuel gs acc m) (succVal fun _ => 1) = sok (g ()) + V * sfail (g ()) ∧
      SPMF.expect (searchStep fuel gs acc m) failVal = U * sfail (g ()) := by
  simp only [searchStep, h]
  rw [SPMF.expect_bind, SPMF.expect_bind, sok, sexpect, sfail, ← SPMF.expect_mul_left,
    ← SPMF.expect_mul_left, ← SPMF.expect_add]
  constructor <;> (congr 1; funext o; rcases o with _ | _ | a) <;>
    simp [SPMF.expect_pure, succVal, failVal, hV, hU]

/-- Branches of the same weights and profiles. -/
def BranchesAlike (gs gs' : List (Nat × (Unit → SGen A))) : Prop :=
  List.Forall₂ (fun p p' => p.1 = p'.1 ∧ SameProfile (p.2 ()) (p'.2 ())) gs gs'

theorem BranchesAlike.refl : ∀ gs : List (Nat × (Unit → SGen A)), BranchesAlike gs gs
  | [] => .nil
  | p :: gs => .cons ⟨rfl, sameProfile_refl _⟩ (BranchesAlike.refl gs)

theorem BranchesAlike.sumWeights_eq {gs gs' : List (Nat × (Unit → SGen A))} (h : BranchesAlike gs gs') :
    sumWeights gs = sumWeights gs' := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp only [sumWeights_cons, hp.1, ih]

/-- Alike branch lists draw alike: both nothing, or branches alike with the rests alike. -/
theorem BranchesAlike.pickDrop {gs gs' : List (Nat × (Unit → SGen A))} (h : BranchesAlike gs gs') :
    ∀ n, (Backtrack.pickDrop gs n = none ∧ Backtrack.pickDrop gs' n = none) ∨
      ∃ k g rest g' rest', Backtrack.pickDrop gs n = some (k, g, rest) ∧
        Backtrack.pickDrop gs' n = some (k, g', rest') ∧ SameProfile (g ()) (g' ()) ∧
        BranchesAlike rest rest' := by
  induction h with
  | nil => intro n; left; exact ⟨rfl, rfl⟩
  | @cons p p' gs gs' hp hrest ih =>
    intro n
    obtain ⟨k, g⟩ := p
    obtain ⟨k', g'⟩ := p'
    obtain ⟨rfl, hpr⟩ := hp
    by_cases hn : n < k
    · exact Or.inr ⟨k, g, gs, g', gs', by simp [Backtrack.pickDrop, hn],
        by simp [Backtrack.pickDrop, hn], hpr, hrest⟩
    · rcases ih (n - k) with ⟨h1, h2⟩ | ⟨k₀, g₀, r₀, g₀', r₀', h1, h2, hg, hr⟩
      · left; simp [Backtrack.pickDrop, hn, h1, h2]
      · right
        exact ⟨k₀, g₀, (k, g) :: r₀, g₀', (k, g') :: r₀', by simp [Backtrack.pickDrop, hn, h1],
          by simp [Backtrack.pickDrop, hn, h2], hg, List.Forall₂.cons ⟨rfl, hpr⟩ hr⟩

/-- **A search's profile is its branches'.** Searches over alike branches succeed and fail equally
often, whatever labels they carry. -/
theorem profile_searchWith_congr : ∀ (fuel : Nat) (gs gs' : List (Nat × (Unit → SGen A)))
    (acc acc' : Option Exhaustion), BranchesAlike gs gs' →
    SPMF.expect (searchWith fuel gs acc).run (succVal fun _ => 1) =
        SPMF.expect (searchWith fuel gs' acc').run (succVal fun _ => 1) ∧
      SPMF.expect (searchWith fuel gs acc).run failVal = SPMF.expect (searchWith fuel gs' acc').run failVal
  | _, [], [], acc, acc', _ => by simp [searchWith, expect_finish_succ, expect_finish_fail]
  | _, [], _ :: _, _, _, h => nomatch h
  | _, _ :: _, [], _, _, h => nomatch h
  | 0, _ :: _, _ :: _, acc, acc', _ => by simp [searchWith, expect_finish_succ, expect_finish_fail]
  | fuel + 1, _ :: _, _ :: _, acc, acc', h => by
    have hW := h.sumWeights_eq
    -- The search past the first draw, from alike rests, at any labels.
    have ih := fun rest rest' (hr : BranchesAlike rest rest') a a' =>
      profile_searchWith_congr fuel rest rest' a a' hr
    rw [searchWith_succ_run, searchWith_succ_run]
    simp only [SPMF.expect_bind]
    rw [hW]
    constructor <;> (congr 1; funext m) <;>
      rcases h.pickDrop m with ⟨h1, h2⟩ | ⟨k, g, rest, g', rest', h1, h2, hg, hr⟩
    all_goals try first
      | rw [(expect_searchStep_none h1).1, (expect_searchStep_none h2).1]
      | rw [(expect_searchStep_none h1).2, (expect_searchStep_none h2).2]
    all_goals try
      have hV := fun a => (ih rest rest' hr a none).1
      have hV' := fun a => (ih rest' rest' (BranchesAlike.refl rest') a none).1
      have hU := fun a => (ih rest rest' hr a none).2
      have hU' := fun a => (ih rest' rest' (BranchesAlike.refl rest') a none).2
      first
        | rw [(expect_searchStep_some h1 hV hU).1, (expect_searchStep_some h2 hV' hU').1, hg.1, hg.2]
        | rw [(expect_searchStep_some h1 hV hU).2, (expect_searchStep_some h2 hV' hU').2, hg.2]

/-- **Alike branches, alike searches.** -/
theorem sameProfile_backtrack {gs gs' : List (Nat × (Unit → SGen A))} (h : BranchesAlike gs gs') :
    SameProfile (Specimen.Backtrack.backtrack gs) (Specimen.Backtrack.backtrack gs') := by
  have hl : gs.length = gs'.length := List.Forall₂.length_eq h
  have := profile_searchWith_congr gs.length gs gs' none none h
  refine ⟨?_, ?_⟩
  · show SPMF.expect (searchWith gs.length gs none).run _ = SPMF.expect (searchWith gs'.length gs' none).run _
    rw [← hl]; exact this.1
  · show SPMF.expect (searchWith gs.length gs none).run _ = SPMF.expect (searchWith gs'.length gs' none).run _
    rw [← hl]; exact this.2

end Specimen.Correctness
