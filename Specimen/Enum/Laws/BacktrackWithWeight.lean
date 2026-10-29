/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.BacktrackWeight
public import Specimen.Enum.Laws.BacktrackWith
public import Specimen.Enum.WeightedBacktrackWith
import Basalt.SPMF.Mass

/-!
# Weights Are Probabilities, With Failures That Say Why

`WeighsWith y x` relates a generator with labelled failures at `ExceptT ε WFinite` to its search at
`ExceptT ε (OptionT SPMF)` exactly: where `y` is defined, its entries weigh each success and each
label as `x` does, and what they leave of `1` is the probability that `x` is refuted. It is a `GenRel`
(`genRel_weighsWith`), so `walk` proves it per generator; the rule for `backtrack` rests on the
search's average (`Backtrack.expect_searchWith`): its successes as without labels, its failure a
product over the branches.
-/

@[expose] public section

open Lean.Order RandomChoice
open scoped ENNReal NNRat

namespace Specimen

open Basalt

variable {ε α β : Type}

/-- `y`, if defined, has nonnegative weights, under which every function of an outcome has its
expectation over `x`'s outcomes, and the weights and `x`'s probability of being refuted sum to `1`. -/
def WeighsWith {ε α : Type} (y : ExceptT ε WFinite α) (x : ExceptT ε (OptionT SPMF) α) : Prop :=
  WeighsSome y.run x.run

namespace WeighsWith

theorem pure (a : α) : WeighsWith (Pure.pure a : ExceptT ε WFinite α) (Pure.pure a) :=
  WeighsSome.pure (Except.ok a : Except ε α)

theorem bind {y : ExceptT ε WFinite α} {x : ExceptT ε (OptionT SPMF) α}
    {k' : α → ExceptT ε WFinite β} {k : α → ExceptT ε (OptionT SPMF) β}
    (hk : ∀ a, WeighsWith (k' a) (k a)) (hy : WeighsWith y x) :
    WeighsWith (y >>= k') (x >>= k) := by
  show WeighsSome (y.run >>= ExceptT.bindCont k') (x.run >>= ExceptT.bindCont k)
  refine WeighsSome.bind (fun r => ?_) hy
  cases r with
  | ok a => exact hk a
  | error e => exact WeighsSome.pure _

theorem map {y : ExceptT ε WFinite α} {x : ExceptT ε (OptionT SPMF) α} (f : α → β)
    (hy : WeighsWith y x) : WeighsWith (f <$> y) (f <$> x) := by
  rw [EnumeratesWith.map_eq_bind, EnumeratesWith.map_eq_bind]
  exact bind (fun a => pure (f a)) hy

theorem default (x : ExceptT ε (OptionT SPMF) α) :
    WeighsWith (Inhabited.default : ExceptT ε WFinite α) x := fun h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    WeighsWith (RandomChoice.choose lo hi h : ExceptT ε WFinite _)
      (RandomChoice.choose lo hi h : ExceptT ε (OptionT SPMF) _) :=
  WeighsSome.map Except.ok (WeighsSome.choose lo hi h)

theorem admissible (x : ExceptT ε (OptionT SPMF) α) :
    Lean.Order.admissible fun y : ExceptT ε WFinite α => WeighsWith y x :=
  Finite.admissible_defined (α := Except ε α × Rat) _

theorem fail : WeighsWith (Fail.fail : ExceptT ε WFinite α) (Fail.fail : ExceptT ε (OptionT SPMF) α) :=
  WeighsSome.map Except.ok WeighsSome.fail

theorem failWith (e : ε) :
    WeighsWith (FailWith.failWith e : ExceptT ε WFinite α)
      (FailWith.failWith e : ExceptT ε (OptionT SPMF) α) :=
  WeighsSome.pure (Except.error e : Except ε α)

theorem seq {f : ExceptT ε WFinite (α → β)} {f' : ExceptT ε (OptionT SPMF) (α → β)}
    {y : ExceptT ε WFinite α} {x : ExceptT ε (OptionT SPMF) α}
    (hf : WeighsWith f f') (hy : WeighsWith y x) : WeighsWith (f <*> y) (f' <*> x) :=
  bind (fun g => map g hy) hf

end WeighsWith

@[walk_rel]
theorem genRel_weighsWith :
    GenRel (ExceptT ε WFinite) (ExceptT ε (OptionT SPMF)) (@WeighsWith ε) where
  pure := WeighsWith.pure
  bind := WeighsWith.bind
  map := WeighsWith.map
  default := WeighsWith.default
  choose := WeighsWith.choose
  admissible := WeighsWith.admissible

attribute [gen_rule] WeighsWith.fail WeighsWith.failWith WeighsWith.seq

/-! ## Sums over outcomes -/

theorem tsum_option_eq (f : Option β → ℝ≥0∞) : ∑' o, f o = f none + ∑' b, f (some b) := by
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  refine ((Option.some_injective β).tsum_eq fun o ho => ?_).symm.trans (tsum_congr fun a => ?_)
  · cases o with
    | none => simp at ho
    | some a => exact ⟨a, rfl⟩
  · simp

theorem tsum_except_eq (f : Except ε α → ℝ≥0∞) :
    ∑' r, f r = ∑' a, f (.ok a) + ∑' e, f (.error e) := by
  let e : ε ⊕ α ≃ Except ε α :=
    { toFun := Sum.elim .error .ok
      invFun := fun r => match r with
        | .error e => .inl e
        | .ok a => .inr a
      left_inv := fun s => by cases s <;> rfl
      right_inv := fun r => by cases r <;> rfl }
  rw [← e.tsum_eq, ENNReal.summable.tsum_sum ENNReal.summable, add_comm]
  rfl

/-! ## The search at `OptionT SPMF` -/

namespace Backtrack

/-- A branch's probability of each way of failing: refuted, or with each label. -/
noncomputable def failWeights (x : ExceptT ε (OptionT SPMF) α) : Option ε → ℝ≥0∞
  | none => x.run.run none
  | some l => x.run.run (some (.error l))

/-- Each branch's weight and its probability of each way of failing. -/
noncomputable def failData (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) :
    List (Nat × (Option ε → ℝ≥0∞)) :=
  gs.map fun p => (p.1, failWeights (p.2 ()))

/-- Each branch's weight, probability of failing (`1` for a branch never drawn), and itself. -/
noncomputable def branchDataWith (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) :
    List (Nat × ℝ≥0∞ × (Unit → ExceptT ε (OptionT SPMF) α)) :=
  gs.map fun p => (p.1, if p.1 = 0 then 1 else ∑' o, failWeights (p.2 ()) o, p.2)

/-- `H` averaged over how the branches of positive weight fail, independently, each folding its way
of failing into the labels so far. -/
noncomputable def failJoin [Max ε] (H : Option ε → ℝ≥0∞) :
    List (Nat × (Option ε → ℝ≥0∞)) → Option ε → ℝ≥0∞
  | [], acc => H acc
  | (w, m) :: rest, acc =>
    if w = 0 then failJoin H rest acc else ∑' o, m o * failJoin H rest (Option.merge max acc o)

theorem merge_right_comm [SemilatticeSup ε] (a b c : Option ε) :
    Option.merge max (Option.merge max a b) c = Option.merge max (Option.merge max a c) b := by
  cases a <;> cases b <;> cases c <;> simp [sup_comm, sup_left_comm]

/-- The order the branches fail in does not show. -/
theorem failJoin_perm [SemilatticeSup ε] (H : Option ε → ℝ≥0∞)
    {l₁ l₂ : List (Nat × (Option ε → ℝ≥0∞))} (h : l₁.Perm l₂) :
    ∀ acc, failJoin H l₁ acc = failJoin H l₂ acc := by
  induction h with
  | nil => intro _; rfl
  | cons x _ ih =>
    intro acc
    obtain ⟨w, m⟩ := x
    simp only [failJoin, ih]
  | swap x y l =>
    intro acc
    obtain ⟨w, m⟩ := x
    obtain ⟨w', m'⟩ := y
    simp only [failJoin]
    by_cases hw : w = 0 <;> by_cases hw' : w' = 0 <;> simp only [hw, hw', ↓reduceIte]
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun o => tsum_congr fun o' => ?_
    rw [merge_right_comm]
    ring
  | trans _ _ ih₁ ih₂ => intro acc; rw [ih₁, ih₂]

theorem failJoin_of_sumWeights_eq_zero [Max ε] (H : Option ε → ℝ≥0∞) :
    ∀ (l : List (Nat × (Option ε → ℝ≥0∞))) (acc : Option ε), sumWeights l = 0 →
      failJoin H l acc = H acc
  | [], _, _ => rfl
  | (w, m) :: rest, acc, h => by
    simp only [sumWeights_cons] at h
    simp only [failJoin, show w = 0 by omega, ↓reduceIte]
    exact failJoin_of_sumWeights_eq_zero H rest acc (by omega)

theorem perm_picks : ∀ {l : List β} {e : β × List β}, e ∈ picks l → (e.1 :: e.2).Perm l
  | [], _, h => by simp [picks] at h
  | p :: rest, e, h => by
    simp only [picks, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨e', he', rfl⟩
    · exact List.Perm.refl _
    · exact (List.Perm.swap p e'.1 e'.2).trans ((perm_picks he').cons p)

theorem some_elim_eq_merge [Max ε] (acc : Option ε) (e : ε) :
    some (acc.elim e (max · e)) = Option.merge max acc (some e) := by
  cases acc <;> rfl

theorem expect_finish (acc : Option ε) (G : Option (Except ε α) → ℝ≥0∞) :
    SPMF.expect (finish acc : OptionT SPMF (Except ε α)).run G = G (acc.map .error) := by
  cases acc <;> exact SPMF.expect_pure _ _

/-- One unfolding of the search: a branch drawn by weight, then on a failure the search among the
rest, the labels so far joined with the branch's. -/
theorem expect_searchWith_succ [Max ε] (G : Option (Except ε α) → ℝ≥0∞) (fuel : Nat)
    (q : Nat × (Unit → ExceptT ε (OptionT SPMF) α)) (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α)))
    (acc : Option ε) :
    SPMF.expect (searchWith (fuel + 1) (q :: gs) acc).run G =
      if sumWeights (q :: gs) = 0 then G (acc.map .error) else (sumWeights (q :: gs) : ℝ≥0∞)⁻¹ *
        ((picks (q :: gs)).map fun e => (e.1.1 : ℝ≥0∞) *
          SPMF.expect (e.1.2 ()).run.run (fun o => match o with
            | some (.ok a) => G (some (.ok a))
            | some (.error l) => SPMF.expect (searchWith fuel e.2 (Option.merge max acc (some l))).run G
            | none => SPMF.expect (searchWith fuel e.2 acc).run G)).sum := by
  simp only [searchWith, OptionT.run_mk]
  rw [SPMF.expect_bind]
  let H : Option (Nat × (Unit → ExceptT ε (OptionT SPMF) α) ×
      List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) → ℝ≥0∞ := fun o => SPMF.expect (match o with
        | none => (finish acc : OptionT SPMF (Except ε α)).run
        | some (_, g, rest) => (g ()).run.run >>= fun o => match o with
          | some (.ok a) => Pure.pure (some (.ok a))
          | some (.error e) => (searchWith fuel rest (some (acc.elim e (max · e)))).run
          | none => (searchWith fuel rest acc).run) G
  refine Eq.trans (congrArg (SPMF.expect (choose 0 (sumWeights (q :: gs) - 1) (Nat.zero_le _)))
    (funext fun a => ?_ : _ = fun a => H (pickDrop (q :: gs) a.down.val))) ?_
  · generalize pickDrop (q :: gs) a.down.val = o
    rcases o with _ | ⟨_, g, rest⟩ <;> rfl
  show Mix.average.mix 0 _ _ = _
  rw [Mix.range_average 0 _ (fun n => H (pickDrop (q :: gs) n))]
  by_cases hW : sumWeights (q :: gs) = 0
  · simp only [hW, ↓reduceIte, Nat.zero_sub, Finset.Icc_self, Finset.sum_singleton, zero_add,
      Nat.cast_one, div_one, pickDrop_of_le (Nat.le_of_eq hW)]
    exact expect_finish acc G
  · simp only [hW, ↓reduceIte]
    rw [show sumWeights (q :: gs) - 1 - 0 + 1 = sumWeights (q :: gs) by omega,
      show Finset.Icc 0 (sumWeights (q :: gs) - 1) = Finset.range (sumWeights (q :: gs)) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_range]; omega,
      sum_range_pickDrop, div_eq_mul_inv, mul_comm]
    congr 2
    refine List.map_congr_left fun e _ => ?_
    simp only [nsmul_eq_mul]
    congr 1
    show SPMF.expect ((e.1.2 ()).run.run >>= _) G = _
    rw [SPMF.expect_bind]
    congr 1
    funext o
    rcases o with _ | _ | _
    · rfl
    · simp only [some_elim_eq_merge]
    · exact SPMF.expect_pure _ _

/-- The search's average, given fuel to try every branch: its successes weighted by the probability
that the search reaches their branch, as without labels, and how it fails averaged over the branches
failing independently. -/
theorem expect_searchWith [SemilatticeSup ε] (G : Option (Except ε α) → ℝ≥0∞) :
    ∀ (fuel : Nat) (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) (acc : Option ε),
    gs.length ≤ fuel →
    SPMF.expect (searchWith fuel gs acc).run G =
      mix (fun g => ∑' a, (g ()).run.run (some (.ok a)) * G (some (.ok a))) 0 fuel (branchDataWith gs) +
        failJoin (fun o => G (o.map .error)) (failData gs) acc
  | fuel, [], acc, _ => by
    have h : searchWith fuel ([] : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) acc =
        finish acc := by
      cases fuel <;> rfl
    rw [h, expect_finish]
    cases fuel <;> simp [mix_zero, mix_succ, branchDataWith, failData, failJoin]
  | 0, _ :: _, _, h => by simp at h
  | fuel + 1, q :: gs, acc, h => by
    rw [expect_searchWith_succ, mix_succ]
    have hs : sumWeights (branchDataWith (q :: gs)) = sumWeights (q :: gs) :=
      sumWeights_map (h := fun p : Nat × (Unit → ExceptT ε (OptionT SPMF) α) =>
        (p.1, if p.1 = 0 then 1 else ∑' o, failWeights (p.2 ()) o, p.2)) (fun _ => rfl) _
    have hs' : sumWeights (failData (q :: gs)) = sumWeights (q :: gs) :=
      sumWeights_map (h := fun p : Nat × (Unit → ExceptT ε (OptionT SPMF) α) =>
        (p.1, failWeights (p.2 ()))) (fun _ => rfl) _
    rw [hs]
    by_cases hW : sumWeights (q :: gs) = 0
    · simp only [hW, ↓reduceIte, zero_add]
      exact (failJoin_of_sumWeights_eq_zero (fun o => G (o.map .error)) _ acc (hs'.trans hW)).symm
    · simp only [hW, ↓reduceIte]
      have key : ∀ e ∈ picks (q :: gs), (e.1.1 : ℝ≥0∞) *
          SPMF.expect (e.1.2 ()).run.run (fun o => match o with
            | some (.ok a) => G (some (.ok a))
            | some (.error l) => SPMF.expect (searchWith fuel e.2 (Option.merge max acc (some l))).run G
            | none => SPMF.expect (searchWith fuel e.2 acc).run G) =
          (e.1.1 : ℝ≥0∞) * ((∑' a, (e.1.2 ()).run.run (some (.ok a)) * G (some (.ok a))) +
            (if e.1.1 = 0 then 1 else ∑' o, failWeights (e.1.2 ()) o) *
              mix (fun g => ∑' a, (g ()).run.run (some (.ok a)) * G (some (.ok a))) 0 fuel
                (branchDataWith e.2)) +
          (e.1.1 : ℝ≥0∞) * failJoin (fun o => G (o.map .error)) (failData (q :: gs)) acc := by
        intro e he
        by_cases hw : e.1.1 = 0
        · simp [hw]
        have hl : e.2.length ≤ fuel := by
          have := length_picks he
          simp only [List.length_cons] at h this
          omega
        have hQ : failJoin (fun o => G (o.map .error)) (failData (q :: gs)) acc =
            ∑' o, failWeights (e.1.2 ()) o *
              failJoin (fun o => G (o.map .error)) (failData e.2) (Option.merge max acc o) := by
          have hp := failJoin_perm (fun o => G (o.map .error))
            ((perm_picks he).map fun p => (p.1, failWeights (p.2 ()))) acc
          rw [failData, ← hp]
          simp [failJoin, failData, hw]
        simp only [hw, ↓reduceIte, expect_searchWith G fuel e.2 _ hl, hQ]
        rw [SPMF.expect_option, tsum_except_eq, tsum_option_eq, tsum_option_eq]
        simp only [failWeights, Option.merge_none_right, mul_add, ENNReal.tsum_add,
          ENNReal.tsum_mul_right]
        ring
      rw [List.map_congr_left key, List.sum_map_add, mul_add, branchDataWith, picks_map,
        List.map_map]
      congr 1
      rw [List.sum_map_mul_right, sum_picks_weights, ← mul_assoc,
        ENNReal.inv_mul_cancel (by exact_mod_cast hW) (ENNReal.natCast_ne_top _), one_mul]

theorem mass_bind_eq_one {γ : Type} {x : SPMF β} {f : β → SPMF γ} (hx : x.mass = 1)
    (hf : ∀ b, (f b).mass = 1) : (x >>= f).mass = 1 := by
  rw [SPMF.mass_bind_tsum]
  simp only [hf, mul_one]
  exact hx

/-- The search terminates when every branch it can draw does. -/
theorem mass_searchWith [Max ε] : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) (acc : Option ε),
    (∀ p ∈ gs, 0 < p.1 → (p.2 ()).run.run.mass = 1) → (searchWith fuel gs acc).run.mass = 1
  | _, [], acc, _ | 0, _ :: _, acc, _ => by
    simp only [searchWith]
    cases acc <;> exact SPMF.mass_pure _
  | fuel + 1, q :: gs, acc, h => by
    simp only [searchWith, OptionT.run_mk]
    refine mass_bind_eq_one (SPMF.mass_choose _ _ _) fun n => ?_
    split
    · cases acc <;> exact SPMF.mass_pure _
    · rename_i k g rest hpick
      obtain ⟨hm, hk, hr⟩ := pickDrop_some hpick
      refine mass_bind_eq_one (h _ hm hk) fun o => ?_
      rcases o with _ | _ | _
      · exact mass_searchWith fuel rest acc fun p hp => h p (hr p hp)
      · exact mass_searchWith fuel rest _ fun p hp => h p (hr p hp)
      · exact SPMF.mass_pure _

/-- Two draws from the same range, followed by the same continuation. -/
theorem choose_bind_congr {G : Type → Type} [Monad G] [RandomChoice G] {γ : Type} {s₁ s₂ : Nat}
    (hs : s₁ = s₂) {h₁ : 0 ≤ s₁} {h₂ : 0 ≤ s₂} {k₁ : ULift {x : Nat // 0 ≤ x ∧ x ≤ s₁} → G γ}
    {k₂ : ULift {x : Nat // 0 ≤ x ∧ x ≤ s₂} → G γ}
    (hk : ∀ n hn₁ hn₂, k₁ (.up ⟨n, hn₁⟩) = k₂ (.up ⟨n, hn₂⟩)) :
    (RandomChoice.choose 0 s₁ h₁ >>= k₁) = (RandomChoice.choose 0 s₂ h₂ >>= k₂) := by
  subst hs
  exact congrArg _ (funext fun ⟨⟨n, hn⟩⟩ => hk n hn hn)

theorem pickDrop_map {κ : Type} (f : β → κ) : ∀ (gs : List (Nat × β)) (n : Nat),
    pickDrop (gs.map fun p => (p.1, f p.2)) n =
      (pickDrop gs n).map fun t => (t.1, f t.2.1, t.2.2.map fun p => (p.1, f p.2))
  | [], _ => rfl
  | (k, g) :: rest, n => by
    simp only [List.map_cons, pickDrop]
    split
    · rfl
    · rw [pickDrop_map f rest]
      simp [Option.map_map, Function.comp_def]

/-- One draw over labelled failures is one draw over the branches' runs: with no fuel left, the search
ends as the branch it drew did. -/
theorem searchWith_one {G : Type → Type} [Monad G] [RandomChoice G] [Max ε]
    (gs : List (Nat × (Unit → ExceptT ε (OptionT G) α))) :
    searchWith 1 gs none = search 1 (gs.map fun p => (p.1, fun u => (p.2 u).run)) := by
  cases gs with
  | nil => rfl
  | cons q gs =>
    have hs : sumWeights ((q :: gs).map fun p => (p.1, fun u => (p.2 u).run)) =
        sumWeights (q :: gs) :=
      sumWeights_map (h := fun p : Nat × (Unit → ExceptT ε (OptionT G) α) =>
        (p.1, fun u => (p.2 u).run)) (fun _ => rfl) _
    have hp := pickDrop_map (fun g : Unit → ExceptT ε (OptionT G) α => fun u => (g u).run) (q :: gs)
    simp only [List.map_cons] at hs hp
    simp only [searchWith, search, List.map_cons, hp]
    congr 1
    refine choose_bind_congr (by rw [hs]) fun n _ _ => ?_
    dsimp only
    cases pickDrop (q :: gs) n with
    | none => rfl
    | some t =>
      obtain ⟨k, g, rest⟩ := t
      simp only [Option.map_some]
      refine congrArg _ (funext fun o => ?_)
      rcases o with _ | _ | _ <;> cases rest <;> rfl

end Backtrack

/-! ## The labelled search at `WFinite` -/

namespace WFinite

theorem expect_pure (a : β) (g : β → ℝ≥0∞) : Finite.expect (Pure.pure a : WFinite β) g = g a := by
  show Finite.expect (Finite.singleton (a, 1)) g = g a
  simp [Finite.singleton]

theorem nonneg_pure (a : β) : Finite.Nonneg (Pure.pure a : WFinite β) := fun _ => by norm_num

/-- The tower rule at `WFinite`, every continuation defined. -/
theorem bind_spec {γ : Type} {y : WFinite β} {k : β → WFinite γ} (hy : y ≠ .undef)
    (hyn : Finite.Nonneg y) (hk : ∀ b, k b ≠ .undef ∧ Finite.Nonneg (k b)) :
    WFinite.bind y k ≠ .undef ∧ Finite.Nonneg (WFinite.bind y k) ∧
      ∀ g, Finite.expect (WFinite.bind y k) g = Finite.expect y fun b => Finite.expect (k b) g := by
  have hd : WFinite.bind y k ≠ .undef := Finite.bind_defined hy fun p _ => by
    rcases hkp : k p.1 with _ | ⟨n, f⟩
    · exact absurd hkp (hk p.1).1
    · simp [Finite.map]
  exact ⟨hd, nonneg_expect_bind hd hyn fun b _ => (hk b).2⟩

theorem oks_spec {y : WFinite (Except ε α)} (hy : y ≠ .undef) (hyn : Finite.Nonneg y) :
    oks y ≠ .undef ∧ Finite.Nonneg (oks y) ∧ ∀ g, Finite.expect (oks y) g =
      Finite.expect y fun r => match r with
        | .ok a => g a
        | .error _ => 0 := by
  obtain ⟨hd, hn, he⟩ := bind_spec (k := fun r : Except ε α => match r with
    | .ok a => (Pure.pure a : WFinite α)
    | .error _ => Fail.fail) hy hyn fun r => by
      cases r with
      | ok a => exact ⟨Finite.singleton_ne_undef _, nonneg_pure a⟩
      | error _ => exact ⟨Finite.empty_ne_undef, Finite.nonneg_empty⟩
  refine ⟨hd, hn, fun g => (he g).trans (congrArg (Finite.expect y) (funext fun r => ?_))⟩
  cases r with
  | ok a => exact expect_pure a g
  | error _ => exact Finite.expect_empty g

theorem failures_spec {y : WFinite (Except ε α)} (hy : y ≠ .undef) (hyn : Finite.Nonneg y) :
    failures y ≠ .undef ∧ Finite.Nonneg (failures y) ∧ ∀ h, Finite.expect (failures y) h =
      ofNNRat (failMass y) * h none + Finite.expect y fun r => match r with
        | .ok _ => 0
        | .error l => h (some l) := by
  obtain ⟨hd, hn, he⟩ := bind_spec (k := fun r : Except ε α => match r with
    | .ok _ => Fail.fail
    | .error l => (Pure.pure (some l) : WFinite (Option ε))) hy hyn fun r => by
      cases r with
      | ok _ => exact ⟨Finite.empty_ne_undef, Finite.nonneg_empty⟩
      | error l => exact ⟨Finite.singleton_ne_undef _, nonneg_pure _⟩
  have hs : Finite.singleton ((none : Option ε), (failMass y : Rat)) ≠ .undef :=
    Finite.singleton_ne_undef _
  refine ⟨Finite.union_defined hs hd,
    Finite.nonneg_union (fun _ => (failMass y).2) hn, fun h => ?_⟩
  refine (Finite.expect_union hs hd h).trans ?_
  congr 1
  · simp [Finite.singleton, ofNNRat_apply]
  · refine (he h).trans (congrArg (Finite.expect y) (funext fun r => ?_))
    cases r with
    | ok _ => exact Finite.expect_empty h
    | error l => exact expect_pure _ h

/-! ### Merging entries -/

/-- The expectation of `g` under a list of weighted entries. -/
noncomputable def listExpect (l : List (β × Rat)) (g : β → ℝ≥0∞) : ℝ≥0∞ :=
  (l.map fun p => ENNReal.ofReal p.2 * g p.1).sum

theorem expect_mk_eq_listExpect {n : Nat} (f : Fin n → β × Rat) (g : β → ℝ≥0∞) :
    Finite.expect (.mk n f) g = listExpect (List.ofFn f) g := by
  rw [Finite.expect_mk, listExpect, List.map_ofFn, List.sum_ofFn]
  rfl

theorem expect_ofList (l : List (β × Rat)) (g : β → ℝ≥0∞) :
    Finite.expect (.mk l.length fun i => l[i]) g = listExpect l g := by
  rw [expect_mk_eq_listExpect]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

theorem addEntry_spec [DecidableEq β] (g : β → ℝ≥0∞) (p : β × Rat) (hp : 0 ≤ p.2) :
    ∀ l : List (β × Rat), (∀ q ∈ l, 0 ≤ q.2) →
      (∀ q ∈ addEntry p l, 0 ≤ q.2) ∧
        listExpect (addEntry p l) g = ENNReal.ofReal p.2 * g p.1 + listExpect l g
  | [], _ => by simp [addEntry, listExpect, hp]
  | q :: qs, hl => by
    have hq : 0 ≤ q.2 := hl q (List.mem_cons_self ..)
    simp only [addEntry]
    split
    · rename_i h
      refine ⟨fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact add_nonneg hq hp
        · exact hl r (List.mem_cons_of_mem _ hr)
      · simp only [listExpect, List.map_cons, List.sum_cons]
        rw [Rat.cast_add, ENNReal.ofReal_add (by exact_mod_cast hq) (by exact_mod_cast hp), h]
        ring
    · obtain ⟨h₁, h₂⟩ := addEntry_spec g p hp qs fun r hr => hl r (List.mem_cons_of_mem _ hr)
      refine ⟨fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact hq
        · exact h₁ r hr
      · simp only [listExpect, List.map_cons, List.sum_cons] at h₂ ⊢
        rw [h₂]
        ring

theorem foldr_addEntry_spec [DecidableEq β] (g : β → ℝ≥0∞) :
    ∀ l : List (β × Rat), (∀ q ∈ l, 0 ≤ q.2) →
      (∀ q ∈ l.foldr addEntry [], 0 ≤ q.2) ∧ listExpect (l.foldr addEntry []) g = listExpect l g
  | [], _ => ⟨by simp, rfl⟩
  | p :: ps, hl => by
    obtain ⟨h₁, h₂⟩ := foldr_addEntry_spec g ps fun r hr => hl r (List.mem_cons_of_mem _ hr)
    obtain ⟨h₃, h₄⟩ := addEntry_spec g p (hl p (List.mem_cons_self ..)) _ h₁
    refine ⟨h₃, ?_⟩
    rw [List.foldr_cons, h₄, h₂]
    simp [listExpect]

theorem listExpect_filter (g : β → ℝ≥0∞) :
    ∀ l : List (β × Rat), listExpect (l.filter fun p => p.2 ≠ 0) g = listExpect l g
  | [] => rfl
  | p :: ps => by
    have ih := listExpect_filter g ps
    by_cases hp : p.2 = 0
    · simp only [List.filter_cons, hp, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte, ih]
      simp [listExpect, hp]
    · simp only [List.filter_cons, hp, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      simp only [listExpect, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

theorem merge_spec [DecidableEq β] {y : WFinite β} (hy : y ≠ .undef) (hyn : Finite.Nonneg y) :
    merge y ≠ .undef ∧ Finite.Nonneg (merge y) ∧ ∀ g, Finite.expect (merge y) g = Finite.expect y g := by
  cases y with
  | undef => exact absurd rfl hy
  | mk n f =>
    have hl : ∀ q ∈ List.ofFn f, 0 ≤ q.2 := fun q hq => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact hyn i
    simp only [merge]
    refine ⟨fun h => (by cases h), fun i => ?_, fun g => ?_⟩
    · have := List.getElem_mem (l := ((List.ofFn f).foldr addEntry []).filter fun p => p.2 ≠ 0)
        (n := i) i.2
      exact (foldr_addEntry_spec (fun _ => 0) _ hl).1 _ (List.mem_of_mem_filter this)
    · rw [expect_ofList, listExpect_filter, (foldr_addEntry_spec g _ hl).2, expect_mk_eq_listExpect]

/-! ### Joining the failures -/

theorem joinStep_spec [Max ε] [DecidableEq ε] {D : WFinite (Option ε)} {y : WFinite (Except ε α)}
    (hD : D ≠ .undef) (hDn : Finite.Nonneg D) (hy : y ≠ .undef) (hyn : Finite.Nonneg y) :
    joinStep D y ≠ .undef ∧ Finite.Nonneg (joinStep D y) ∧ ∀ H, Finite.expect (joinStep D y) H =
      Finite.expect D fun acc => Finite.expect (failures y) fun o => H (Option.merge max acc o) := by
  obtain ⟨hfd, hfn, -⟩ := failures_spec hy hyn
  have hinner := fun acc : Option ε => bind_spec
    (k := fun o => (Pure.pure (Option.merge max acc o) : WFinite (Option ε))) hfd hfn
    fun _ => ⟨Finite.singleton_ne_undef _, nonneg_pure _⟩
  obtain ⟨hbd, hbn, hbe⟩ := bind_spec (k := fun acc => WFinite.bind (failures y) fun o =>
    (Pure.pure (Option.merge max acc o) : WFinite (Option ε))) hD hDn
    fun acc => ⟨(hinner acc).1, (hinner acc).2.1⟩
  obtain ⟨hmd, hmn, hme⟩ := merge_spec hbd hbn
  refine ⟨hmd, hmn, fun H => ?_⟩
  rw [joinStep, hme, hbe]
  congr 1
  funext acc
  rw [(hinner acc).2.2]
  simp only [expect_pure]

theorem failMass_empty : failMass (Finite.empty : WFinite β) = 1 := by
  simp [failMass, Finite.empty]

theorem oks_empty : oks (Finite.empty : WFinite (Except ε α)) = Finite.empty := rfl

theorem oks_undef : oks (Finite.undef : WFinite (Except ε α)) = Finite.undef := rfl

/-- Folding the branches' failures in, each related to its ways of failing, is averaging over them. -/
theorem foldl_joinStep_spec [Max ε] [DecidableEq ε] (H : Option ε → ℝ≥0∞) :
    ∀ {ys : List (Nat × WFinite (Except ε α))} {ds : List (Nat × (Option ε → ℝ≥0∞))},
    List.Forall₂ (fun p d => p.1 = d.1 ∧ p.2 ≠ .undef ∧ Finite.Nonneg p.2 ∧
      (p.1 = 0 → p.2 = Finite.empty) ∧
      (p.1 ≠ 0 → ∀ h, Finite.expect (failures p.2) h = ∑' o, d.2 o * h o)) ys ds →
    ∀ {D : WFinite (Option ε)}, D ≠ .undef → Finite.Nonneg D →
    ys.foldl (fun D p => joinStep D p.2) D ≠ .undef ∧
      Finite.Nonneg (ys.foldl (fun D p => joinStep D p.2) D) ∧
      Finite.expect (ys.foldl (fun D p => joinStep D p.2) D) H =
        Finite.expect D fun acc => Backtrack.failJoin H ds acc
  | _, _, .nil, _, hD, hDn => ⟨hD, hDn, rfl⟩
  | p :: _, (w, m) :: _, .cons ⟨hw, hd, hn, hz, hf⟩ hrest, D, hD, hDn => by
    obtain ⟨hjd, hjn, hje⟩ := joinStep_spec hD hDn hd hn
    obtain ⟨h₁, h₂, h₃⟩ := foldl_joinStep_spec H hrest hjd hjn
    refine ⟨h₁, h₂, h₃.trans ((hje _).trans ?_)⟩
    congr 1
    funext acc
    simp only at hw
    subst hw
    simp only [Backtrack.failJoin]
    by_cases h0 : p.1 = 0
    · simp only [h0, ↓reduceIte]
      rw [hz h0, (failures_spec Finite.empty_ne_undef Finite.nonneg_empty).2.2, failMass_empty]
      simp
    · simp only [h0, ↓reduceIte]
      exact hf h0 _

/-! ### A branch, related -/

theorem expect_map_ok {y : WFinite α} (g : Except ε α → ℝ≥0∞) :
    Finite.expect (Finite.map (fun q => ((.ok q.1 : Except ε α), q.2)) y) g =
      Finite.expect y fun a => g (.ok a) := by
  cases y <;> rfl

theorem nonneg_map_ok {y : WFinite α} (hy : Finite.Nonneg y) :
    Finite.Nonneg (Finite.map (fun q => ((.ok q.1 : Except ε α), q.2)) y) := by
  cases y with
  | undef => trivial
  | mk n f => exact fun i => hy i

/-- What a related branch's weights say of its successes and its ways of failing. -/
theorem branch_spec {y : WFinite (Except ε α)} {x : ExceptT ε (OptionT SPMF) α}
    (h : WeighsSome y x.run) (hd : y ≠ .undef) :
    x.run.run.mass = 1 ∧ ofNNRat (failMass (oks y)) = ∑' o, Backtrack.failWeights x o ∧
      (∀ g, Finite.expect (oks y) g = ∑' a, x.run.run (some (.ok a)) * g a) ∧
      ∀ H, Finite.expect (failures y) H = ∑' o, Backtrack.failWeights x o * H o := by
  obtain ⟨hn, he, hm⟩ := h hd
  have hsome : ∑' r, x.run.run (some r) = Finite.expect y fun _ => 1 := by
    rw [he]
    simp
  have hmass : x.run.run.mass = 1 := by
    rw [SPMF.mass, tsum_option_eq, hsome, add_comm, hm]
  obtain ⟨hod, hon, hoe⟩ := oks_spec hd hn
  have hok : ∀ g, Finite.expect (oks y) g = ∑' a, x.run.run (some (.ok a)) * g a := fun g => by
    rw [hoe, he, tsum_except_eq]
    simp
  have hle : Finite.expect y (fun _ => 1) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_self_add hm)
  have hfail : ofNNRat (failMass y) = x.run.run none := by
    rw [ofNNRat_failMass hd hn]
    exact ENNReal.sub_eq_of_eq_add_rev hle hm.symm
  refine ⟨hmass, ?_, hok, fun H => ?_⟩
  · have h1 : (1 : ℝ≥0∞) = (∑' a, x.run.run (some (.ok a))) + ∑' o, Backtrack.failWeights x o := by
      rw [← hmass, SPMF.mass, tsum_option_eq, tsum_except_eq, tsum_option_eq]
      simp only [Backtrack.failWeights]
      ring
    have hle' : (∑' a, x.run.run (some (.ok a))) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_self_add h1.symm)
    rw [ofNNRat_failMass hod hon, hok]
    simp only [mul_one]
    exact ENNReal.sub_eq_of_eq_add_rev hle' h1
  · rw [(failures_spec hd hn).2.2, hfail, he, tsum_except_eq, tsum_option_eq]
    simp [Backtrack.failWeights]

/-- Related branches, run once each, have the distribution of the labelled search over them: each
success weighted by the probability that the search reaches its branch, each label by the
probability that every branch fails and their labels join to it. -/
theorem weighsSome_backtrackWithRun [SemilatticeSup ε] [DecidableEq ε]
    {ys : List (Nat × WFinite (Except ε α))} {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))}
    (hlen : ys.length = gs.length)
    (hw : ∀ i (h : i < ys.length), ys[i].1 = (gs[i]'(hlen ▸ h)).1)
    (hz : ∀ i (h : i < ys.length), ys[i].1 = 0 → ys[i].2 = Finite.empty)
    (hr : ∀ i (h : i < ys.length), ys[i].1 ≠ 0 → WeighsSome ys[i].2 ((gs[i]'(hlen ▸ h)).2 ()).run) :
    WeighsSome (backtrackWithRun ys) (Backtrack.searchWith gs.length gs none) := fun hd => by
  let zs := ys.map fun p => (p.1, oks p.2)
  have hzl : zs.length = ys.length := List.length_map _
  have hgl : gs.length = zs.length := by rw [hzl, hlen]
  have hzi : ∀ i (h : i < zs.length), zs[i] = (ys[i].1, oks ys[i].2) := fun i h => List.getElem_map ..
  obtain ⟨hSd, hFd⟩ := Finite.union_ne_undef hd
  have hRd : runWith zs (reach zs) ≠ .undef := Finite.map_ne_undef hSd
  have hdef : ∀ i (h : i < ys.length), ys[i].2 ≠ .undef := fun i h hu => by
    refine Finite.map_ne_undef (Finite.flatten_ne_undef hRd _
      (List.mem_ofFn.mpr ⟨⟨i, hzl ▸ h⟩, rfl⟩)) ?_
    show zs[i].2 = .undef
    rw [hzi i (hzl ▸ h), hu]
    rfl
  have hn : ∀ i (h : i < ys.length), Finite.Nonneg ys[i].2 := fun i h => by
    by_cases h0 : ys[i].1 = 0
    · rw [hz i h h0]
      exact Finite.nonneg_empty
    · exact (hr i h h0 (hdef i h)).1
  have hb := fun (i : Nat) (h : i < ys.length) (h0 : ys[i].1 ≠ 0) =>
    branch_spec (hr i h h0) (hdef i h)
  have hzn : ∀ i : Fin zs.length, Finite.Nonneg zs[i].2 := fun i => by
    rw [Fin.getElem_fin, hzi i i.2]
    exact (oks_spec (hdef i (hzl ▸ i.2)) (hn i _)).2.1
  let σ : Fin zs.length → (Unit → ExceptT ε (OptionT SPMF) α) := fun j =>
    (gs[j.val]'(by rw [hgl]; exact j.2)).2
  let dsZ := List.ofFn fun j : Fin zs.length => (zs[j].1, ofNNRat (failMass zs[j].2), j)
  have hbd : Backtrack.branchDataWith gs = dsZ.map fun d => (d.1, d.2.1, σ d.2.2) := by
    refine List.ext_getElem (by simp [Backtrack.branchDataWith, dsZ, hgl]) fun k h₁ h₂ => ?_
    have hk : k < ys.length := by simpa [dsZ, hzl] using h₂
    simp only [Backtrack.branchDataWith, List.getElem_map, dsZ, List.getElem_ofFn, σ,
      Fin.getElem_fin, zs]
    rw [← hw k hk]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    by_cases h0 : ys[k].1 = 0
    · simp only [h0, ↓reduceIte]
      rw [hz k hk h0, oks_empty, failMass_empty, map_one]
    · simp only [h0, ↓reduceIte]
      exact (hb k hk h0).2.1.symm
  have hfd : List.Forall₂ (fun p d => p.1 = d.1 ∧ p.2 ≠ .undef ∧ Finite.Nonneg p.2 ∧
      (p.1 = 0 → p.2 = Finite.empty) ∧
      (p.1 ≠ 0 → ∀ h, Finite.expect (failures p.2) h = ∑' o, d.2 o * h o)) ys
      (Backtrack.failData gs) := by
    refine List.forall₂_of_length_eq_of_get (by simp [Backtrack.failData, hlen]) fun i h₁ h₂ => ?_
    simp only [List.get_eq_getElem, Backtrack.failData, List.getElem_map]
    exact ⟨hw i h₁, hdef i h₁, hn i h₁, hz i h₁, fun h0 => (hb i h₁ h0).2.2.2⟩
  have hj := fun H : Option ε → ℝ≥0∞ =>
    foldl_joinStep_spec H hfd (Finite.singleton_ne_undef _) (nonneg_pure (none : Option ε))
  obtain ⟨hjd, hjn, -⟩ := hj fun _ => 0
  have hfin := bind_spec (k := fun o : Option ε => match o with
    | none => Fail.fail
    | some l => (Pure.pure (.error l) : WFinite (Except ε α))) hjd hjn fun o => by
      cases o with
      | none => exact ⟨Finite.empty_ne_undef, Finite.nonneg_empty⟩
      | some l => exact ⟨Finite.singleton_ne_undef _, nonneg_pure _⟩
  have hout : ∀ g : α → ℝ≥0∞, Finite.expect (runWith zs (reach zs)) g =
      Backtrack.mix (fun j => Finite.expect zs[j].2 g) 0 zs.length dsZ := fun g => by
    rw [expect_runWith hRd hzn, Backtrack.mix_eq_sum _ 0]
    simp only [ofNNRat_reach, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hexp : ∀ g : Except ε α → ℝ≥0∞, Finite.expect (backtrackWithRun ys) g =
      ∑' r, (Backtrack.searchWith gs.length gs none).run (some r) * g r := fun g => by
    rw [SPMF.tsum_some_eq_expect, Backtrack.expect_searchWith _ _ _ _ le_rfl, hbd,
      Backtrack.mix_reindex, backtrackWithRun]
    refine (Finite.expect_union hSd hFd g).trans ?_
    congr 1
    · rw [expect_map_ok, backtrackRun, hgl]
      refine (hout _).trans (Backtrack.mix_congr 0 _ _ fun d hd hp => ?_)
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
      simp only [Fin.getElem_fin, hzi j j.2] at hp ⊢
      rw [(hb j (hzl ▸ j.2) (Nat.pos_iff_ne_zero.mp hp)).2.2.1]
      rfl
    · let H : Option ε → ℝ≥0∞ := fun o => (o.map Except.error).elim 0 g
      have hk : (fun o : Option ε => Finite.expect (match o with
          | none => Fail.fail
          | some l => (Pure.pure (.error l) : WFinite (Except ε α))) g) = H := funext fun o => by
        cases o with
        | none => exact Finite.expect_empty g
        | some l => exact expect_pure _ g
      exact (hfin.2.2 g).trans ((congrArg _ hk).trans (((hj H).2.2).trans (expect_pure _ _)))
  refine ⟨Finite.nonneg_union (nonneg_map_ok (nonneg_runWith _ hzn)) hfin.2.1, hexp, ?_⟩
  rw [hexp]
  simp only [mul_one]
  have hm := Backtrack.mass_searchWith gs.length gs none fun p hp hp0 => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    exact (hb i (hlen ▸ hi) (by rw [hw]; omega)).1
  rw [SPMF.mass, tsum_option_eq] at hm
  rw [add_comm]
  exact hm

end WFinite

/-! ## The rules -/

namespace WeighsWith

/-- Related branches, unwrapped, are related at `WFinite` and `OptionT SPMF`. -/
theorem weighted_run {gs' : List (Nat × (Unit → ExceptT ε WFinite α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))}
    (hs : GenRel.Weighted (@WeighsWith ε) gs' gs) :
    GenRel.Weighted @WeighsSome (gs'.map fun p => (p.1, fun u => (p.2 u).run))
      (gs.map fun p => (p.1, fun u => (p.2 u).run)) := by
  induction hs with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

/-- Each branch run once at `WFinite` has the distribution of the labelled search, when their
branches are related weight for weight. -/
@[gen_rule]
theorem backtrack [SemilatticeSup ε] [DecidableEq ε] {gs' : List (Nat × (Unit → ExceptT ε WFinite α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))}
    (hs : GenRel.Weighted (@WeighsWith ε) gs' gs) :
    WeighsWith (Backtrack.backtrack gs') (Backtrack.backtrack gs) := by
  have hlen : (WFinite.runBranches (gs'.map fun p => (p.1, fun u => (p.2 u).run))).length =
      gs.length := by
    simpa [WFinite.runBranches] using congrArg List.length hs.weights
  have hw := hs.getElem
  show WeighsSome (WFinite.backtrackWithRun _) (Backtrack.searchWith gs.length gs none)
  refine WFinite.weighsSome_backtrackWithRun hlen (fun i h => ?_) (fun i h h0 => ?_)
    (fun i h h0 => ?_)
  · simp only [WFinite.runBranches, List.getElem_map]
    exact (hw i (by simpa [WFinite.runBranches] using h) (by simpa using hlen ▸ h)).1
  · simp only [WFinite.runBranches, List.getElem_map] at h0 ⊢
    simp only [h0, ↓reduceIte]
    rfl
  · simp only [WFinite.runBranches, List.getElem_map] at h0 ⊢
    simp only [h0, ↓reduceIte]
    exact (hw i (by simpa [WFinite.runBranches] using h) (by simpa using hlen ▸ h)).2

/-- Each branch weighted by its share of the weight has the distribution of the draw. -/
@[gen_rule]
theorem pick [Max ε] {gs' : List (Nat × (Unit → ExceptT ε WFinite α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))}
    (hs : GenRel.Weighted (@WeighsWith ε) gs' gs)
    {h' : 0 < Backtrack.sumWeights gs'} {h : 0 < Backtrack.sumWeights gs} :
    WeighsWith (Pick.pick gs' h') (Pick.pick gs h) := by
  show WeighsSome (Pick.pick _ (by simpa using h') : WFinite _) (Backtrack.searchWith 1 gs none)
  rw [Backtrack.searchWith_one]
  exact WeighsSome.pick (h := by simpa using h) (weighted_run hs)

end WeighsWith

end Specimen
