/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.Weight
public import Specimen.Enum.WeightedBacktrack
public import Basalt.OptionT
public import Basalt.SPMF.Expect.Basic
import Basalt.SPMF.Mass

/-!
# Weights Are Probabilities, With Failure

A generator that can `fail` or `backtrack`, run at `WFinite`, where its result is defined, weighs
each success as `OptionT SPMF` does, and what the weights leave of `1` is the probability of failing
(`WeighsSome`). It is a `GenRel` (`genRel_weighsSome`), so `walk fixpoint` proves it per generator;
`WeighsSome.backtrack` is the rule for `backtrack`, whose search at `OptionT SPMF` and mixture at
`WFinite` average the same way over the branch drawn first (`Backtrack.expect_search`).
-/

@[expose] public section

open Lean.Order RandomChoice
open scoped ENNReal NNRat

namespace SPMF

variable {α : Type}

/-- An expectation over `Option α`: failure, then the successes. -/
theorem expect_option (x : SPMF (Option α)) (G : Option α → ℝ≥0∞) :
    expect x G = x none * G none + ∑' a, x (some a) * G (some a) := by
  unfold expect
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  refine ((Option.some_injective α).tsum_eq fun o ho => ?_).symm.trans (tsum_congr fun a => ?_)
  · cases o with
    | none => simp at ho
    | some a => exact ⟨a, rfl⟩
  · simp

theorem tsum_some_eq_expect (x : SPMF (Option α)) (g : α → ℝ≥0∞) :
    ∑' a, x (some a) * g a = expect x (fun o => o.elim 0 g) := by
  simp [expect_option]

theorem none_eq_expect (x : SPMF (Option α)) : x none = expect x (fun o => o.elim 1 0) := by
  simp [expect_option]

end SPMF

namespace Specimen

open Basalt

/-! ## `Finite.expect` -/

namespace Finite

variable {α β : Type}

theorem expect_congr {y : Finite (α × Rat)} {g g' : α → ℝ≥0∞}
    (h : ∀ p, y.Mem p → g p.1 = g' p.1) : expect y g = expect y g' := by
  cases y with
  | undef => rfl
  | mk n f => exact Finset.sum_congr rfl fun i _ => by rw [h (f i) ⟨i, rfl⟩]

theorem expect_add (y : Finite (α × Rat)) (g g' : α → ℝ≥0∞) :
    expect y (fun a => g a + g' a) = expect y g + expect y g' := by
  cases y with
  | undef => simp [expect]
  | mk n f => simp [mul_add, Finset.sum_add_distrib]

@[simp] theorem expect_empty (g : α → ℝ≥0∞) : expect (empty : Finite (α × Rat)) g = 0 := by
  simp [empty]

theorem nonneg_empty : Nonneg (empty : Finite (α × Rat)) := fun i => i.elim0

end Finite

namespace WFinite

variable {α β : Type}

/-- The tower rule at `WFinite`, where the bind is defined. -/
theorem nonneg_expect_bind {y : WFinite α} {k' : α → WFinite β}
    (hd : (y >>= k' : WFinite β) ≠ .undef) (hyn : Finite.Nonneg y)
    (hkn : ∀ a, k' a ≠ .undef → Finite.Nonneg (k' a)) :
    Finite.Nonneg (y >>= k' : WFinite β) ∧ ∀ g,
      Finite.expect (y >>= k' : WFinite β) g = Finite.expect y fun a => Finite.expect (k' a) g := by
  change WFinite.bind y k' ≠ .undef at hd
  change Finite.Nonneg (WFinite.bind y k') ∧ ∀ g, Finite.expect (WFinite.bind y k') g = _
  obtain ⟨hyd, hkd⟩ := Finite.bind_ne_undef hd
  cases y with
  | undef => exact absurd rfl hyd
  | mk n f =>
    have hk' : ∀ i, Finite.Nonneg (k' (f i).1) := fun i =>
      hkn _ (Finite.map_ne_undef (hkd (f i) ⟨i, rfl⟩))
    show Finite.Nonneg (Finite.flatten (List.ofFn fun i => _)) ∧
      ∀ g, Finite.expect (Finite.flatten (List.ofFn fun i => _)) g = _
    refine ⟨Finite.nonneg_flatten fun z hz => ?_, fun g => ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact Finite.nonneg_scale (hyn i) (hk' i)
    · rw [Finite.expect_flatten hd, List.map_ofFn, List.sum_ofFn]
      simp only [Function.comp, Finite.expect_scale (hyn _) (hk' _)]
      rfl

theorem expect_entries_le_one {y : WFinite α} {x : SPMF α}
    (h : ∀ g : α → ℝ≥0∞, Finite.expect y g = ∑' a, x a * g a) :
    Finite.expect y (fun _ => 1) ≤ 1 := by
  rw [h]
  simp

end WFinite


/-! ## The relation -/

/-- `y`, if defined, has nonnegative weights, under which every function has its expectation over
`x`'s successes, and the weights and `x`'s probability of failing sum to `1`. -/
def WeighsSome {α : Type} (y : WFinite α) (x : OptionT SPMF α) : Prop :=
  y ≠ .undef → Finite.Nonneg y ∧
    (∀ g : α → ℝ≥0∞, Finite.expect y g = ∑' a, (x.run : SPMF (Option α)) (some a) * g a) ∧
    Finite.expect y (fun _ => 1) + (x.run : SPMF (Option α)) none = 1

namespace WeighsSome

variable {α β : Type}

/-- The relation as one expectation over `Option α`: failure is what the weights leave of `1`. -/
theorem expect_eq {y : WFinite α} {x : OptionT SPMF α} (h : WeighsSome y x) (hd : y ≠ .undef)
    (G : Option α → ℝ≥0∞) :
    Finite.expect y (fun a => G (some a)) + (1 - Finite.expect y fun _ => 1) * G none =
      ∑' o, (x.run : SPMF (Option α)) o * G o := by
  obtain ⟨_, he, hm⟩ := h hd
  have hle : Finite.expect y (fun _ => 1) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_self_add hm)
  rw [ENNReal.sub_eq_of_eq_add_rev hle hm.symm, he, add_comm]
  exact (SPMF.expect_option _ G).symm

theorem pure (a : α) : WeighsSome (Pure.pure a) (Pure.pure a : OptionT SPMF α) := fun hd => by
  obtain ⟨hn, he⟩ := Weighs.pure a hd
  have hrun : (Pure.pure a : OptionT SPMF α).run = (Pure.pure (some a) : SPMF (Option α)) := rfl
  refine ⟨hn, fun g => ?_, ?_⟩
  · rw [he, hrun, SPMF.tsum_some_eq_expect, SPMF.expect_pure]
    simp [SPMF.pure_apply]
  · rw [he, hrun, SPMF.none_eq_expect, SPMF.expect_pure]
    simp [SPMF.pure_apply]

theorem bind {y : WFinite α} {x : OptionT SPMF α} {k' : α → WFinite β} {k : α → OptionT SPMF β}
    (hk : ∀ a, WeighsSome (k' a) (k a)) (hy : WeighsSome y x) :
    WeighsSome (y >>= k') (x >>= k) := fun hd => by
  have hbd := Finite.bind_ne_undef (show WFinite.bind y k' ≠ .undef from hd)
  obtain ⟨hyn, hye, hym⟩ := hy hbd.1
  obtain ⟨hn, hb⟩ := WFinite.nonneg_expect_bind hd hyn fun a ha => (hk a ha).1
  have hent : ∀ p, (y : Finite (α × Rat)).Mem p → k' p.1 ≠ .undef := fun p hp =>
    Finite.map_ne_undef (hbd.2 p hp)
  have hrun : (x >>= k : OptionT SPMF β).run = (x.run >>= fun o => match o with
      | some a => (k a).run
      | none => Pure.pure none : SPMF (Option β)) := rfl
  refine ⟨hn, fun g => ?_, ?_⟩
  · rw [hb, Finite.expect_congr (g' := fun a => SPMF.expect (k a).run (fun o => o.elim 0 g))
      fun p hp => ((hk p.1 (hent p hp)).2.1 g).trans (SPMF.tsum_some_eq_expect _ _), hye,
      SPMF.tsum_some_eq_expect, SPMF.tsum_some_eq_expect, hrun, SPMF.expect_bind]
    congr 1
    funext o
    cases o <;> simp
  · have hnone : (x >>= k : OptionT SPMF β).run none =
        x.run none + ∑' a, x.run (some a) * (k a).run none := by
      rw [hrun, SPMF.none_eq_expect, SPMF.expect_bind, SPMF.expect_option]
      simp [← SPMF.none_eq_expect]
    calc Finite.expect (y >>= k' : WFinite β) (fun _ => 1) + (x >>= k : OptionT SPMF β).run none
        = (Finite.expect y fun a => Finite.expect (k' a) fun _ => 1) +
            Finite.expect y (fun a => (k a).run none) + x.run none := by
          rw [hb, hnone, hye (fun a => (k a).run none), add_assoc, add_comm (x.run none)]
      _ = Finite.expect y (fun _ => 1) + x.run none := by
          refine (congrArg (· + x.run none) (Finite.expect_add y _ _).symm).trans ?_
          rw [Finite.expect_congr (g' := fun _ => 1) fun p hp => (hk p.1 (hent p hp)).2.2]
      _ = 1 := hym

theorem map {y : WFinite α} {x : OptionT SPMF α} (f : α → β) (hy : WeighsSome y x) :
    WeighsSome (f <$> y) (f <$> x) :=
  bind (fun a => pure (f a)) hy

theorem default (x : OptionT SPMF α) : WeighsSome Inhabited.default x := fun h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    WeighsSome (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := fun hd => by
  obtain ⟨hn, he⟩ := Weighs.choose lo hi h hd
  have hrun : (RandomChoice.choose lo hi h : OptionT SPMF _).run =
      ((RandomChoice.choose lo hi h : SPMF _) >>= fun a => Pure.pure (some a)) := rfl
  refine ⟨hn, fun g => ?_, ?_⟩
  · rw [he, hrun, SPMF.tsum_some_eq_expect, SPMF.expect_bind]
    simp [SPMF.expect]
  · rw [he, hrun, SPMF.none_eq_expect, SPMF.expect_bind]
    have hm : (RandomChoice.choose lo hi h : SPMF (ULift.{0} {x : Nat // lo ≤ x ∧ x ≤ hi})).mass = 1 :=
      SPMF.mass_choose lo hi h
    unfold SPMF.mass at hm
    simp [hm, SPMF.expect]

theorem admissible (x : OptionT SPMF α) :
    Lean.Order.admissible fun y : WFinite α => WeighsSome y x :=
  Finite.admissible_defined (α := α × Rat) _

theorem fail : WeighsSome (Fail.fail : WFinite α) (Fail.fail : OptionT SPMF α) := fun _ => by
  have hrun : (Fail.fail : OptionT SPMF α).run = (Pure.pure none : SPMF (Option α)) := rfl
  refine ⟨Finite.nonneg_empty, fun g => ?_, ?_⟩
  · rw [hrun, SPMF.tsum_some_eq_expect, SPMF.expect_pure]
    exact Finite.expect_empty g
  · rw [hrun, SPMF.none_eq_expect, SPMF.expect_pure]
    show Finite.expect Finite.empty _ + _ = 1
    simp

theorem seq {f : WFinite (α → β)} {f' : OptionT SPMF (α → β)} {y : WFinite α}
    {x : OptionT SPMF α} (hf : WeighsSome f f') (hy : WeighsSome y x) :
    WeighsSome (f <*> y) (f' <*> x) :=
  bind (fun g => map g hy) hf

end WeighsSome

@[walk_rel]
theorem genRel_weighsSome : GenRel WFinite (OptionT SPMF) @WeighsSome where
  pure := WeighsSome.pure
  bind := WeighsSome.bind
  map := WeighsSome.map
  default := WeighsSome.default
  choose := WeighsSome.choose
  admissible := WeighsSome.admissible

attribute [gen_rule] WeighsSome.fail WeighsSome.seq

/-! ## The average over the branch drawn first -/

namespace Backtrack

variable {α β S T ι κ : Type}

theorem mem_picks : ∀ {ds : List β} {e : β × List β}, e ∈ picks ds → e.1 ∈ ds ∧ ∀ x ∈ e.2, x ∈ ds
  | [], _, h => by simp [picks] at h
  | p :: rest, e, h => by
    simp only [picks, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨e', he', rfl⟩
    · exact ⟨List.mem_cons_self .., fun x hx => List.mem_cons_of_mem _ hx⟩
    · obtain ⟨h1, h2⟩ := mem_picks he'
      refine ⟨List.mem_cons_of_mem _ h1, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (h2 x hx)

theorem picks_map (φ : β → κ) : ∀ ds : List β,
    picks (ds.map φ) = (picks ds).map fun e => (φ e.1, e.2.map φ)
  | [] => rfl
  | p :: rest => by simp [picks, picks_map φ rest, Function.comp_def]

theorem sumWeights_map {h : Nat × β → Nat × κ} (hh : ∀ d, (h d).1 = d.1) (ds : List (Nat × β)) :
    sumWeights (ds.map h) = sumWeights ds := by
  simp [sumWeights, Function.comp_def, hh]

/-- Summing over every offset counts each branch once per unit of its weight. -/
theorem sum_range_pickDrop {M : Type} [AddCommMonoid M] (H : Option (Nat × β × List (Nat × β)) → M) :
    ∀ gs : List (Nat × β), ∑ n ∈ Finset.range (sumWeights gs), H (pickDrop gs n) =
      ((picks gs).map fun e => e.1.1 • H (some (e.1.1, e.1.2, e.2))).sum
  | [] => by simp [picks]
  | (k, g) :: rest => by
    rw [sumWeights_cons, Finset.sum_range_add]
    have h1 : ∑ x ∈ Finset.range k, H (pickDrop ((k, g) :: rest) x) = k • H (some (k, g, rest)) := by
      rw [Finset.sum_congr rfl (g := fun _ => H (some (k, g, rest))) fun x hx => by
          simp [pickDrop, Finset.mem_range.mp hx],
        Finset.sum_const, Finset.card_range]
    have h2 : ∀ x, pickDrop ((k, g) :: rest) (k + x) =
        (pickDrop rest x).map fun t => (t.1, t.2.1, (k, g) :: t.2.2) := by
      intro x
      simp only [pickDrop, show ¬ k + x < k by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    simp only [h1, h2]
    rw [sum_range_pickDrop (fun o => H (o.map fun t => (t.1, t.2.1, (k, g) :: t.2.2))) rest]
    simp [picks, Function.comp_def]

theorem sum_picks_weights [Semiring S] (ds : List (Nat × β)) :
    ((picks ds).map fun e => (e.1.1 : S)).sum = sumWeights ds := by
  have := sum_range_pickDrop (M := S) (fun _ => 1) ds
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  exact this.symm

section mix

variable [Semiring S] [Inv S]

theorem mix_zero (v : ι → S) (b : S) (ds : List (Nat × S × ι)) : mix v b 0 ds = b := rfl

theorem mix_succ (v : ι → S) (b : S) (fuel : Nat) (ds : List (Nat × S × ι)) :
    mix v b (fuel + 1) ds = if sumWeights ds = 0 then b else (sumWeights ds : S)⁻¹ *
      ((picks ds).map fun e => (e.1.1 : S) * (v e.1.2.2 + e.1.2.1 * mix v b fuel e.2)).sum := rfl

/-- Indices are only read through `v`. -/
theorem mix_reindex (σ : ι → κ) (v : κ → S) (b : S) : ∀ (fuel : Nat) (ds : List (Nat × S × ι)),
    mix v b fuel (ds.map fun d => (d.1, d.2.1, σ d.2.2)) = mix (v ∘ σ) b fuel ds
  | 0, _ => rfl
  | fuel + 1, ds => by
    have hs : sumWeights (ds.map fun d => (d.1, d.2.1, σ d.2.2)) = sumWeights ds :=
      sumWeights_map (h := fun d : Nat × S × ι => (d.1, d.2.1, σ d.2.2)) (fun _ => rfl) ds
    rw [mix_succ, mix_succ, picks_map, hs]
    simp [Function.comp_def, mix_reindex σ v b fuel]

/-- Only branches of positive weight are read. -/
theorem mix_congr {v v' : ι → S} (b : S) : ∀ (fuel : Nat) (ds : List (Nat × S × ι)),
    (∀ d ∈ ds, 0 < d.1 → v d.2.2 = v' d.2.2) → mix v b fuel ds = mix v' b fuel ds
  | 0, _, _ => rfl
  | fuel + 1, ds, h => by
    rw [mix_succ, mix_succ]
    congr 2
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    obtain ⟨h1, h2⟩ := mem_picks he
    by_cases hw : e.1.1 = 0
    · simp [hw]
    · rw [h e.1 h1 (Nat.pos_of_ne_zero hw), mix_congr b fuel e.2 fun d hd => h d (h2 d hd)]

theorem map_mix [Semiring T] [Inv T] (φ : S →+* T) (hφ : ∀ n : Nat, n ≠ 0 → φ (n : S)⁻¹ = (n : T)⁻¹)
    (v : ι → S) (b : S) : ∀ (fuel : Nat) (ds : List (Nat × S × ι)),
    φ (mix v b fuel ds) = mix (φ ∘ v) (φ b) fuel (ds.map fun d => (d.1, φ d.2.1, d.2.2))
  | 0, _ => rfl
  | fuel + 1, ds => by
    have hs : sumWeights (ds.map fun d => (d.1, φ d.2.1, d.2.2)) = sumWeights ds :=
      sumWeights_map (h := fun d : Nat × S × ι => (d.1, φ d.2.1, d.2.2)) (fun _ => rfl) ds
    rw [mix_succ, mix_succ, hs, picks_map]
    by_cases hW : sumWeights ds = 0
    · simp [hW]
    · simp only [hW, ↓reduceIte, map_mul, hφ _ hW, map_list_sum, List.map_map]
      congr 2
      refine List.map_congr_left fun e _ => ?_
      simp [map_mix φ hφ v b fuel]

end mix

section linear

variable [CommSemiring S] [Inv S] [Fintype ι] [DecidableEq ι]

omit [Inv S] [DecidableEq ι] in
private theorem list_sum_finset_sum {γ : Type} (l : List γ) (F : γ → ι → S) :
    (l.map fun x => ∑ i, F x i).sum = ∑ i, (l.map fun x => F x i).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Finset.sum_add_distrib]

/-- The average is linear: each branch's value weighted by the probability that the search reaches
it, and `b` by the probability that it reaches none. -/
theorem mix_eq_sum (v : ι → S) (b : S) : ∀ (fuel : Nat) (ds : List (Nat × S × ι)),
    mix v b fuel ds = ∑ i, v i * mix (fun j => if j = i then 1 else 0) 0 fuel ds +
      b * mix (fun _ => 0) 1 fuel ds
  | 0, _ => by simp [mix_zero]
  | fuel + 1, ds => by
    simp only [mix_succ]
    split
    · simp
    · have hδ : ∀ j, ∑ i, v i * (if j = i then (1 : S) else 0) = v j := fun j => by simp [mul_ite]
      have key : ∀ e : (Nat × S × ι) × List (Nat × S × ι),
          (e.1.1 : S) * (v e.1.2.2 + e.1.2.1 * mix v b fuel e.2) =
            ∑ i, v i * ((e.1.1 : S) * ((if e.1.2.2 = i then 1 else 0) +
              e.1.2.1 * mix (fun j => if j = i then 1 else 0) 0 fuel e.2)) +
            b * ((e.1.1 : S) * (0 + e.1.2.1 * mix (fun _ => 0) 1 fuel e.2)) := fun e => by
        have hs : ∑ i, v i * ((e.1.1 : S) * ((if e.1.2.2 = i then 1 else 0) +
              e.1.2.1 * mix (fun j => if j = i then 1 else 0) 0 fuel e.2)) =
            (e.1.1 : S) * ∑ i, v i * (if e.1.2.2 = i then 1 else 0) + (e.1.1 : S) * e.1.2.1 *
              ∑ i, v i * mix (fun j => if j = i then 1 else 0) 0 fuel e.2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hs, hδ, mix_eq_sum v b fuel e.2]
        ring
      rw [List.map_congr_left fun e _ => key e, List.sum_map_add, list_sum_finset_sum]
      simp only [List.sum_map_mul_left]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · ring

/-- The two parts of the average add: the branches' values with nothing left, and `b`. -/
theorem mix_add_base (v : ι → S) (b : S) (fuel : Nat) (ds : List (Nat × S × ι)) :
    mix v 0 fuel ds + mix (fun _ => 0) b fuel ds = mix v b fuel ds := by
  rw [mix_eq_sum v 0, mix_eq_sum (fun _ => 0) b, mix_eq_sum v b]
  simp

end linear

theorem mix_one {v : ι → ℝ≥0∞} : ∀ (fuel : Nat) (ds : List (Nat × ℝ≥0∞ × ι)),
    (∀ d ∈ ds, 0 < d.1 → v d.2.2 + d.2.1 = 1) → mix v 1 fuel ds = 1
  | 0, _, _ => rfl
  | fuel + 1, ds, h => by
    rw [mix_succ]
    split
    · rfl
    · rename_i hW
      have hl : ((picks ds).map fun e => (e.1.1 : ℝ≥0∞) * (v e.1.2.2 + e.1.2.1 * mix v 1 fuel e.2)) =
          (picks ds).map fun e => (e.1.1 : ℝ≥0∞) := List.map_congr_left fun e he => by
        obtain ⟨h1, h2⟩ := mem_picks he
        by_cases hw : e.1.1 = 0
        · simp [hw]
        · rw [mix_one fuel e.2 fun d hd => h d (h2 d hd), mul_one, h e.1 h1 (Nat.pos_of_ne_zero hw),
            mul_one]
      rw [hl, sum_picks_weights]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast hW) (ENNReal.natCast_ne_top _)

/-! ## `mix`, once per set of branches left -/

theorem length_picks : ∀ {l : List β} {e : β × List β}, e ∈ picks l → e.2.length + 1 = l.length
  | [], _, h => by simp [picks] at h
  | p :: rest, e, h => by
    simp only [picks, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨e', he', rfl⟩
    · rfl
    · simp [length_picks he']

theorem length_subMask_le : ∀ (ds : List β) (m : Nat), (subMask ds m).length ≤ ds.length
  | [], _ => le_rfl
  | d :: ds, m => by
    have := length_subMask_le ds (m / 2)
    simp only [subMask]
    split <;> simp <;> omega

theorem subMask_full : ∀ ds : List β, subMask ds (2 ^ ds.length - 1) = ds
  | [] => rfl
  | d :: ds => by
    have hp : 0 < 2 ^ ds.length := Nat.two_pow_pos _
    have h2 : 2 ^ (d :: ds).length = 2 * 2 ^ ds.length := by simp [pow_succ, mul_comm]
    simp only [subMask, h2, show (2 * 2 ^ ds.length - 1) % 2 = 1 by omega, ↓reduceIte,
      show (2 * 2 ^ ds.length - 1) / 2 = 2 ^ ds.length - 1 by omega, subMask_full ds]

theorem maskSum_congr [AddMonoid S] : ∀ (ds : List β) (m : Nat) {G G' : β → Nat → S},
    (∀ x m', m' < m → G x m' = G' x m') → maskSum ds m G = maskSum ds m G'
  | [], _, _, _, _ => rfl
  | d :: ds, m, G, G', h => by
    simp only [maskSum]
    congr 1
    · split
      · exact h d _ (by omega)
      · rfl
    · exact maskSum_congr ds (m / 2) fun x m' hm => h x _ (by omega)

theorem subMask_cons_odd {d : β} {ds : List β} {m : Nat} (hm : m % 2 = 1) :
    subMask (d :: ds) m = d :: subMask ds (m / 2) := by
  simp [subMask, hm]

theorem subMask_cons_even {d : β} {ds : List β} {m : Nat} (hm : m % 2 = 0) :
    subMask (d :: ds) m = subMask ds (m / 2) := by
  simp [subMask, hm]

/-- The picks of a mask's branches are its set bits. -/
theorem sum_picks_subMask [AddCommMonoid S] : ∀ (ds : List β) (m : Nat) (F : β → List β → S),
    ((picks (subMask ds m)).map fun e => F e.1 e.2).sum =
      maskSum ds m fun x m' => F x (subMask ds m')
  | [], _, _ => by simp [subMask, picks, maskSum]
  | d :: ds, m, F => by
    rw [maskSum]
    by_cases hm : m % 2 = 1
    · rw [subMask_cons_odd hm, ite_eq_left hm, subMask_cons_even (by omega : (m - 1) % 2 = 0),
        show (m - 1) / 2 = m / 2 by omega]
      simp only [picks, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      congr 1
      refine (sum_picks_subMask ds (m / 2) fun x r => F x (d :: r)).trans
        (congrArg _ (funext fun x => funext fun m' => ?_))
      rw [hm, subMask_cons_odd (by omega), show (2 * m' + 1) / 2 = m' by omega]
    · rw [subMask_cons_even (by omega), ite_eq_right hm, zero_add]
      refine (sum_picks_subMask ds (m / 2) F).trans
        (congrArg _ (funext fun x => funext fun m' => ?_))
      rw [subMask_cons_even (by omega), show (2 * m' + m % 2) / 2 = m' by omega]

section dp

variable [Semiring S] [Inv S]

/-- Fuel past the number of branches is never spent. -/
theorem mix_fuel (v : ι → S) (b : S) : ∀ (fuel fuel' : Nat) (ds : List (Nat × S × ι)),
    ds.length ≤ fuel → ds.length ≤ fuel' → mix v b fuel ds = mix v b fuel' ds
  | fuel, fuel', [], _, _ => by
    cases fuel <;> cases fuel' <;> rfl
  | 0, _, _ :: _, h, _ => by simp at h
  | _, 0, _ :: _, _, h' => by simp at h'
  | fuel + 1, fuel' + 1, d :: ds, h, h' => by
    rw [mix_succ, mix_succ]
    congr 2
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    have := length_picks he
    rw [mix_fuel v b fuel fuel' e.2 (by simp at h this; omega) (by simp at h' this; omega)]

theorem mixStep_eq (v : ι → S) (b : S) (ds : List (Nat × S × ι)) (T : Array S) (k : Nat)
    (hT : ∀ j < k, T[j]? = some (mix v b ds.length (subMask ds j))) :
    mixStep v b ds T k = mix v b ds.length (subMask ds k) := by
  have hle := length_subMask_le ds k
  simp only [mixStep]
  obtain h0 | ⟨n, hn⟩ : ds.length = 0 ∨ ∃ n, ds.length = n + 1 :=
    (Nat.eq_zero_or_pos _).imp id fun h => ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  · have hr : subMask ds k = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hr, h0, mix_zero]
  · rw [hn] at hT hle ⊢
    rw [mix_succ]
    by_cases hW : sumWeights (subMask ds k) = 0
    · simp only [hW, ↓reduceIte]
    · simp only [hW, ↓reduceIte]
      congr 1
      have hr : ((picks (subMask ds k)).map fun e =>
            (e.1.1 : S) * (v e.1.2.2 + e.1.2.1 * mix v b n e.2)) =
          (picks (subMask ds k)).map fun e =>
            (e.1.1 : S) * (v e.1.2.2 + e.1.2.1 * mix v b (n + 1) e.2) :=
        List.map_congr_left fun e he => by
          have := length_picks he
          rw [mix_fuel v b n (n + 1) e.2 (by omega) (by omega)]
      rw [hr, sum_picks_subMask ds k fun x r => (x.1 : S) * (v x.2.2 + x.2.1 * mix v b (n + 1) r)]
      apply maskSum_congr
      intro x m' hm
      rw [Array.getD_eq_getD_getElem?, hT m' hm, Option.getD_some]

theorem mixTable_spec (v : ι → S) (b : S) (ds : List (Nat × S × ι)) : ∀ k : Nat,
    ((List.range k).foldl (fun T m => T.push (mixStep v b ds T m)) #[]).size = k ∧
    ∀ j < k, ((List.range k).foldl (fun T m => T.push (mixStep v b ds T m)) #[])[j]? =
      some (mix v b ds.length (subMask ds j))
  | 0 => by simp
  | k + 1 => by
    obtain ⟨hs, hT⟩ := mixTable_spec v b ds k
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl (fun T m => T.push (mixStep v b ds T m)) #[] = T at hs hT
    refine ⟨by simp [hs], fun j hj => ?_⟩
    rw [Array.getElem?_push, hs]
    by_cases hjk : j = k
    · rw [ite_eq_left hjk, hjk, mixStep_eq v b ds T k hT]
    · rw [ite_eq_right hjk]
      exact hT j (by omega)

/-- The table computes `mix`. -/
theorem mixDP_eq (v : ι → S) (b : S) (ds : List (Nat × S × ι)) :
    mixDP v b ds = mix v b ds.length ds := by
  have hp : 0 < 2 ^ ds.length := Nat.two_pow_pos _
  rw [mixDP, mixTable, Array.getD_eq_getD_getElem?, (mixTable_spec v b ds _).2 _ (by omega),
    Option.getD_some, subMask_full]

end dp



theorem pickDrop_of_le : ∀ {gs : List (Nat × β)} {n : Nat}, sumWeights gs ≤ n → pickDrop gs n = none
  | [], _, _ => rfl
  | (k, g) :: rest, n, h => by
    simp only [sumWeights_cons] at h
    simp [pickDrop, show ¬ n < k by omega, pickDrop_of_le (show sumWeights rest ≤ n - k by omega)]

/-- Each branch's weight, probability of failing (`1` for a branch never drawn), and itself. -/
noncomputable def branchData (gs : List (Nat × (Unit → OptionT SPMF α))) :
    List (Nat × ℝ≥0∞ × (Unit → OptionT SPMF α)) :=
  gs.map fun p => (p.1, if p.1 = 0 then 1 else (p.2 ()).run none, p.2)

/-- One unfolding of the search: a branch drawn by weight, then on failure the search among the
rest, however the branch failed. -/
theorem expect_search (G : Option α → ℝ≥0∞) :
    ∀ (fuel : Nat) (gs : List (Nat × (Unit → OptionT SPMF α))),
    SPMF.expect (search fuel gs).run G =
      mix (fun g => ∑' a, (g ()).run (some a) * G (some a)) (G none) fuel (branchData gs)
  | fuel, [] => by
    have : (search fuel ([] : List (Nat × (Unit → OptionT SPMF α)))).run =
        (Pure.pure none : SPMF (Option α)) := by
      cases fuel <;> rfl
    rw [this, SPMF.expect_pure]
    cases fuel <;> rfl
  | 0, q :: gs => by
    rw [show (search 0 (q :: gs)).run = (Pure.pure none : SPMF (Option α)) from rfl,
      SPMF.expect_pure]
    rfl
  | fuel + 1, q :: gs => by
    simp only [search, OptionT.run_mk]
    rw [SPMF.expect_bind]
    let H : Option (Nat × (Unit → OptionT SPMF α) × List (Nat × (Unit → OptionT SPMF α))) →
        ℝ≥0∞ := fun o => SPMF.expect (match o with
          | none => Pure.pure none
          | some (_, g, rest) => (g ()).run >>= fun o => match o with
            | some a => Pure.pure (some a)
            | none => (search fuel rest).run) G
    refine Eq.trans (congrArg (SPMF.expect (choose 0 (sumWeights (q :: gs) - 1) (Nat.zero_le _)))
      (funext fun a => ?_ : _ = fun a => H (pickDrop (q :: gs) a.down.val))) ?_
    · generalize pickDrop (q :: gs) a.down.val = o
      rcases o with _ | ⟨_, g, rest⟩ <;> rfl
    have hs : sumWeights (branchData (q :: gs)) = sumWeights (q :: gs) :=
      sumWeights_map (h := fun p : Nat × (Unit → OptionT SPMF α) =>
        (p.1, if p.1 = 0 then 1 else (p.2 ()).run none, p.2)) (fun _ => rfl) _
    show Mix.average.mix 0 _ _ = _
    rw [Mix.range_average 0 _ (fun n => H (pickDrop (q :: gs) n)), mix_succ, hs]
    by_cases hW : sumWeights (q :: gs) = 0
    · simp only [hW, ↓reduceIte, Nat.zero_sub, Finset.Icc_self, Finset.sum_singleton, zero_add, Nat.cast_one,
        div_one, pickDrop_of_le (Nat.le_of_eq hW)]
      exact SPMF.expect_pure _ _
    · simp only [hW, ↓reduceIte]
      rw [show sumWeights (q :: gs) - 1 - 0 + 1 = sumWeights (q :: gs) by omega,
        show Finset.Icc 0 (sumWeights (q :: gs) - 1) = Finset.range (sumWeights (q :: gs)) by
          ext x; simp only [Finset.mem_Icc, Finset.mem_range]; omega,
        sum_range_pickDrop, div_eq_mul_inv, mul_comm, branchData, picks_map, List.map_map]
      congr 2
      refine List.map_congr_left fun e he => ?_
      by_cases hw : e.1.1 = 0
      · simp [hw]
      · simp only [Function.comp, nsmul_eq_mul, hw, ↓reduceIte]
        congr 1
        show SPMF.expect ((e.1.2 ()).run >>= _) G = _
        rw [SPMF.expect_bind, SPMF.expect_option]
        simp only [SPMF.expect_pure]
        rw [expect_search G fuel e.2, add_comm]
        rfl

end Backtrack

/-! ## The mixture at `WFinite` -/

namespace WFinite

variable {α : Type}

/-- `ℚ≥0` into `ℝ≥0∞`, as `Finite.expect` reads a weight. -/
noncomputable def ofNNRat : ℚ≥0 →+* ℝ≥0∞ where
  toFun q := ENNReal.ofReal ((q : ℚ) : ℝ)
  map_one' := by simp
  map_mul' a b := by push_cast; exact ENNReal.ofReal_mul (by positivity)
  map_zero' := by simp
  map_add' a b := by push_cast; exact ENNReal.ofReal_add (by positivity) (by positivity)

theorem ofNNRat_apply (q : ℚ≥0) : ofNNRat q = ENNReal.ofReal ((q : ℚ) : ℝ) := rfl

theorem ofNNRat_natCast_inv (n : Nat) (hn : n ≠ 0) : ofNNRat (n : ℚ≥0)⁻¹ = (n : ℝ≥0∞)⁻¹ := by
  rw [ofNNRat_apply, NNRat.coe_inv, NNRat.coe_natCast, Rat.cast_inv, Rat.cast_natCast,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn), ENNReal.ofReal_natCast]

/-- What a defined tree's weights leave of `1`, read in `ℝ≥0∞`. -/
theorem ofNNRat_failMass {y : WFinite α} (hd : y ≠ .undef) (hn : Finite.Nonneg y) :
    ofNNRat (failMass y) = 1 - Finite.expect y fun _ => 1 := by
  cases y with
  | undef => exact absurd rfl hd
  | mk n f =>
    have hmax : ∀ q : ℚ, ENNReal.ofReal ((max q 0 : ℚ) : ℝ) = ENNReal.ofReal (q : ℝ) := fun q => by
      rcases le_total q 0 with h | h
      · rw [max_eq_right h, Rat.cast_zero, ENNReal.ofReal_zero,
          ENNReal.ofReal_of_nonpos (by exact_mod_cast h)]
      · rw [max_eq_left h]
    rw [ofNNRat_apply, show ((failMass (.mk n f) : ℚ≥0) : ℚ) =
        max (1 - (List.ofFn fun i => (f i).2).sum) 0 from rfl, hmax, List.sum_ofFn, Rat.cast_sub,
      Rat.cast_one, Rat.cast_sum, ENNReal.ofReal_sub _ (Finset.sum_nonneg fun i _ => by
        exact_mod_cast hn i), ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg fun i _ => by
        exact_mod_cast hn i]
    simp

theorem nonneg_runWith {ys : List (Nat × WFinite α)} (r : Fin ys.length → ℚ≥0)
    (hn : ∀ i : Fin ys.length, Finite.Nonneg ys[i].2) : Finite.Nonneg (runWith ys r) :=
  Finite.nonneg_flatten fun z hz => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact Finite.nonneg_scale (by exact_mod_cast (r i).2) (hn i)

/-- Each branch's expectation, weighted by `r` of it. -/
theorem expect_runWith {ys : List (Nat × WFinite α)} {r : Fin ys.length → ℚ≥0}
    (hd : runWith ys r ≠ .undef) (hn : ∀ i : Fin ys.length, Finite.Nonneg ys[i].2) (g : α → ℝ≥0∞) :
    Finite.expect (runWith ys r) g =
      ∑ i : Fin ys.length, ofNNRat (r i) * Finite.expect ys[i].2 g := by
  rw [runWith, Finite.expect_flatten hd, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ =>
    Finite.expect_scale (by exact_mod_cast (r i).2) (hn i) g

/-- The probability of reaching a branch, read in `ℝ≥0∞`, is the search's. -/
theorem ofNNRat_reach (ys : List (Nat × WFinite α)) (i : Fin ys.length) :
    ofNNRat (reach ys i) = Backtrack.mix (fun j => if j = i then 1 else 0) 0 ys.length
      (List.ofFn fun j : Fin ys.length => (ys[j].1, ofNNRat (failMass ys[j].2), j)) := by
  rw [reach, Backtrack.mixDP_eq, List.length_ofFn,
    Backtrack.map_mix ofNNRat ofNNRat_natCast_inv, List.map_ofFn, map_zero]
  congr 1
  funext j
  simp only [Function.comp]
  split <;> simp

/-- The probability of one draw picking a branch, read in `ℝ≥0∞`, is the search's with fuel `1`. -/
theorem ofNNRat_pickReach (ys : List (Nat × WFinite α)) (i : Fin ys.length) :
    ofNNRat (pickReach ys i) = Backtrack.mix (fun j => if j = i then 1 else 0) 0 1
      (List.ofFn fun j : Fin ys.length => (ys[j].1, ofNNRat (failMass ys[j].2), j)) := by
  rw [pickReach, Backtrack.map_mix ofNNRat ofNNRat_natCast_inv, List.map_ofFn, map_zero]
  congr 1
  funext j
  simp only [Function.comp]
  split <;> simp

/-- Related branches, weighted by the probabilities that a search with `fuel` reaches them, are
related to that search over them. -/
theorem weighsSome_runWith {ys : List (Nat × WFinite α)}
    {gs : List (Nat × (Unit → OptionT SPMF α))} (fuel : Nat) (r : Fin ys.length → ℚ≥0)
    (hreach : ∀ i, ofNNRat (r i) = Backtrack.mix (fun j => if j = i then 1 else 0) 0 fuel
      (List.ofFn fun j : Fin ys.length => (ys[j].1, ofNNRat (failMass ys[j].2), j)))
    (hlen : ys.length = gs.length)
    (hw : ∀ i (h : i < ys.length), ys[i].1 = (gs[i]'(hlen ▸ h)).1)
    (hz : ∀ i (h : i < ys.length), ys[i].1 = 0 → ys[i].2 = Finite.empty)
    (hr : ∀ i (h : i < ys.length), ys[i].1 ≠ 0 → WeighsSome ys[i].2 ((gs[i]'(hlen ▸ h)).2 ())) :
    WeighsSome (runWith ys r) (Backtrack.search fuel gs) := fun hd => by
  have hdef : ∀ i : Fin ys.length, ys[i].2 ≠ .undef := fun i =>
    Finite.map_ne_undef (Finite.flatten_ne_undef hd _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hn : ∀ i : Fin ys.length, Finite.Nonneg ys[i].2 := fun i => by
    by_cases h0 : ys[i].1 = 0
    · show Finite.Nonneg (ys[i.val].2 : Finite (α × Rat))
      rw [hz i i.2 h0]
      exact Finite.nonneg_empty
    · exact (hr i i.2 h0 (hdef i)).1
  let σ : Fin ys.length → (Unit → OptionT SPMF α) := fun j => (gs[j.val]'(hlen ▸ j.2)).2
  have hfail : ∀ j : Fin ys.length, ys[j].1 ≠ 0 →
      ofNNRat (failMass ys[j].2) = ((σ j) ()).run none := fun j h0 => by
    obtain ⟨hn', _, hm⟩ := hr j j.2 h0 (hdef j)
    have hle : Finite.expect ys[j].2 (fun _ => 1) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_self_add hm)
    rw [ofNNRat_failMass (hdef j) hn']
    exact ENNReal.sub_eq_of_eq_add_rev hle hm.symm
  let dsP := List.ofFn fun j : Fin ys.length => (ys[j].1, ofNNRat (failMass ys[j].2), j)
  have hbd : Backtrack.branchData gs = dsP.map fun d => (d.1, d.2.1, σ d.2.2) := by
    refine List.ext_getElem (by simp [Backtrack.branchData, dsP, hlen]) fun k h₁ h₂ => ?_
    have hk : k < ys.length := by simpa [dsP] using h₂
    simp only [Backtrack.branchData, List.getElem_map, dsP, List.getElem_ofFn]
    rw [← hw k hk]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show _ = ofNNRat (failMass ys[k].2)
    by_cases h0 : ys[k].1 = 0
    · simp only [h0, ↓reduceIte]
      rw [hz k hk h0, ofNNRat_failMass (by intro h; cases h) Finite.nonneg_empty]
      simp
    · simp only [h0, ↓reduceIte]
      exact (hfail ⟨k, hk⟩ h0).symm
  have hsearch : ∀ G : Option α → ℝ≥0∞, SPMF.expect (Backtrack.search fuel gs).run G =
      Backtrack.mix (fun j => ∑' a, ((σ j) ()).run (some a) * G (some a)) (G none) fuel
        dsP := fun G => by
    rw [Backtrack.expect_search, hbd, Backtrack.mix_reindex]
    rfl
  have hout : ∀ g, Finite.expect (runWith ys r) g =
      Backtrack.mix (fun j => Finite.expect ys[j].2 g) 0 fuel dsP := fun g => by
    rw [expect_runWith hd hn, Backtrack.mix_eq_sum _ 0]
    simp only [hreach, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hmem : ∀ d ∈ dsP, 0 < d.1 → ∃ j : Fin ys.length, ys[j].1 ≠ 0 ∧ d = (ys[j].1, ofNNRat (failMass ys[j].2), j) :=
    fun d hd hp => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨j, Nat.pos_iff_ne_zero.mp hp, rfl⟩
  refine ⟨nonneg_runWith r hn, fun g => ?_, ?_⟩
  · rw [hout g, Backtrack.mix_congr (v' := fun j => ∑' a, ((σ j) ()).run (some a) * g a) 0 _ _
      fun d hd hp => ?_, SPMF.tsum_some_eq_expect, hsearch]
    · rfl
    · obtain ⟨j, h0, rfl⟩ := hmem d hd hp
      exact (hr j j.2 h0 (hdef j)).2.1 g
  · rw [hout, SPMF.none_eq_expect, hsearch]
    simp only [Option.elim, Pi.zero_apply, mul_zero, tsum_zero]
    rw [Backtrack.mix_add_base]
    refine Backtrack.mix_one _ _ fun d hd hp => ?_
    obtain ⟨j, h0, rfl⟩ := hmem d hd hp
    simp only
    rw [hfail j h0]
    exact (hr j j.2 h0 (hdef j)).2.2

end WFinite

theorem _root_.GenRel.Weighted.getElem {M N : Type → Type} {α : Type} {R : ∀ {α : Type}, M α → N α → Prop}
    {gs' : List (Nat × (Unit → M α))} {gs : List (Nat × (Unit → N α))}
    (hs : GenRel.Weighted @R gs' gs) :
    ∀ i (h' : i < gs'.length) (h : i < gs.length), gs'[i].1 = gs[i].1 ∧ R (gs'[i].2 ()) (gs[i].2 ()) := by
  induction hs with
  | nil => intro i h'; simp at h'
  | cons h hs ih =>
    intro i h' h₂
    cases i with
    | zero => exact ⟨rfl, h⟩
    | succ i => exact ih i (by simpa using h') (by simpa using h₂)

/-- Related branches, weighted by the probabilities that a search with `fuel` reaches them, are
related to that search, the branches of weight `0` not run. -/
theorem WFinite.weighsSome_runBranches {α : Type} {gs' : List (Nat × (Unit → WFinite α))}
    {gs : List (Nat × (Unit → OptionT SPMF α))} (hs : GenRel.Weighted @WeighsSome gs' gs)
    (fuel : Nat) (r : Fin (WFinite.runBranches gs').length → ℚ≥0)
    (hreach : ∀ i, WFinite.ofNNRat (r i) = Backtrack.mix (fun j => if j = i then 1 else 0) 0 fuel
      (List.ofFn fun j : Fin (WFinite.runBranches gs').length =>
        ((WFinite.runBranches gs')[j].1, WFinite.ofNNRat (WFinite.failMass (WFinite.runBranches gs')[j].2), j))) :
    WeighsSome (WFinite.runWith (WFinite.runBranches gs') r) (Backtrack.search fuel gs) := by
  have hlen : gs'.length = gs.length := by simpa using congrArg List.length hs.weights
  have hw := hs.getElem
  refine WFinite.weighsSome_runWith fuel r hreach (by simp [WFinite.runBranches, hlen])
    (fun i h => ?_) (fun i h h0 => ?_) (fun i h h0 => ?_)
  · simp only [WFinite.runBranches, List.getElem_map]
    exact (hw i _ _).1
  · simp only [WFinite.runBranches, List.getElem_map] at h0 ⊢
    simp only [h0, ↓reduceIte]
    rfl
  · simp only [WFinite.runBranches, List.getElem_map] at h0 ⊢
    simp only [h0, ↓reduceIte]
    exact (hw i _ _).2

/-- The mixture at `WFinite` has the distribution of the search at `OptionT SPMF`, when their
branches are related weight for weight. -/
@[gen_rule]
theorem WeighsSome.backtrack {α : Type} {gs' : List (Nat × (Unit → WFinite α))}
    {gs : List (Nat × (Unit → OptionT SPMF α))} (hs : GenRel.Weighted @WeighsSome gs' gs) :
    WeighsSome (Backtrack.backtrack gs') (Backtrack.backtrack gs) := by
  have hlen : (WFinite.runBranches gs').length = gs.length := by
    simpa [WFinite.runBranches] using congrArg List.length hs.weights
  show WeighsSome (WFinite.runWith _ _) (Backtrack.search gs.length gs)
  exact WFinite.weighsSome_runBranches hs _ _ fun i => by
    rw [WFinite.ofNNRat_reach]
    exact congrArg (Backtrack.mix _ _ · _) hlen

/-- Each branch weighted by its share of the weight has the distribution of the draw. -/
@[gen_rule]
theorem WeighsSome.pick {α : Type} {gs' : List (Nat × (Unit → WFinite α))}
    {gs : List (Nat × (Unit → OptionT SPMF α))} (hs : GenRel.Weighted @WeighsSome gs' gs)
    {h' : 0 < Backtrack.sumWeights gs'} {h : 0 < Backtrack.sumWeights gs} :
    WeighsSome (Pick.pick gs' h') (Pick.pick gs h) :=
  WFinite.weighsSome_runBranches hs 1 _ (WFinite.ofNNRat_pickReach _)

end Specimen
