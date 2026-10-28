/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.Basic
public import Specimen.Enum.Weighted
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Weights Are Probabilities

A generator run at `WFinite`, where its result is defined, weighs each value exactly as its `SPMF`
distribution does. Stated as expectations, Basalt's usual form: `Weighs y x` says `y`, if defined,
has nonnegative weights under which every function has the expectation it has under `x`. It is a
`GenRel` (`genRel_weighs`), so `walk fixpoint` proves it per generator (`IsWeighed`), and
`IsWeighed.prob_eq` reads a value's probability off its entries' weights.
-/

@[expose] public section

open Lean.Order RandomChoice
open scoped ENNReal

namespace Specimen

open Basalt

namespace Finite

variable {α β : Type}

/-- Every weight is nonnegative. -/
def Nonneg : Finite (α × Rat) → Prop
  | .undef => True
  | .mk _ f => ∀ i, 0 ≤ (f i).2

/-- The expectation of `g` under the entries' weights. -/
noncomputable def expect : Finite (α × Rat) → (α → ℝ≥0∞) → ℝ≥0∞
  | .undef, _ => 0
  | .mk _ f, g => ∑ i, ENNReal.ofReal (f i).2 * g (f i).1

@[simp] theorem expect_mk {n : Nat} {f : Fin n → α × Rat} {g : α → ℝ≥0∞} :
    expect (.mk n f) g = ∑ i, ENNReal.ofReal (f i).2 * g (f i).1 := rfl

@[simp] theorem nonneg_mk {n : Nat} {f : Fin n → α × Rat} :
    Nonneg (.mk n f) ↔ ∀ i, 0 ≤ (f i).2 := Iff.rfl

theorem expect_union {x y : Finite (α × Rat)} (hx : x ≠ .undef) (hy : y ≠ .undef)
    (g : α → ℝ≥0∞) : expect (x.union y) g = expect x g + expect y g := by
  cases x with
  | undef => exact absurd rfl hx
  | mk m f =>
    cases y with
    | undef => exact absurd rfl hy
    | mk n h =>
      simp only [union, expect_mk]
      rw [Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [i.isLt]
      · refine Finset.sum_congr rfl fun i _ => ?_
        have h₁ : ¬ m + i.val < m := by omega
        simp [h₁]

theorem nonneg_union {x y : Finite (α × Rat)} (hx : Nonneg x) (hy : Nonneg y) :
    Nonneg (x.union y) := by
  cases x with
  | undef => trivial
  | mk m f =>
    cases y with
    | undef => trivial
    | mk n h =>
      intro i
      dsimp only
      split
      · exact hx _
      · exact hy _

theorem expect_flatten {xs : List (Finite (α × Rat))} (h : flatten xs ≠ .undef) (g : α → ℝ≥0∞) :
    expect (flatten xs) g = (xs.map (expect · g)).sum := by
  induction xs with
  | nil => simp [flatten, empty]
  | cons x xs ih =>
    have hu := union_ne_undef (x := x) (y := flatten xs) h
    show expect (x.union (flatten xs)) g = _
    rw [expect_union hu.1 hu.2, ih hu.2]
    simp

theorem nonneg_flatten {xs : List (Finite (α × Rat))} (h : ∀ x ∈ xs, Nonneg x) :
    Nonneg (flatten xs) := by
  induction xs with
  | nil => intro i; exact i.elim0
  | cons x xs ih =>
    exact nonneg_union (h x (List.mem_cons_self ..)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Scaling every weight by `w` scales the expectation by `w`. -/
theorem expect_scale {z : Finite (β × Rat)} {w : Rat} (hw : 0 ≤ w) (hz : Nonneg z)
    (g : β → ℝ≥0∞) :
    expect (z.map fun q => (q.1, w * q.2)) g = ENNReal.ofReal w * expect z g := by
  cases z with
  | undef => simp [map, expect]
  | mk n f =>
    simp only [map, expect_mk, Function.comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Rat.cast_mul, ENNReal.ofReal_mul (by exact_mod_cast hw), mul_assoc]

theorem nonneg_scale {z : Finite (β × Rat)} {w : Rat} (hw : 0 ≤ w) (hz : Nonneg z) :
    Nonneg (z.map fun q => (q.1, w * q.2)) := by
  cases z with
  | undef => trivial
  | mk n f => exact fun j => mul_nonneg hw (hz j)

end Finite

/-! ## The relation -/

/-- `y`, if defined, has nonnegative weights, under which every function has its expectation under
`x`. -/
def Weighs {α : Type} (y : WFinite α) (x : SPMF α) : Prop :=
  y ≠ .undef → Finite.Nonneg y ∧ ∀ g : α → ℝ≥0∞, Finite.expect y g = ∑' a, x a * g a

namespace Weighs

variable {α β : Type}

theorem pure (a : α) : Weighs (Pure.pure a) (Pure.pure a : SPMF α) := fun _ => by
  refine ⟨fun _ => by norm_num, fun g => ?_⟩
  show Finite.expect (Finite.singleton (a, 1)) g = _
  simp [Finite.singleton, ite_mul]

theorem bind {y : WFinite α} {x : SPMF α} {k' : α → WFinite β} {k : α → SPMF β}
    (hk : ∀ a, Weighs (k' a) (k a)) (hy : Weighs y x) :
    Weighs (y >>= k') (x >>= k) := fun hd => by
  change WFinite.bind y k' ≠ .undef at hd
  change Finite.Nonneg (WFinite.bind y k') ∧ ∀ g, Finite.expect (WFinite.bind y k') g = _
  obtain ⟨hyd, hkd⟩ := Finite.bind_ne_undef hd
  obtain ⟨hyn, hye⟩ := hy hyd
  have hk' : ∀ p, (y : Finite (α × Rat)).Mem p → k' p.1 ≠ .undef := fun p hp =>
    Finite.map_ne_undef (hkd p hp)
  cases y with
  | undef => exact absurd rfl hyd
  | mk n f =>
    have hmem : ∀ i, (Finite.mk n f).Mem (f i) := fun i => ⟨i, rfl⟩
    have hki := fun i => hk (f i).1 (hk' (f i) (hmem i))
    have hparts : ∀ i, (Finite.map (fun q => (q.1, (f i).2 * q.2)) (k' (f i).1)) ≠ .undef :=
      fun i => hkd (f i) (hmem i)
    show Finite.Nonneg (Finite.flatten (List.ofFn fun i => _)) ∧
      ∀ g, Finite.expect (Finite.flatten (List.ofFn fun i => _)) g = _
    refine ⟨Finite.nonneg_flatten fun z hz => ?_, fun g => ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact Finite.nonneg_scale (hyn i) (hki i).1
    · rw [Finite.expect_flatten hd, List.map_ofFn, List.sum_ofFn]
      simp only [Function.comp, Finite.expect_scale (hyn _) (hki _).1, (hki _).2]
      have := hye fun a => ∑' b, k a b * g b
      simp only [Finite.expect_mk] at this
      rw [this]
      simp only [SPMF.bind_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
      exact ENNReal.tsum_comm

theorem map {y : WFinite α} {x : SPMF α} (f : α → β) (hy : Weighs y x) :
    Weighs (f <$> y) (f <$> x) :=
  bind (fun a => pure (f a)) hy

theorem default (x : SPMF α) : Weighs Inhabited.default x := fun h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    Weighs (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := fun _ => by
  rw [show (RandomChoice.choose lo hi h : WFinite _) = (Finite.mk (hi - lo + 1)
      (fun i => (.up ⟨lo + i.val, by have := i.isLt; omega⟩,
        (1 : Rat) / ((hi : Rat) - (lo : Rat) + 1))) : WFinite _) from rfl]
  have hN : (0 : Rat) < (hi : Rat) - lo + 1 := by
    have : (lo : Rat) ≤ hi := by exact_mod_cast h
    linarith
  refine ⟨fun _ => by positivity, fun g => ?_⟩
  simp only [Finite.expect_mk, SPMF.choose_apply]
  have hc : ENNReal.ofReal (((1 : Rat) / ((hi : Rat) - lo + 1) : Rat) : ℝ)
      = 1 / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
    rw [show ((hi : Rat) - lo + 1) = ((hi - lo + 1 : ℕ) : Rat) by push_cast [Nat.cast_sub h]; ring]
    push_cast
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one]
    norm_cast
  simp only [hc, ← Finset.mul_sum, ENNReal.tsum_mul_left]
  congr 1
  let e : Fin (hi - lo + 1) ≃ ULift {x : Nat // lo ≤ x ∧ x ≤ hi} :=
    { toFun := fun i => .up ⟨lo + i.val, by have := i.isLt; omega⟩
      invFun := fun m => ⟨m.down.val - lo, by have := m.down.property; omega⟩
      left_inv := fun i => by ext; simp
      right_inv := fun m => by
        obtain ⟨⟨v, hv⟩⟩ := m
        simp only [ULift.up.injEq, Subtype.mk.injEq]
        omega }
  rw [← e.tsum_eq, tsum_fintype]
  rfl

theorem admissible (x : SPMF α) : Lean.Order.admissible fun y : WFinite α => Weighs y x :=
  Finite.admissible_defined (α := α × Rat) _

end Weighs

@[walk_rel]
theorem genRel_weighs : GenRel WFinite SPMF @Weighs where
  pure := Weighs.pure
  bind := Weighs.bind
  map := Weighs.map
  default := Weighs.default
  choose := Weighs.choose
  admissible := Weighs.admissible

/-! ## Per generator -/

/-- `gen` at `WFinite`, wherever it is defined, has `gen`'s distribution. The field is proved by
`walk fixpoint`, with a callee's law passed by its field. -/
structure IsWeighed {α : Type} (gen : {G : Type → Type} → [Gen G] → G α) : Prop where
  weighs : Weighs (gen (G := WFinite)) (gen (G := SPMF))

open Classical in
/-- A value's probability is the total weight of its entries. -/
theorem IsWeighed.prob_eq {α : Type} {gen : {G : Type → Type} → [Gen G] → G α}
    (h : IsWeighed gen) (hd : gen (G := WFinite) ≠ .undef) (a : α) :
    Finite.expect (gen (G := WFinite)) (fun b => if b = a then 1 else 0) = gen (G := SPMF) a := by
  rw [((h.weighs hd).2 _)]
  simp [mul_ite, tsum_ite_eq]

end Specimen
