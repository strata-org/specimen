/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.Basic
public import Specimen.Enum.Graded
public import Basalt.SPMF.Cost

/-!
# A Cost-Graded Enumeration Is `SPMF.Cost`'s Support

`SPMF.Cost` pairs each value with the number of choices that produced it. Tier `n` of a generator
run at `CostGraded Finite`, where defined, is exactly the values `SPMF.Cost` gives at cost `n`:
the same notion of cost, indexed rather than tagged. `CostEnumerates` is the relation, a `GenRel`
(`genRel_costEnumerates`), proved per generator by `walk fixpoint` (`IsCostEnumerated`).
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen

open Basalt

namespace Finite

variable {β : Type}

theorem foldr_union_ne_undef {l : List Nat} {F : Nat → Finite β}
    (h : l.foldr (fun k acc => Union.union (F k) acc) (Fail.fail : Finite β) ≠ .undef) :
    ∀ k ∈ l, F k ≠ .undef := by
  induction l with
  | nil => intro _ hk; cases hk
  | cons k l ih =>
    have hu := union_ne_undef (x := F k) (y := l.foldr (fun k acc => Union.union (F k) acc) Fail.fail) h
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hu.1
    · exact ih hu.2 j hj

theorem mem_foldr_union {l : List Nat} {F : Nat → Finite β}
    (h : l.foldr (fun k acc => Union.union (F k) acc) (Fail.fail : Finite β) ≠ .undef) {b : β} :
    (l.foldr (fun k acc => Union.union (F k) acc) (Fail.fail : Finite β)).Mem b ↔
      ∃ k ∈ l, (F k).Mem b := by
  induction l with
  | nil => exact ⟨fun hb => absurd hb (not_mem_empty b), fun ⟨_, hk, _⟩ => by cases hk⟩
  | cons k l ih =>
    have hu := union_ne_undef (x := F k) (y := l.foldr (fun k acc => Union.union (F k) acc) Fail.fail) h
    show ((F k).union _).Mem b ↔ _
    rw [mem_union hu.1 hu.2, ih hu.2]
    simp

end Finite

/-! ## The relation -/

/-- Every defined tier `n` of `y` has as its entries exactly the values `x` gives at cost `n`. -/
def CostEnumerates {α : Type} (y : CostGraded Finite α) (x : SPMF.Cost α) : Prop :=
  ∀ n, y n ≠ .undef → ∀ a, (y n).Mem a ↔ (a, n) ∈ x.support

namespace CostEnumerates

variable {α β : Type}

theorem pure (a : α) : CostEnumerates (Pure.pure a) (Pure.pure a : SPMF.Cost α) := fun n _ b => by
  rw [SPMF.Cost.mem_support_pure_iff]
  cases n with
  | zero => exact (Finite.mem_singleton).trans (by simp)
  | succ n => exact ⟨fun hb => absurd hb (Finite.not_mem_empty b), fun h => absurd h.2 (by omega)⟩

theorem bind {y : CostGraded Finite α} {x : SPMF.Cost α} {k' : α → CostGraded Finite β}
    {k : α → SPMF.Cost β} (hk : ∀ a, CostEnumerates (k' a) (k a)) (hy : CostEnumerates y x) :
    CostEnumerates (y >>= k') (x >>= k) := fun n hd b => by
  change (List.range (n + 1)).foldr (fun j acc => Union.union (y j >>= fun a => k' a (n - j)) acc)
    Fail.fail ≠ .undef at hd
  change ((List.range (n + 1)).foldr (fun j acc => Union.union (y j >>= fun a => k' a (n - j)) acc)
    Fail.fail).Mem b ↔ _
  have hparts := Finite.foldr_union_ne_undef hd
  rw [Finite.mem_foldr_union hd, SPMF.Cost.mem_support_bind_iff]
  constructor
  · rintro ⟨j, hj, hb⟩
    have hj' := List.mem_range.mp hj
    obtain ⟨hyd, hkd⟩ := Finite.bind_ne_undef (hparts j hj)
    obtain ⟨a, ha, hb⟩ := (Finite.mem_bind (hparts j hj)).mp hb
    exact ⟨a, j, n - j, (hy j hyd a).mp ha, (hk a (n - j) (hkd a ha) b).mp hb, by omega⟩
  · rintro ⟨a, j, m, ha, hb, rfl⟩
    have hj : j ∈ List.range (j + m + 1) := List.mem_range.mpr (by omega)
    obtain ⟨hyd, hkd⟩ := Finite.bind_ne_undef (hparts j hj)
    have ha' := (hy j hyd a).mpr ha
    have hm : j + m - j = m := by omega
    refine ⟨j, hj, (Finite.mem_bind (hparts j hj)).mpr ⟨a, ha', ?_⟩⟩
    have hkd' := hkd a ha'
    rw [hm] at hkd' ⊢
    exact (hk a m hkd' b).mpr hb

theorem map {y : CostGraded Finite α} {x : SPMF.Cost α} (f : α → β) (hy : CostEnumerates y x) :
    CostEnumerates (f <$> y) (f <$> x) :=
  bind (fun a => pure (f a)) hy

theorem default (x : SPMF.Cost α) : CostEnumerates Inhabited.default x := fun _ h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    CostEnumerates (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := fun n hd m => by
  rw [SPMF.Cost.mem_support_choose_iff]
  change (if n = 1 then RandomChoice.choose lo hi h else Fail.fail : Finite _).Mem m ↔ _
  by_cases hn : n = 1
  · simp only [hn, ↓reduceIte, iff_true]
    exact Finite.mem_choose m
  · simp only [hn, ↓reduceIte, iff_false]
    exact Finite.not_mem_empty m

theorem admissible (x : SPMF.Cost α) :
    Lean.Order.admissible fun y : CostGraded Finite α => CostEnumerates y x := by
  show Lean.Order.admissible fun y : Nat → Finite α =>
    ∀ n, y n ≠ .undef → ∀ a, (y n).Mem a ↔ (a, n) ∈ x.support
  exact admissible_pi_apply (β := fun _ => Finite α)
    (fun n z => z ≠ .undef → ∀ a, z.Mem a ↔ (a, n) ∈ x.support)
    fun _ => Finite.admissible_defined _

end CostEnumerates

@[walk_rel]
theorem genRel_costEnumerates : GenRel (CostGraded Finite) SPMF.Cost @CostEnumerates where
  pure := CostEnumerates.pure
  bind := CostEnumerates.bind
  map := CostEnumerates.map
  default := CostEnumerates.default
  choose := CostEnumerates.choose
  admissible := CostEnumerates.admissible

/-! ## Per generator -/

/-- `gen`'s cost-graded enumeration, at every defined tier, is its `SPMF.Cost` support at that
cost. The field is proved by `walk fixpoint`. -/
structure IsCostEnumerated {α : Type} (gen : {G : Type → Type} → [Gen G] → G α) : Prop where
  costEnumerates : CostEnumerates (gen (G := CostGraded Finite)) (gen (G := SPMF.Cost))

/-- A defined tier `n` lists exactly the values the generator produces in exactly `n` choices. -/
theorem IsCostEnumerated.tier_eq {α : Type} {gen : {G : Type → Type} → [Gen G] → G α}
    (h : IsCostEnumerated gen) {n : Nat} (hd : gen (G := CostGraded Finite) n ≠ .undef) :
    {a | (gen (G := CostGraded Finite) n).Mem a} = {a | (a, n) ∈ (gen (G := SPMF.Cost)).support} :=
  Set.ext (h.costEnumerates n hd)

end Specimen
