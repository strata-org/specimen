/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Backtrack
public import Specimen.Enum.Laws.Fail
public import Specimen.Enum.Pick

/-!
# Backtracking Enumerates Its Branches

What `backtrack` can succeed with at `OptionT SPMF` is what its branches of positive weight can
(`mem_support_backtrack_iff`), which is what the union at `Finite` lists, so the two are related by
`EnumeratesSome` whenever their branches are (`EnumeratesSome.backtrack`); so is `pick`, the draw
without retry (`EnumeratesSome.pick`).
-/

@[expose] public section

open RandomChoice

namespace Specimen

open Basalt

namespace Backtrack

variable {α β : Type}

/-! ## `pickDrop` -/

/-- A selected entry is a member of positive weight, and the rest are members. -/
theorem pickDrop_some : ∀ {gs : List (Nat × β)} {n k : Nat} {g : β} {rest : List (Nat × β)},
    pickDrop gs n = some (k, g, rest) → (k, g) ∈ gs ∧ 0 < k ∧ ∀ p ∈ rest, p ∈ gs
  | [], _, _, _, _, h => by simp [pickDrop] at h
  | (k₀, g₀) :: gs, n, k, g, rest, h => by
    by_cases hn : n < k₀
    · simp only [pickDrop, hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self .., by omega, fun p hp => List.mem_cons_of_mem _ hp⟩
    · simp only [pickDrop, hn, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨k', g', rest'⟩, h', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨hm, hk, hr⟩ := pickDrop_some h'
      refine ⟨List.mem_cons_of_mem _ hm, hk, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hr p hp)

/-- Every member of positive weight is selected by some offset inside the total weight. -/
theorem exists_pickDrop : ∀ {gs : List (Nat × β)} {p : Nat × β}, p ∈ gs → 0 < p.1 →
    ∃ n < sumWeights gs, ∃ rest, pickDrop gs n = some (p.1, p.2, rest)
  | [], _, hp, _ => by simp at hp
  | (k, g) :: gs, p, hp, hk => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨0, by simp; omega, gs, by simp [pickDrop, hk]⟩
    · obtain ⟨n, hn, rest, h⟩ := exists_pickDrop hp hk
      refine ⟨k + n, by simp; omega, (k, g) :: rest, ?_⟩
      have : ¬ k + n < k := by omega
      simp [pickDrop, this, h]

/-! ## Successes at `OptionT SPMF` -/

/-- A success of the search is a success of a branch of positive weight. -/
theorem mem_support_search : ∀ (fuel : Nat) (gs : List (Nat × (Unit → OptionT SPMF α))) (a : α),
    some a ∈ (search fuel gs).run.support → ∃ p ∈ gs, 0 < p.1 ∧ some a ∈ (p.2 ()).run.support
  | _, [], a, h => by simp [search] at h
  | 0, _ :: _, a, h => by simp [search] at h
  | fuel + 1, q :: gs, a, h => by
    simp only [search, OptionT.run_mk, SPMF.mem_support_bind_iff] at h
    obtain ⟨n, _, h⟩ := h
    split at h
    · simp at h
    · rename_i k g rest hpick
      obtain ⟨hm, hk, hr⟩ := pickDrop_some hpick
      rw [SPMF.mem_support_bind_iff] at h
      obtain ⟨o, ho, h⟩ := h
      cases o with
      | some a' =>
        simp only [SPMF.mem_support_pure_iff, Option.some.injEq] at h
        exact ⟨(k, g), hm, hk, h ▸ ho⟩
      | none =>
        obtain ⟨p, hp, hp0, hpa⟩ := mem_support_search fuel rest a h
        exact ⟨p, hr p hp, hp0, hpa⟩

/-- A success of a branch of positive weight is a success of the search, given the fuel to try it. -/
theorem mem_support_search_of_branch : ∀ (fuel : Nat) (gs : List (Nat × (Unit → OptionT SPMF α)))
    (p : Nat × (Unit → OptionT SPMF α)), p ∈ gs → 0 < p.1 → 0 < fuel → ∀ a,
    some a ∈ (p.2 ()).run.support → some a ∈ (search fuel gs).run.support
  | _, [], _, hp, _, _, _, _ => by simp at hp
  | 0, _ :: _, _, _, _, hf, _, _ => absurd hf (Nat.lt_irrefl 0)
  | fuel + 1, q :: gs, p, hp, hk, _, a, h => by
    obtain ⟨n, hn, rest, hpick⟩ := exists_pickDrop hp hk
    simp only [search, OptionT.run_mk, SPMF.mem_support_bind_iff]
    refine ⟨ULift.up ⟨n, Nat.zero_le _, by omega⟩, by simp, ?_⟩
    simp only [hpick, SPMF.mem_support_bind_iff]
    exact ⟨some a, h, by simp⟩

/-- What `backtrack` can succeed with is what its branches of positive weight can. -/
theorem mem_support_backtrack_iff (gs : List (Nat × (Unit → OptionT SPMF α))) (a : α) :
    some a ∈ (backtrack gs : OptionT SPMF α).run.support ↔
      ∃ p ∈ gs, 0 < p.1 ∧ some a ∈ (p.2 ()).run.support := by
  refine ⟨mem_support_search gs.length gs a, fun ⟨p, hp, hk, h⟩ => ?_⟩
  exact mem_support_search_of_branch gs.length gs p hp hk (List.length_pos_of_mem hp) a h

/-! ## Entries at `Finite` -/

private theorem mem_filterMap_branch {gs : List (Nat × (Unit → Finite α))} {x : Finite α} :
    x ∈ gs.filterMap (fun p => if p.1 = 0 then none else some (p.2 ())) ↔
      ∃ p ∈ gs, 0 < p.1 ∧ p.2 () = x := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨⟨w, g⟩, hp, h⟩
    split at h
    · simp at h
    · exact ⟨(w, g), hp, by omega, Option.some.inj h⟩
  · rintro ⟨⟨w, g⟩, hp, hw, rfl⟩
    exact ⟨(w, g), hp, by simp only; split <;> first | omega | rfl⟩

/-- A defined union lists exactly its branches of positive weight's entries, each defined. -/
theorem mem_backtrack_finite {gs : List (Nat × (Unit → Finite α))}
    (hd : (backtrack gs : Finite α) ≠ .undef) (a : α) :
    (backtrack gs : Finite α).Mem a ↔ ∃ p ∈ gs, 0 < p.1 ∧ (p.2 ()).Mem a := by
  change (Finite.flatten _).Mem a ↔ _
  rw [Finite.mem_flatten hd]
  constructor
  · rintro ⟨x, hx, ha⟩
    obtain ⟨p, hp, hk, rfl⟩ := mem_filterMap_branch.mp hx
    exact ⟨p, hp, hk, ha⟩
  · rintro ⟨p, hp, hk, ha⟩
    exact ⟨p.2 (), mem_filterMap_branch.mpr ⟨p, hp, hk, rfl⟩, ha⟩

theorem backtrack_branch_defined {gs : List (Nat × (Unit → Finite α))}
    (hd : (backtrack gs : Finite α) ≠ .undef) {p : Nat × (Unit → Finite α)} (hp : p ∈ gs)
    (hk : 0 < p.1) : p.2 () ≠ .undef :=
  Finite.flatten_ne_undef hd _ (mem_filterMap_branch.mpr ⟨p, hp, hk, rfl⟩)

end Backtrack

/-! ## Successes of the draw at `OptionT SPMF` -/

namespace Pick

open Backtrack

variable {α : Type}

/-- What `pick` can succeed with is what its branches of positive weight can. -/
theorem mem_support_pick_iff (gs : List (Nat × (Unit → OptionT SPMF α))) (a : α) :
    some a ∈ (pick gs : OptionT SPMF α).run.support ↔
      ∃ p ∈ gs, 0 < p.1 ∧ some a ∈ (p.2 ()).run.support :=
  ⟨mem_support_search 1 gs a, fun ⟨p, hp, hk, h⟩ =>
    mem_support_search_of_branch 1 gs p hp hk Nat.one_pos a h⟩

end Pick

/-! ## The law -/

/-- The union at `Finite` lists exactly what `x` can succeed with, when `x`'s successes are its
branches' of positive weight and the branches are related weight for weight. -/
theorem EnumeratesSome.union {α : Type} {gs' : List (Nat × (Unit → Finite α))}
    {gs : List (Nat × (Unit → OptionT SPMF α))} {x : OptionT SPMF α}
    (hs : GenRel.Weighted @EnumeratesSome gs' gs)
    (hx : ∀ a, some a ∈ x.run.support ↔ ∃ p ∈ gs, 0 < p.1 ∧ some a ∈ (p.2 ()).run.support) :
    EnumeratesSome (Backtrack.backtrack gs') x := fun hd a => by
  rw [Backtrack.mem_backtrack_finite hd, hx]
  have hdef := fun {p} (hp : p ∈ gs') (hk : 0 < p.1) => Backtrack.backtrack_branch_defined hd hp hk
  clear hd hx
  induction hs with
  | nil => simp
  | @cons w g' g gs' gs h hs ih =>
    simp only [List.mem_cons, exists_eq_or_imp]
    refine or_congr ?_ (ih fun hp hk => hdef (List.mem_cons_of_mem _ hp) hk)
    by_cases hw : 0 < w
    · simp only [hw, true_and]
      exact h (hdef (List.mem_cons_self ..) hw) a
    · simp [hw]

/-- The union at `Finite` lists exactly what the search at `OptionT SPMF` can succeed with, when
their branches are related weight for weight. -/
@[gen_rule]
theorem EnumeratesSome.backtrack {α : Type} {gs' : List (Nat × (Unit → Finite α))}
    {gs : List (Nat × (Unit → OptionT SPMF α))} (hs : GenRel.Weighted @EnumeratesSome gs' gs) :
    EnumeratesSome (Backtrack.backtrack gs') (Backtrack.backtrack gs) :=
  union hs (Backtrack.mem_support_backtrack_iff gs)

/-- The union at `Finite` lists exactly what the draw at `OptionT SPMF` can succeed with. -/
@[gen_rule]
theorem EnumeratesSome.pick {α : Type} {gs' : List (Nat × (Unit → Finite α))}
    {gs : List (Nat × (Unit → OptionT SPMF α))} (hs : GenRel.Weighted @EnumeratesSome gs' gs) :
    EnumeratesSome (Pick.pick gs') (Pick.pick gs) :=
  union hs (Pick.mem_support_pick_iff gs)

end Specimen
