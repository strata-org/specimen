/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.GenRel
public import Specimen.Enum.Laws.Backtrack
public import Specimen.Enum.Laws.Cost

/-!
# Backtracking, Graded by Cost

`CostEnumeratesSome y x` relates a cost-graded enumeration to a search at `OptionT SPMF.Cost`:
every entry of tier `n` is a success of cost `n`, and every success is listed at a tier no costlier.
It is a `GenRel` (`genRel_costEnumeratesSome`) with rules for `fail`, `<*>`, `backtrack` and `pick`; it is
not `CostEnumerates`, because a search that fails some branches before succeeding with another pays
for them, and that cost is not a tier.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen

open Basalt

/-! ## Successes of the search, with their cost -/

namespace Backtrack

variable {α : Type}

/-- A success of the search costs at least one more than a success of a branch of positive weight. -/
theorem mem_support_search_cost : ∀ (fuel : Nat) (gs : List (Nat × (Unit → OptionT SPMF.Cost α)))
    (a : α) (n : Nat), (some a, n) ∈ (search fuel gs).run.support →
      ∃ p ∈ gs, 0 < p.1 ∧ ∃ c, (some a, c) ∈ (p.2 ()).run.support ∧ c + 1 ≤ n
  | _, [], a, n, h => by simp [search] at h
  | 0, _ :: _, a, n, h => by simp [search] at h
  | fuel + 1, q :: gs, a, n, h => by
    simp only [search, OptionT.run_mk, SPMF.Cost.mem_support_bind_iff] at h
    obtain ⟨i, n₁, n₂, hi, h, rfl⟩ := h
    rw [SPMF.Cost.mem_support_choose_iff] at hi
    subst hi
    split at h
    · simp at h
    · rename_i k g rest hpick
      obtain ⟨hm, hk, hr⟩ := pickDrop_some hpick
      rw [SPMF.Cost.mem_support_bind_iff] at h
      obtain ⟨o, c₁, c₂, ho, h, rfl⟩ := h
      cases o with
      | some a' =>
        simp only [SPMF.Cost.mem_support_pure_iff, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨(k, g), hm, hk, c₁, ho, by omega⟩
      | none =>
        obtain ⟨p, hp, hp0, c, hpa, hc⟩ := mem_support_search_cost fuel rest a c₂ h
        exact ⟨p, hr p hp, hp0, c, hpa, by omega⟩

/-- A success of a branch of positive weight is a success of the search for one more choice, given
the fuel to try it. -/
theorem mem_support_search_cost_of_branch : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → OptionT SPMF.Cost α))) (p : Nat × (Unit → OptionT SPMF.Cost α)),
    p ∈ gs → 0 < p.1 → 0 < fuel → ∀ a c,
    (some a, c) ∈ (p.2 ()).run.support → (some a, c + 1) ∈ (search fuel gs).run.support
  | _, [], _, hp, _, _, _, _, _ => by simp at hp
  | 0, _ :: _, _, _, _, hf, _, _, _ => absurd hf (Nat.lt_irrefl 0)
  | fuel + 1, q :: gs, p, hp, hk, _, a, c, h => by
    obtain ⟨n, hn, rest, hpick⟩ := exists_pickDrop hp hk
    simp only [search, OptionT.run_mk, SPMF.Cost.mem_support_bind_iff]
    refine ⟨ULift.up ⟨n, Nat.zero_le _, by omega⟩, 1, c, by simp, ?_, by omega⟩
    simp only [hpick, SPMF.Cost.mem_support_bind_iff]
    exact ⟨some a, c, 0, h, by simp, rfl⟩

end Backtrack


/-! ## Tiers at `CostGraded Finite` -/

namespace Finite

variable {α : Type}

theorem ne_undef_of_mem {x : Finite α} {a : α} (h : x.Mem a) : x ≠ .undef := by
  rintro rfl
  exact h

/-- A limit defined at tier `m` is, there, an element of the chain. -/
theorem exists_chain_eq_csup {c : (Nat → Finite α) → Prop} (hc : chain c) (m : Nat)
    (hd : CCPO.csup hc m ≠ .undef) : ∃ y, c y ∧ y m = CCPO.csup hc m :=
  admissible_iff.mp (admissible_apply (β := fun _ => Finite α)
    (fun _ z => z ≠ .undef → ∃ y, c y ∧ y m = z) m (admissible_defined _)) c hc
    (fun y hy _ => ⟨y, hy, rfl⟩) hd

/-- A limit defined at every tier up to `n` is, there, one element of the chain. -/
theorem exists_chain_eq_csup_upTo {c : (Nat → Finite α) → Prop} (hc : chain c) :
    ∀ n, (∀ m ≤ n, CCPO.csup hc m ≠ .undef) →
      ∃ y, c y ∧ ∀ m ≤ n, y m = CCPO.csup hc m
  | 0, hd => by
    obtain ⟨y, hy, he⟩ := exists_chain_eq_csup hc 0 (hd 0 (Nat.le_refl 0))
    exact ⟨y, hy, fun m hm => by rw [Nat.le_zero.mp hm]; exact he⟩
  | n + 1, hd => by
    obtain ⟨y₁, hy₁, he₁⟩ := exists_chain_eq_csup_upTo hc n fun m hm => hd m (by omega)
    obtain ⟨y₂, hy₂, he₂⟩ := exists_chain_eq_csup hc (n + 1) (hd (n + 1) (Nat.le_refl _))
    have up {y y' : Nat → Finite α} (h : y ⊑ y') {m} (he : y m = CCPO.csup hc m)
        (hm : CCPO.csup hc m ≠ .undef) : y' m = CCPO.csup hc m :=
      he ▸ ((eq_undef_or_eq (h m)).resolve_left (he ▸ hm)).symm
    rcases hc y₁ y₂ hy₁ hy₂ with h | h
    · refine ⟨y₂, hy₂, fun m hm => ?_⟩
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact up h (he₁ m (by omega)) (hd m (by omega))
      · exact he₂
    · refine ⟨y₁, hy₁, fun m hm => ?_⟩
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact he₁ m (by omega)
      · exact up h he₂ (hd _ (Nat.le_refl _))

end Finite

namespace CostGraded

variable {G : Type → Type} {α β : Type}

theorem backtrackTier_cons [Fail G] [Union G] (q : Nat × (Unit → CostGraded G α))
    (gs : List (Nat × (Unit → CostGraded G α))) (n : Nat) :
    backtrackTier (q :: gs) n =
      if q.1 = 0 then backtrackTier gs n else Union.union (q.2 () n) (backtrackTier gs n) := rfl

theorem backtrackTier_branch_defined {gs : List (Nat × (Unit → CostGraded Finite α))} {n : Nat}
    (hd : backtrackTier gs n ≠ .undef) {p : Nat × (Unit → CostGraded Finite α)} (hp : p ∈ gs)
    (hk : 0 < p.1) : p.2 () n ≠ .undef := by
  induction gs with
  | nil => cases hp
  | cons q gs ih =>
    rw [backtrackTier_cons] at hd
    by_cases hq : q.1 = 0
    · simp only [hq, ↓reduceIte] at hd
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · exact ih hd hp
    · simp only [hq, ↓reduceIte] at hd
      have hu := Finite.union_ne_undef hd
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hu.1
      · exact ih hu.2 hp

theorem mem_backtrackTier {gs : List (Nat × (Unit → CostGraded Finite α))} {n : Nat}
    (hd : backtrackTier gs n ≠ .undef) (a : α) :
    (backtrackTier gs n).Mem a ↔ ∃ p ∈ gs, 0 < p.1 ∧ (p.2 () n).Mem a := by
  induction gs with
  | nil => exact ⟨fun h => absurd h (Finite.not_mem_empty a), fun ⟨_, hp, _⟩ => by cases hp⟩
  | cons q gs ih =>
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [backtrackTier_cons] at hd ⊢
    by_cases hq : q.1 = 0
    · simp only [hq, ↓reduceIte] at hd ⊢
      rw [ih hd]
      simp
    · simp only [hq, ↓reduceIte] at hd ⊢
      have hu := Finite.union_ne_undef hd
      change (Finite.union _ _).Mem a ↔ _
      rw [Finite.mem_union hu.1 hu.2, ih hu.2]
      simp only [Nat.pos_iff_ne_zero.mpr hq, true_and]

/-- A defined tier of a `bind` has every split's parts defined, and lists what they compose to. -/
theorem bind_tier {y : CostGraded Finite α} {k : α → CostGraded Finite β} {n : Nat}
    (hd : (y >>= k) n ≠ .undef) :
    (∀ j ≤ n, y j ≠ .undef ∧ ∀ a, (y j).Mem a → k a (n - j) ≠ .undef) ∧
      ∀ b, ((y >>= k) n).Mem b ↔ ∃ j ≤ n, ∃ a, (y j).Mem a ∧ (k a (n - j)).Mem b := by
  change (List.range (n + 1)).foldr (fun j acc => Union.union (y j >>= fun a => k a (n - j)) acc)
    Fail.fail ≠ .undef at hd
  have hparts := Finite.foldr_union_ne_undef hd
  have hj {j} (h : j ≤ n) : j ∈ List.range (n + 1) := List.mem_range.mpr (by omega)
  refine ⟨fun j h => Finite.bind_ne_undef (hparts j (hj h)), fun b => ?_⟩
  change ((List.range (n + 1)).foldr (fun j acc => Union.union (y j >>= fun a => k a (n - j)) acc)
    Fail.fail).Mem b ↔ _
  rw [Finite.mem_foldr_union hd]
  constructor
  · rintro ⟨j, hjn, hb⟩
    exact ⟨j, by have := List.mem_range.mp hjn; omega, (Finite.mem_bind (hparts j hjn)).mp hb⟩
  · rintro ⟨j, hjn, hb⟩
    exact ⟨j, hj hjn, (Finite.mem_bind (hparts j (hj hjn))).mpr hb⟩

end CostGraded

/-! ## The relation -/

/-- Every entry of tier `n` of `y` is a success of `x` of cost `n`, and every success of `x` is
listed at some tier no costlier, if `y` is defined up to its cost. -/
def CostEnumeratesSome {α : Type} (y : CostGraded Finite α) (x : OptionT SPMF.Cost α) : Prop :=
  (∀ n a, (y n).Mem a → (some a, n) ∈ x.run.support) ∧
    ∀ n a, (some a, n) ∈ x.run.support → (∀ m ≤ n, y m ≠ .undef) → ∃ m ≤ n, (y m).Mem a

namespace CostEnumeratesSome

variable {α β : Type}

theorem mem_support_run_bind {x : OptionT SPMF.Cost α} {k : α → OptionT SPMF.Cost β} {b : β}
    {n : Nat} : (some b, n) ∈ (x >>= k).run.support ↔
      ∃ a n₁ n₂, (some a, n₁) ∈ x.run.support ∧ (some b, n₂) ∈ (k a).run.support ∧ n = n₁ + n₂ := by
  have : (x >>= k).run = (x.run >>= fun o => match o with
      | some a => (k a).run
      | none => Pure.pure none : SPMF.Cost (Option β)) := rfl
  rw [this, SPMF.Cost.mem_support_bind_iff]
  constructor
  · rintro ⟨o, n₁, n₂, ho, hb, rfl⟩
    cases o with
    | none => simp at hb
    | some a => exact ⟨a, n₁, n₂, ho, hb, rfl⟩
  · rintro ⟨a, n₁, n₂, ha, hb, rfl⟩
    exact ⟨some a, n₁, n₂, ha, hb, rfl⟩

theorem pure (a : α) :
    CostEnumeratesSome (Pure.pure a) (Pure.pure a : OptionT SPMF.Cost α) := by
  have hrun : (Pure.pure a : OptionT SPMF.Cost α).run = Pure.pure (some a) := rfl
  have hy (n : Nat) : (Pure.pure a : CostGraded Finite α) n =
      if n = 0 then Pure.pure a else Fail.fail := rfl
  refine ⟨fun n b hb => ?_, fun n b hb _ => ?_⟩
  · rw [hy] at hb
    rw [hrun, SPMF.Cost.mem_support_pure_iff]
    split at hb
    · exact ⟨congrArg some (Finite.mem_singleton.mp hb), ‹_›⟩
    · exact absurd hb (Finite.not_mem_empty b)
  · rw [hrun, SPMF.Cost.mem_support_pure_iff] at hb
    obtain ⟨hb, rfl⟩ := hb
    refine ⟨0, Nat.le_refl 0, ?_⟩
    rw [hy]
    exact Finite.mem_singleton.mpr (Option.some_inj.mp hb)

theorem bind {y : CostGraded Finite α} {x : OptionT SPMF.Cost α} {k' : α → CostGraded Finite β}
    {k : α → OptionT SPMF.Cost β} (hk : ∀ a, CostEnumeratesSome (k' a) (k a))
    (hy : CostEnumeratesSome y x) : CostEnumeratesSome (y >>= k') (x >>= k) := by
  refine ⟨fun n b hb => ?_, fun n b hb hd => ?_⟩
  · obtain ⟨j, hj, a, ha, hb⟩ := ((CostGraded.bind_tier (Finite.ne_undef_of_mem hb)).2 b).mp hb
    exact mem_support_run_bind.mpr ⟨a, j, n - j, hy.1 j a ha, (hk a).1 _ b hb, by omega⟩
  · obtain ⟨a, n₁, n₂, ha, hb₂, rfl⟩ := mem_support_run_bind.mp hb
    obtain ⟨m₁, hm₁, ha'⟩ := hy.2 n₁ a ha fun j hj =>
      ((CostGraded.bind_tier (hd _ (Nat.le_refl _))).1 j (by omega)).1
    obtain ⟨m₂, hm₂, hb'⟩ := (hk a).2 n₂ b hb₂ fun j hj => by
      have := ((CostGraded.bind_tier (hd (m₁ + j) (by omega))).1 m₁ (by omega)).2 a ha'
      rwa [Nat.add_sub_cancel_left] at this
    refine ⟨m₁ + m₂, by omega, ((CostGraded.bind_tier (hd _ (by omega))).2 b).mpr ?_⟩
    exact ⟨m₁, by omega, a, ha', by rwa [Nat.add_sub_cancel_left]⟩

theorem map {y : CostGraded Finite α} {x : OptionT SPMF.Cost α} (f : α → β)
    (hy : CostEnumeratesSome y x) : CostEnumeratesSome (f <$> y) (f <$> x) :=
  bind (fun a => pure (f a)) hy

theorem default (x : OptionT SPMF.Cost α) : CostEnumeratesSome Inhabited.default x :=
  ⟨fun _ a h => absurd h (Finite.not_mem_undef a), fun _ _ _ hd => absurd rfl (hd 0 (Nat.zero_le _))⟩

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    CostEnumeratesSome (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := by
  have hrun : (RandomChoice.choose lo hi h : OptionT SPMF.Cost _).run =
      ((RandomChoice.choose lo hi h : SPMF.Cost _) >>= fun a => Pure.pure (some a)) := rfl
  have hy (n : Nat) : (RandomChoice.choose lo hi h : CostGraded Finite _) n =
      if n = 1 then RandomChoice.choose lo hi h else Fail.fail := rfl
  refine ⟨fun n m hm => ?_, fun n m hm _ => ?_⟩
  · rw [hy] at hm
    split at hm
    · subst n
      rw [hrun, SPMF.Cost.mem_support_bind_iff]
      exact ⟨m, 1, 0, by simp, by simp, rfl⟩
    · exact absurd hm (Finite.not_mem_empty m)
  · rw [hrun, SPMF.Cost.mem_support_bind_iff] at hm
    obtain ⟨m', n₁, n₂, hm', hb, rfl⟩ := hm
    rw [SPMF.Cost.mem_support_choose_iff] at hm'
    rw [SPMF.Cost.mem_support_pure_iff] at hb
    obtain ⟨hb, rfl⟩ := hb
    refine ⟨1, by omega, ?_⟩
    rw [hy]
    exact Finite.mem_choose m

/-- The limit's tiers up to a success's cost are those of one element of the chain, so the success
is listed there. -/
theorem admissible (x : OptionT SPMF.Cost α) :
    Lean.Order.admissible fun y : CostGraded Finite α => CostEnumeratesSome y x := by
  show Lean.Order.admissible fun y : Nat → Finite α =>
    (∀ n a, (y n).Mem a → (some a, n) ∈ x.run.support) ∧
      ∀ n a, (some a, n) ∈ x.run.support → (∀ m ≤ n, y m ≠ .undef) → ∃ m ≤ n, (y m).Mem a
  rw [admissible_iff]
  intro c hc hall
  refine ⟨fun n a ha => ?_, fun n a hx hd => ?_⟩
  · obtain ⟨y, hy, he⟩ := Finite.exists_chain_eq_csup hc n (Finite.ne_undef_of_mem ha)
    exact (hall y hy).1 n a (he ▸ ha)
  · obtain ⟨y, hy, he⟩ := Finite.exists_chain_eq_csup_upTo hc n hd
    obtain ⟨m, hm, ha⟩ := (hall y hy).2 n a hx fun m hm => he m hm ▸ hd m hm
    exact ⟨m, hm, he m hm ▸ ha⟩

theorem fail : CostEnumeratesSome (Fail.fail : CostGraded Finite α) (Fail.fail : OptionT SPMF.Cost α) := by
  have hrun : (Fail.fail : OptionT SPMF.Cost α).run = Pure.pure none := rfl
  refine ⟨fun _ a h => absurd h (Finite.not_mem_empty a), fun _ a h _ => ?_⟩
  rw [hrun, SPMF.Cost.mem_support_pure_iff] at h
  cases h.1

theorem seq {f : CostGraded Finite (α → β)} {f' : OptionT SPMF.Cost (α → β)}
    {y : CostGraded Finite α} {x : OptionT SPMF.Cost α} (hf : CostEnumeratesSome f f')
    (hy : CostEnumeratesSome y x) : CostEnumeratesSome (f <*> y) (f' <*> x) :=
  bind (fun g => map g hy) hf

/-- Defined up to `n`, `y` lists exactly the successes of `x` of cost at most `n`, each at some tier
no costlier. -/
theorem mem_upTo_iff {y : CostGraded Finite α} {x : OptionT SPMF.Cost α}
    (h : CostEnumeratesSome y x) {n : Nat} (hd : ∀ m ≤ n, y m ≠ .undef) (a : α) :
    (∃ c ≤ n, (some a, c) ∈ x.run.support) ↔ ∃ m ≤ n, (y m).Mem a := by
  constructor
  · rintro ⟨c, hc, ha⟩
    obtain ⟨m, hm, ha⟩ := h.2 c a ha fun m hm => hd m (by omega)
    exact ⟨m, by omega, ha⟩
  · rintro ⟨m, hm, ha⟩
    exact ⟨m, hm, h.1 m a ha⟩

/-- Defined up to `n`, `y` has an entry at a tier up to `n` exactly when `x` can succeed within `n`
choices: a search to a cost bound, checked by enumerating. -/
theorem succeeds_upTo_iff {y : CostGraded Finite α} {x : OptionT SPMF.Cost α}
    (h : CostEnumeratesSome y x) {n : Nat} (hd : ∀ m ≤ n, y m ≠ .undef) :
    (∃ a, ∃ c ≤ n, (some a, c) ∈ x.run.support) ↔ ∃ m ≤ n, ∃ a, (y m).Mem a := by
  simp only [h.mem_upTo_iff hd]
  exact ⟨fun ⟨a, m, hm, ha⟩ => ⟨m, hm, a, ha⟩, fun ⟨m, hm, a, ha⟩ => ⟨a, m, hm, ha⟩⟩

theorem mem_of_get?_eq_some {z : Finite α} {i : Nat} {a : α} (h : z.get? i = some a) : z.Mem a := by
  cases z with
  | undef => cases h
  | mk k f =>
    simp only [Finite.get?] at h
    split at h
    · exact ⟨_, Option.some.inj h⟩
    · cases h

theorem get?_zero_ne_none {z : Finite α} {a : α} (h : z.Mem a) : z.get? 0 ≠ none := by
  cases z with
  | undef => exact absurd h (Finite.not_mem_undef a)
  | mk k f =>
    obtain ⟨i, _⟩ := h
    simp only [Finite.get?]
    rw [dite_eq_left (by have := i.isLt; omega)]
    exact Option.some_ne_none _

/-- What `firstUpTo?` finds is a success within the budget. -/
theorem firstUpTo?_sound {y : CostGraded Finite α} {x : OptionT SPMF.Cost α}
    (h : CostEnumeratesSome y x) {b : Nat} {a : α} (hf : y.firstUpTo? b = some a) :
    ∃ c ≤ b, (some a, c) ∈ x.run.support := by
  obtain ⟨n, hn, hg⟩ := List.exists_of_findSome?_eq_some hf
  exact ⟨n, Nat.lt_succ_iff.mp (List.mem_range.mp hn), h.1 n a (mem_of_get?_eq_some hg)⟩

/-- If `firstUpTo?` finds nothing in defined tiers, nothing succeeds within the budget. -/
theorem firstUpTo?_complete {y : CostGraded Finite α} {x : OptionT SPMF.Cost α}
    (h : CostEnumeratesSome y x) {b : Nat} (hd : ∀ m ≤ b, y m ≠ .undef)
    (hf : y.firstUpTo? b = none) (a : α) {c : Nat} (hc : c ≤ b) : (some a, c) ∉ x.run.support := by
  intro hx
  obtain ⟨m, hm, ha⟩ := h.2 c a hx fun m hm => hd m (by omega)
  exact get?_zero_ne_none ha (List.findSome?_eq_none_iff.mp hf m (List.mem_range.mpr (by omega)))

end CostEnumeratesSome

@[walk_rel]
theorem genRel_costEnumeratesSome :
    GenRel (CostGraded Finite) (OptionT SPMF.Cost) @CostEnumeratesSome where
  pure := CostEnumeratesSome.pure
  bind := CostEnumeratesSome.bind
  map := CostEnumeratesSome.map
  default := CostEnumeratesSome.default
  choose := CostEnumeratesSome.choose
  admissible := CostEnumeratesSome.admissible

attribute [gen_rule] CostEnumeratesSome.fail CostEnumeratesSome.seq

/-! ## Backtracking -/

/-- The union of the branches, one tier up, lists a cost-graded `x` complete up to cost, when every
success of `x` costs more than a success of a branch of positive weight, and every such success is
one of `x`'s for one more choice. -/
theorem CostEnumeratesSome.union {α : Type} {gs' : List (Nat × (Unit → CostGraded Finite α))}
    {gs : List (Nat × (Unit → OptionT SPMF.Cost α))} {x : OptionT SPMF.Cost α}
    (hs : GenRel.Weighted @CostEnumeratesSome gs' gs)
    (hup : ∀ a n, (some a, n) ∈ x.run.support →
      ∃ p ∈ gs, 0 < p.1 ∧ ∃ c, (some a, c) ∈ (p.2 ()).run.support ∧ c + 1 ≤ n)
    (hdown : ∀ p ∈ gs, 0 < p.1 → ∀ a c, (some a, c) ∈ (p.2 ()).run.support →
      (some a, c + 1) ∈ x.run.support) :
    CostEnumeratesSome (Backtrack.backtrack gs') x := by
  have hy (n : Nat) : (Backtrack.backtrack gs' : CostGraded Finite α) (n + 1) =
      CostGraded.backtrackTier gs' n := rfl
  refine ⟨fun n a ha => ?_, fun n a hx' hd => ?_⟩
  · cases n with
    | zero => exact absurd ha (Finite.not_mem_empty a)
    | succ n =>
      rw [hy] at ha
      obtain ⟨p', hp', hk, ha⟩ :=
        (CostGraded.mem_backtrackTier (Finite.ne_undef_of_mem ha) a).mp ha
      obtain ⟨g, hg, hr⟩ := Weighted.exists_right hs hp'
      exact hdown _ hg hk a n (hr.1 n a ha)
  · obtain ⟨p, hp, hk, c, hpa, hc⟩ := hup a n hx'
    obtain ⟨g', hg', hr⟩ := Weighted.exists_left hs hp
    have hdef (m : Nat) (hm : m + 1 ≤ n) : CostGraded.backtrackTier gs' m ≠ .undef :=
      hy m ▸ hd (m + 1) hm
    obtain ⟨m, hm, ha⟩ := hr.2 c a hpa fun m hm =>
      CostGraded.backtrackTier_branch_defined (hdef m (by omega)) hg' hk
    refine ⟨m + 1, by omega, ?_⟩
    rw [hy, CostGraded.mem_backtrackTier (hdef m (by omega))]
    exact ⟨(p.1, g'), hg', hk, ha⟩

/-- Tier `n + 1` of the union lists the successes of each branch of positive weight at cost `n`,
which the search reaches by picking that branch first; a success after other branches failed is
listed at the tier of its own branch's cost, which is cheaper. -/
@[gen_rule]
theorem CostEnumeratesSome.backtrack {α : Type} {gs' : List (Nat × (Unit → CostGraded Finite α))}
    {gs : List (Nat × (Unit → OptionT SPMF.Cost α))}
    (hs : GenRel.Weighted @CostEnumeratesSome gs' gs) :
    CostEnumeratesSome (Backtrack.backtrack gs') (Backtrack.backtrack gs) :=
  union hs (Backtrack.mem_support_search_cost _ gs) fun p hp hk =>
    Backtrack.mem_support_search_cost_of_branch _ gs p hp hk (List.length_pos_of_mem hp)

/-- With no retry, the draw reaches each success at exactly one more than its branch's cost. -/
@[gen_rule]
theorem CostEnumeratesSome.pick {α : Type} {gs' : List (Nat × (Unit → CostGraded Finite α))}
    {gs : List (Nat × (Unit → OptionT SPMF.Cost α))}
    (hs : GenRel.Weighted @CostEnumeratesSome gs' gs)
    {h' : 0 < Backtrack.sumWeights gs'} {h : 0 < Backtrack.sumWeights gs} :
    CostEnumeratesSome (Pick.pick gs' h') (Pick.pick gs h) :=
  union hs (Backtrack.mem_support_search_cost 1 gs) fun p hp hk =>
    Backtrack.mem_support_search_cost_of_branch 1 gs p hp hk Nat.one_pos

end Specimen
