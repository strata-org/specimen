/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.GenRel
public import Mathlib.Order.Lattice
public import Specimen.Enum.Laws.BacktrackCost
public import Specimen.Enum.Laws.BacktrackWith
public import Specimen.Enum.GradedWith

/-!
# Failures That Say Why, Graded by Cost

`CostEnumeratesWith y x` relates a generator with labelled failures at `ExceptT ε (CostGraded Finite)`
to its search at `ExceptT ε (OptionT SPMF.Cost)`: successes as `CostEnumeratesSome` has them, sound
per tier and complete up to cost, and below every label the search can fail with, one listed at a
tier no costlier. It is a `GenRel` (`genRel_costEnumeratesWith`) with rules for `fail`, `failWith`,
`<*>`, `backtrack` and `pick`.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen

open Basalt

/-- Every success entry of tier `n` of `y` is a success of `x` of cost `n`; every success of `x` is
listed, and every label `x` can fail with is above one listed, at some tier no costlier, if `y` is
defined up to its cost. -/
def CostEnumeratesWith {ε : Type} [LE ε] {α : Type} (y : ExceptT ε (CostGraded Finite) α)
    (x : ExceptT ε (OptionT SPMF.Cost) α) : Prop :=
  (∀ n a, (y.run n).Mem (.ok a) → (some (.ok a), n) ∈ x.run.run.support) ∧
    (∀ n a, (some (.ok a), n) ∈ x.run.run.support → (∀ m ≤ n, y.run m ≠ .undef) →
      ∃ m ≤ n, (y.run m).Mem (.ok a)) ∧
    ∀ n e, (some (.error e), n) ∈ x.run.run.support → (∀ m ≤ n, y.run m ≠ .undef) →
      ∃ m ≤ n, ∃ e', (y.run m).Mem (.error e') ∧ e' ≤ e

namespace CostEnumeratesWith

variable {ε α β : Type}

/-! ## Runs of `bind` -/

theorem mem_support_run_bind {x : ExceptT ε (OptionT SPMF.Cost) α}
    {k : α → ExceptT ε (OptionT SPMF.Cost) β} {r : Except ε β} {n : Nat} :
    (some r, n) ∈ (x >>= k).run.run.support ↔
      (∃ a n₁ n₂, (some (.ok a), n₁) ∈ x.run.run.support ∧ (some r, n₂) ∈ (k a).run.run.support ∧
        n = n₁ + n₂) ∨ ∃ e, (some (.error e), n) ∈ x.run.run.support ∧ r = .error e := by
  rw [ExceptT.run_bind, CostEnumeratesSome.mem_support_run_bind]
  constructor
  · rintro ⟨r₀, n₁, n₂, h₀, h, rfl⟩
    cases r₀ with
    | ok a => exact .inl ⟨a, n₁, n₂, h₀, h, rfl⟩
    | error e =>
      change (some r, n₂) ∈
        (Pure.pure (some (Except.error e)) : SPMF.Cost (Option (Except ε β))).support at h
      rw [SPMF.Cost.mem_support_pure_iff] at h
      obtain ⟨h, rfl⟩ := h
      exact .inr ⟨e, by rwa [Nat.add_zero], Option.some_inj.mp h⟩
  · rintro (⟨a, n₁, n₂, h₀, h, rfl⟩ | ⟨e, h₀, rfl⟩)
    · exact ⟨.ok a, n₁, n₂, h₀, h, rfl⟩
    · refine ⟨.error e, n, 0, h₀, ?_, rfl⟩
      change (some (Except.error e), 0) ∈
        (Pure.pure (some (Except.error e)) : SPMF.Cost (Option (Except ε β))).support
      rw [SPMF.Cost.mem_support_pure_iff]
      exact ⟨rfl, rfl⟩

theorem mem_pure_tier {γ : Type} {r s : γ} {n : Nat} :
    ((Pure.pure r : CostGraded Finite γ) n).Mem s ↔ s = r ∧ n = 0 := by
  change (if n = 0 then Finite.singleton r else Fail.fail).Mem s ↔ _
  split
  · exact ⟨fun h => ⟨Finite.mem_singleton.mp h, ‹_›⟩, fun h => Finite.mem_singleton.mpr h.1⟩
  · exact ⟨fun h => absurd h (Finite.not_mem_empty s), fun h => absurd h.2 ‹_›⟩

/-- A defined tier of a `bind` has every split's parts defined, and lists what they compose to and
the labels of `y` at that tier. -/
theorem bind_tier {y : ExceptT ε (CostGraded Finite) α} {k : α → ExceptT ε (CostGraded Finite) β}
    {n : Nat} (hd : (y >>= k).run n ≠ .undef) :
    (∀ j ≤ n, y.run j ≠ .undef ∧ ∀ a, (y.run j).Mem (.ok a) → (k a).run (n - j) ≠ .undef) ∧
      ∀ r, ((y >>= k).run n).Mem r ↔
        (∃ j ≤ n, ∃ a, (y.run j).Mem (.ok a) ∧ ((k a).run (n - j)).Mem r) ∨
          ∃ e, (y.run n).Mem (.error e) ∧ r = .error e := by
  rw [ExceptT.run_bind] at hd ⊢
  obtain ⟨hdef, hmem⟩ := CostGraded.bind_tier hd
  refine ⟨fun j hj => ⟨(hdef j hj).1, fun a ha => (hdef j hj).2 (.ok a) ha⟩, fun r => ?_⟩
  rw [hmem]
  constructor
  · rintro ⟨j, hj, r₀, h₀, h⟩
    cases r₀ with
    | ok a => exact .inl ⟨j, hj, a, h₀, h⟩
    | error e =>
      obtain ⟨rfl, hj0⟩ := mem_pure_tier.mp h
      obtain rfl : j = n := by omega
      exact .inr ⟨e, h₀, rfl⟩
  · rintro (⟨j, hj, a, ha, h⟩ | ⟨e, h₀, rfl⟩)
    · exact ⟨j, hj, .ok a, ha, h⟩
    · exact ⟨n, Nat.le_refl n, .error e, h₀, mem_pure_tier.mpr ⟨rfl, Nat.sub_self n⟩⟩

/-! ## The construct lemmas -/

variable [Preorder ε]

/-- Exact on both runs is enough: each label is above itself. -/
theorem of_costEnumeratesSome {y : ExceptT ε (CostGraded Finite) α}
    {x : ExceptT ε (OptionT SPMF.Cost) α} (h : CostEnumeratesSome y.run x.run) :
    CostEnumeratesWith y x :=
  ⟨fun n a => h.1 n (.ok a), fun n a => h.2 n (.ok a), fun n e he hd =>
    let ⟨m, hm, h'⟩ := h.2 n (.error e) he hd
    ⟨m, hm, e, h', le_rfl⟩⟩

theorem pure (a : α) :
    CostEnumeratesWith (Pure.pure a) (Pure.pure a : ExceptT ε (OptionT SPMF.Cost) α) :=
  of_costEnumeratesSome (CostEnumeratesSome.pure (Except.ok a))

theorem bind {y : ExceptT ε (CostGraded Finite) α} {x : ExceptT ε (OptionT SPMF.Cost) α}
    {k' : α → ExceptT ε (CostGraded Finite) β} {k : α → ExceptT ε (OptionT SPMF.Cost) β}
    (hk : ∀ a, CostEnumeratesWith (k' a) (k a)) (hy : CostEnumeratesWith y x) :
    CostEnumeratesWith (y >>= k') (x >>= k) := by
  have hya {n₁ n : Nat} {a : α} (ha : (some (.ok a), n₁) ∈ x.run.run.support) (hn : n₁ ≤ n)
      (hd : ∀ m ≤ n, (y >>= k').run m ≠ .undef) :
      ∃ m₁ ≤ n₁, (y.run m₁).Mem (.ok a) ∧ ∀ j ≤ n - n₁, (k' a).run j ≠ .undef := by
    obtain ⟨m₁, hm₁, ha'⟩ := hy.2.1 n₁ a ha fun j hj =>
      ((bind_tier (hd _ (Nat.le_refl _))).1 j (by omega)).1
    refine ⟨m₁, hm₁, ha', fun j hj => ?_⟩
    have := ((bind_tier (hd (m₁ + j) (by omega))).1 m₁ (by omega)).2 a ha'
    rwa [Nat.add_sub_cancel_left] at this
  refine ⟨fun n b hb => ?_, fun n b hb hd => ?_, fun n e he hd => ?_⟩
  · rcases ((bind_tier (Finite.ne_undef_of_mem hb)).2 _).mp hb with ⟨j, hj, a, ha, hb⟩ | ⟨_, _, h⟩
    · exact mem_support_run_bind.mpr (.inl ⟨a, j, n - j, hy.1 j a ha, (hk a).1 _ b hb, by omega⟩)
    · cases h
  · rcases mem_support_run_bind.mp hb with ⟨a, n₁, n₂, ha, hb₂, rfl⟩ | ⟨_, _, h⟩
    · obtain ⟨m₁, hm₁, ha', hkd⟩ := hya ha (by omega) hd
      obtain ⟨m₂, hm₂, hb'⟩ := (hk a).2.1 n₂ b hb₂ fun j hj => hkd j (by omega)
      refine ⟨m₁ + m₂, by omega, ((bind_tier (hd _ (by omega))).2 _).mpr (.inl ?_)⟩
      exact ⟨m₁, by omega, a, ha', by rwa [Nat.add_sub_cancel_left]⟩
    · cases h
  · rcases mem_support_run_bind.mp he with ⟨a, n₁, n₂, ha, he₂, rfl⟩ | ⟨e₀, he₀, h⟩
    · obtain ⟨m₁, hm₁, ha', hkd⟩ := hya ha (by omega) hd
      obtain ⟨m₂, hm₂, e', he', hle⟩ := (hk a).2.2 n₂ e he₂ fun j hj => hkd j (by omega)
      refine ⟨m₁ + m₂, by omega, e', ((bind_tier (hd _ (by omega))).2 _).mpr (.inl ?_), hle⟩
      exact ⟨m₁, by omega, a, ha', by rwa [Nat.add_sub_cancel_left]⟩
    · cases h
      obtain ⟨m, hm, e', he', hle⟩ := hy.2.2 n e he₀ fun j hj =>
        ((bind_tier (hd _ (Nat.le_refl _))).1 j hj).1
      exact ⟨m, hm, e', ((bind_tier (hd m hm)).2 _).mpr (.inr ⟨e', he', rfl⟩), hle⟩

theorem map {y : ExceptT ε (CostGraded Finite) α} {x : ExceptT ε (OptionT SPMF.Cost) α}
    (f : α → β) (hy : CostEnumeratesWith y x) : CostEnumeratesWith (f <$> y) (f <$> x) := by
  rw [EnumeratesWith.map_eq_bind, EnumeratesWith.map_eq_bind]
  exact bind (fun a => pure (f a)) hy

theorem default (x : ExceptT ε (OptionT SPMF.Cost) α) :
    CostEnumeratesWith (Inhabited.default : ExceptT ε (CostGraded Finite) α) x :=
  of_costEnumeratesSome (CostEnumeratesSome.default x.run)

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    CostEnumeratesWith (RandomChoice.choose lo hi h : ExceptT ε (CostGraded Finite) _)
      (RandomChoice.choose lo hi h : ExceptT ε (OptionT SPMF.Cost) _) :=
  of_costEnumeratesSome (CostEnumeratesSome.map Except.ok (CostEnumeratesSome.choose lo hi h))

/-- The limit's tiers up to a cost are those of one element of the chain, as for
`CostEnumeratesSome`. -/
theorem admissible (x : ExceptT ε (OptionT SPMF.Cost) α) :
    Lean.Order.admissible fun y : ExceptT ε (CostGraded Finite) α => CostEnumeratesWith y x := by
  show Lean.Order.admissible fun y : Nat → Finite (Except ε α) =>
    (∀ n a, (y n).Mem (.ok a) → (some (.ok a), n) ∈ x.run.run.support) ∧
      (∀ n a, (some (.ok a), n) ∈ x.run.run.support → (∀ m ≤ n, y m ≠ .undef) →
        ∃ m ≤ n, (y m).Mem (.ok a)) ∧
      ∀ n e, (some (.error e), n) ∈ x.run.run.support → (∀ m ≤ n, y m ≠ .undef) →
        ∃ m ≤ n, ∃ e', (y m).Mem (.error e') ∧ e' ≤ e
  rw [admissible_iff]
  intro c hc hall
  refine ⟨fun n a ha => ?_, fun n a hx hd => ?_, fun n e hx hd => ?_⟩
  · obtain ⟨y, hy, he⟩ := Finite.exists_chain_eq_csup hc n (Finite.ne_undef_of_mem ha)
    exact (hall y hy).1 n a (he ▸ ha)
  · obtain ⟨y, hy, he⟩ := Finite.exists_chain_eq_csup_upTo hc n hd
    obtain ⟨m, hm, ha⟩ := (hall y hy).2.1 n a hx fun m hm => he m hm ▸ hd m hm
    exact ⟨m, hm, he m hm ▸ ha⟩
  · obtain ⟨y, hy, he⟩ := Finite.exists_chain_eq_csup_upTo hc n hd
    obtain ⟨m, hm, e', ha, hle⟩ := (hall y hy).2.2 n e hx fun m hm => he m hm ▸ hd m hm
    exact ⟨m, hm, e', he m hm ▸ ha, hle⟩

theorem fail :
    CostEnumeratesWith (Fail.fail : ExceptT ε (CostGraded Finite) α)
      (Fail.fail : ExceptT ε (OptionT SPMF.Cost) α) :=
  of_costEnumeratesSome (CostEnumeratesSome.map Except.ok CostEnumeratesSome.fail)

theorem failWith (e : ε) :
    CostEnumeratesWith (FailWith.failWith e : ExceptT ε (CostGraded Finite) α)
      (FailWith.failWith e : ExceptT ε (OptionT SPMF.Cost) α) :=
  of_costEnumeratesSome (CostEnumeratesSome.pure (Except.error e : Except ε α))

theorem seq {f : ExceptT ε (CostGraded Finite) (α → β)} {f' : ExceptT ε (OptionT SPMF.Cost) (α → β)}
    {y : ExceptT ε (CostGraded Finite) α} {x : ExceptT ε (OptionT SPMF.Cost) α}
    (hf : CostEnumeratesWith f f') (hy : CostEnumeratesWith y x) :
    CostEnumeratesWith (f <*> y) (f' <*> x) :=
  bind (fun g => map g hy) hf

end CostEnumeratesWith

@[walk_rel]
theorem genRel_costEnumeratesWith {ε : Type} [Preorder ε] :
    GenRel (ExceptT ε (CostGraded Finite)) (ExceptT ε (OptionT SPMF.Cost))
      (@CostEnumeratesWith ε _) where
  pure := CostEnumeratesWith.pure
  bind := CostEnumeratesWith.bind
  map := CostEnumeratesWith.map
  default := CostEnumeratesWith.default
  choose := CostEnumeratesWith.choose
  admissible := CostEnumeratesWith.admissible

attribute [gen_rule] CostEnumeratesWith.fail CostEnumeratesWith.failWith CostEnumeratesWith.seq

/-! ## The search at `OptionT SPMF.Cost` -/

namespace Backtrack

variable {ε α : Type} [SemilatticeSup ε]

omit [SemilatticeSup ε] in
theorem mem_support_finish_cost {acc : Option ε} {r : Except ε α} {n : Nat}
    (h : (some r, n) ∈ (finish acc : OptionT SPMF.Cost (Except ε α)).run.support) :
    ∃ l, acc = some l ∧ r = .error l := by
  cases acc with
  | none =>
    change (some r, n) ∈ (Pure.pure none : SPMF.Cost (Option (Except ε α))).support at h
    rw [SPMF.Cost.mem_support_pure_iff] at h
    cases h.1
  | some l =>
    change (some r, n) ∈
      (Pure.pure (some (Except.error l)) : SPMF.Cost (Option (Except ε α))).support at h
    rw [SPMF.Cost.mem_support_pure_iff] at h
    exact ⟨l, rfl, Option.some_inj.mp h.1⟩

/-- A success of the search costs at least one more than a success of a branch of positive weight. -/
theorem mem_support_searchWith_ok_cost : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF.Cost) α))) (acc : Option ε) (a : α) (n : Nat),
    (some (.ok a), n) ∈ (searchWith fuel gs acc).run.support →
      ∃ p ∈ gs, 0 < p.1 ∧ ∃ c, (some (.ok a), c) ∈ (p.2 ()).run.run.support ∧ c + 1 ≤ n
  | _, [], acc, a, n, h | 0, _ :: _, acc, a, n, h => by
    simp only [searchWith] at h
    obtain ⟨_, _, he⟩ := mem_support_finish_cost h
    cases he
  | fuel + 1, q :: gs, acc, a, n, h => by
    simp only [searchWith, OptionT.run_mk, SPMF.Cost.mem_support_bind_iff] at h
    obtain ⟨i, n₁, n₂, hi, h, rfl⟩ := h
    rw [SPMF.Cost.mem_support_choose_iff] at hi
    subst hi
    split at h
    · obtain ⟨_, _, he⟩ := mem_support_finish_cost h
      cases he
    · rename_i k g rest hpick
      obtain ⟨hm, hk, hr⟩ := pickDrop_some hpick
      rw [SPMF.Cost.mem_support_bind_iff] at h
      obtain ⟨o, c₁, c₂, ho, h, rfl⟩ := h
      rcases o with _ | _ | a'
      · obtain ⟨p, hp, hp0, c, hpa, hc⟩ := mem_support_searchWith_ok_cost fuel rest acc a c₂ h
        exact ⟨p, hr p hp, hp0, c, hpa, by omega⟩
      · obtain ⟨p, hp, hp0, c, hpa, hc⟩ := mem_support_searchWith_ok_cost fuel rest _ a c₂ h
        exact ⟨p, hr p hp, hp0, c, hpa, by omega⟩
      · simp only [SPMF.Cost.mem_support_pure_iff, Option.some.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨(k, g), hm, hk, c₁, ho, by omega⟩

/-- A success of a branch of positive weight is a success of the search for one more choice, given
the fuel to try it. -/
theorem mem_support_searchWith_ok_cost_of_branch : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF.Cost) α))) (acc : Option ε)
    (p : Nat × (Unit → ExceptT ε (OptionT SPMF.Cost) α)), p ∈ gs → 0 < p.1 → 0 < fuel → ∀ a c,
    (some (.ok a), c) ∈ (p.2 ()).run.run.support →
      (some (.ok a), c + 1) ∈ (searchWith fuel gs acc).run.support
  | _, [], _, _, hp, _, _, _, _, _ => by simp at hp
  | 0, _ :: _, _, _, _, _, hf, _, _, _ => absurd hf (Nat.lt_irrefl 0)
  | fuel + 1, q :: gs, acc, p, hp, hk, _, a, c, h => by
    obtain ⟨n, hn, rest, hpick⟩ := exists_pickDrop hp hk
    simp only [searchWith, OptionT.run_mk, SPMF.Cost.mem_support_bind_iff]
    refine ⟨ULift.up ⟨n, Nat.zero_le _, by omega⟩, 1, c, by simp, ?_, by omega⟩
    simp only [hpick, SPMF.Cost.mem_support_bind_iff]
    exact ⟨some (.ok a), c, 0, h, by simp, rfl⟩

/-- A label the search fails with is at least the one it started with, or at least one a branch of
positive weight fails with at a cost at least one less. -/
theorem mem_support_searchWith_error_cost : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF.Cost) α))) (acc : Option ε) (e : ε) (n : Nat),
    (some (.error e), n) ∈ (searchWith fuel gs acc).run.support →
      (∃ l, acc = some l ∧ l ≤ e) ∨
        ∃ p ∈ gs, 0 < p.1 ∧ ∃ l c, (some (.error l), c) ∈ (p.2 ()).run.run.support ∧
          c + 1 ≤ n ∧ l ≤ e
  | _, [], acc, e, n, h | 0, _ :: _, acc, e, n, h => by
    simp only [searchWith] at h
    obtain ⟨l, rfl, he⟩ := mem_support_finish_cost h
    cases he
    exact .inl ⟨_, rfl, le_rfl⟩
  | fuel + 1, q :: gs, acc, e, n, h => by
    simp only [searchWith, OptionT.run_mk, SPMF.Cost.mem_support_bind_iff] at h
    obtain ⟨i, n₁, n₂, hi, h, rfl⟩ := h
    rw [SPMF.Cost.mem_support_choose_iff] at hi
    subst hi
    split at h
    · obtain ⟨l, rfl, he⟩ := mem_support_finish_cost h
      cases he
      exact .inl ⟨_, rfl, le_rfl⟩
    · rename_i k g rest hpick
      obtain ⟨hm, hk, hr⟩ := pickDrop_some hpick
      rw [SPMF.Cost.mem_support_bind_iff] at h
      obtain ⟨o, c₁, c₂, ho, h, rfl⟩ := h
      rcases o with _ | e₀ | a'
      · rcases mem_support_searchWith_error_cost fuel rest acc e c₂ h with
          hl | ⟨p, hp, hp0, l, c, hpl, hc, hle⟩
        · exact .inl hl
        · exact .inr ⟨p, hr p hp, hp0, l, c, hpl, by omega, hle⟩
      · rcases mem_support_searchWith_error_cost fuel rest _ e c₂ h with
          ⟨l, hl, hle⟩ | ⟨p, hp, hp0, l, c, hpl, hc, hle⟩
        · simp only [Option.some.injEq] at hl
          refine .inr ⟨(k, g), hm, hk, e₀, c₁, ho, by omega, le_trans ?_ hle⟩
          subst hl
          cases acc with
          | none => exact le_rfl
          | some l₀ => exact le_sup_right
        · exact .inr ⟨p, hr p hp, hp0, l, c, hpl, by omega, hle⟩
      · simp [SPMF.Cost.mem_support_pure_iff] at h

end Backtrack

/-! ## The rules -/

namespace CostEnumeratesWith

variable {ε α : Type} [SemilatticeSup ε]

/-- The union, one tier up, and the search with any fuel that can try every branch: tier `n + 1`
lists each branch of positive weight at cost `n`, which the search reaches by picking that branch
first; a success or label after other branches failed is listed at the tier of its own branch's
cost, which is cheaper. -/
theorem union {gs' : List (Nat × (Unit → ExceptT ε (CostGraded Finite) α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF.Cost) α))}
    (hs : GenRel.Weighted (@CostEnumeratesWith ε _) gs' gs) (fuel : Nat) (hfuel : ∀ p ∈ gs, 0 < fuel) :
    CostEnumeratesWith (Backtrack.backtrack gs' : ExceptT ε (CostGraded Finite) α)
      (ExceptT.mk (Backtrack.searchWith fuel gs none)) := by
  let gsR := gs'.map fun p => (p.1, fun u => (p.2 u).run)
  have hy (n : Nat) : (Backtrack.backtrack gs' : ExceptT ε (CostGraded Finite) α).run (n + 1) =
      CostGraded.backtrackTier gsR n := rfl
  have hmem {n : Nat} (hd : CostGraded.backtrackTier gsR n ≠ .undef) (r : Except ε α) :
      (CostGraded.backtrackTier gsR n).Mem r ↔ ∃ p ∈ gs', 0 < p.1 ∧ ((p.2 ()).run n).Mem r := by
    rw [CostGraded.mem_backtrackTier hd]
    simp only [gsR, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hk, h⟩
      exact ⟨p, hp, hk, h⟩
    · rintro ⟨p, hp, hk, h⟩
      exact ⟨_, ⟨p, hp, rfl⟩, hk, h⟩
  have hdef {n : Nat} (hd : CostGraded.backtrackTier gsR n ≠ .undef) {p} (hp : p ∈ gs')
      (hk : 0 < p.1) : (p.2 ()).run n ≠ .undef :=
    CostGraded.backtrackTier_branch_defined hd (List.mem_map.mpr ⟨p, hp, rfl⟩) hk
  refine ⟨fun n a ha => ?_, fun n a hx hd => ?_, fun n e hx hd => ?_⟩
  · cases n with
    | zero => exact absurd ha (Finite.not_mem_empty _)
    | succ n =>
      rw [hy] at ha
      obtain ⟨p', hp', hk, ha⟩ := (hmem (Finite.ne_undef_of_mem ha) _).mp ha
      obtain ⟨g, hg, hr⟩ := Weighted.exists_right hs hp'
      exact Backtrack.mem_support_searchWith_ok_cost_of_branch fuel gs none _ hg hk (hfuel _ hg) a n
        (hr.1 n a ha)
  · have hd' (m : Nat) (hm : m + 1 ≤ n) : CostGraded.backtrackTier gsR m ≠ .undef :=
      hy m ▸ hd (m + 1) hm
    obtain ⟨p, hp, hk, c, hpa, hc⟩ := Backtrack.mem_support_searchWith_ok_cost fuel gs none a n hx
    obtain ⟨g', hg', hr⟩ := Weighted.exists_left hs hp
    obtain ⟨m, hm, ha⟩ := hr.2.1 c a hpa fun m hm => hdef (hd' m (by omega)) hg' hk
    refine ⟨m + 1, by omega, ?_⟩
    rw [hy]
    exact (hmem (hd' m (by omega)) _).mpr ⟨(p.1, g'), hg', hk, ha⟩
  · have hd' (m : Nat) (hm : m + 1 ≤ n) : CostGraded.backtrackTier gsR m ≠ .undef :=
      hy m ▸ hd (m + 1) hm
    rcases Backtrack.mem_support_searchWith_error_cost fuel gs none e n hx with
      ⟨_, h, _⟩ | ⟨p, hp, hk, l, c, hpl, hc, hle⟩
    · cases h
    · obtain ⟨g', hg', hr⟩ := Weighted.exists_left hs hp
      obtain ⟨m, hm, e', he', hle'⟩ := hr.2.2 c l hpl fun m hm => hdef (hd' m (by omega)) hg' hk
      refine ⟨m + 1, by omega, e', ?_, le_trans hle' hle⟩
      rw [hy]
      exact (hmem (hd' m (by omega)) _).mpr ⟨(p.1, g'), hg', hk, he'⟩

@[gen_rule]
theorem backtrack {gs' : List (Nat × (Unit → ExceptT ε (CostGraded Finite) α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF.Cost) α))}
    (hs : GenRel.Weighted (@CostEnumeratesWith ε _) gs' gs) :
    CostEnumeratesWith (Backtrack.backtrack gs') (Backtrack.backtrack gs) :=
  union hs gs.length fun _ hp => List.length_pos_of_mem hp

/-- The same for the draw, the search with fuel for one branch. -/
@[gen_rule]
theorem pick {gs' : List (Nat × (Unit → ExceptT ε (CostGraded Finite) α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF.Cost) α))}
    (hs : GenRel.Weighted (@CostEnumeratesWith ε _) gs' gs)
    {h' : 0 < Backtrack.sumWeights gs'} {h : 0 < Backtrack.sumWeights gs} :
    CostEnumeratesWith (Pick.pick gs' h') (Pick.pick gs h) :=
  union hs 1 fun _ _ => Nat.one_pos

end CostEnumeratesWith

end Specimen
