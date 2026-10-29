/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.GenRel
public import Mathlib.Order.Lattice
public import Specimen.Enum.BacktrackWith
public import Specimen.Enum.Laws.Backtrack

/-!
# Enumerating Failures That Say Why

`EnumeratesWith y x` relates a generator with labelled failures at `ExceptT ε Finite` to its search at
`ExceptT ε (OptionT SPMF)`: the successes are exact, and every label the search can fail with is at
least one the enumeration lists. Not exact for labels: the union keeps each branch's own, including
one whose branch the search never ends on because another succeeds. Enough for a checker: an entry
that succeeds says yes, only labels say it could not decide, and none says no.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen

open Basalt

variable {ε α β : Type}

/-- `y`, if defined, succeeds with exactly what `x` succeeds with, and lists a label below each one
`x` can fail with. -/
def EnumeratesWith {ε : Type} [LE ε] {α : Type} (y : ExceptT ε Finite α) (x : ExceptT ε (OptionT SPMF) α) : Prop :=
  y.run ≠ .undef →
    (∀ a, y.run.Mem (.ok a) ↔ some (.ok a) ∈ x.run.run.support) ∧
    ∀ e, some (.error e) ∈ x.run.run.support → ∃ e', y.run.Mem (.error e') ∧ e' ≤ e

namespace EnumeratesWith

/-! ## Runs of `bind` -/

/-- `map` is `bind` then `pure`, at any base monad: they differ only in their `match`es. -/
theorem map_eq_bind {m : Type → Type} [Monad m] (f : α → β) (x : ExceptT ε m α) :
    f <$> x = x >>= fun a => Pure.pure (f a) := by
  show ExceptT.mk (x.run >>= _) = ExceptT.mk (x.run >>= _)
  congr 2

theorem bind_ne_undef {y : ExceptT ε Finite α} {k : α → ExceptT ε Finite β}
    (hd : (y >>= k).run ≠ .undef) : y.run ≠ .undef ∧ ∀ a, y.run.Mem (.ok a) → (k a).run ≠ .undef := by
  rw [ExceptT.run_bind] at hd
  obtain ⟨hy, hk⟩ := Finite.bind_ne_undef hd
  exact ⟨hy, fun a ha => hk _ ha⟩

theorem mem_run_bind {y : ExceptT ε Finite α} {k : α → ExceptT ε Finite β}
    (hd : (y >>= k).run ≠ .undef) (r : Except ε β) :
    (y >>= k).run.Mem r ↔
      (∃ a, y.run.Mem (.ok a) ∧ (k a).run.Mem r) ∨ ∃ e, y.run.Mem (.error e) ∧ r = .error e := by
  rw [ExceptT.run_bind] at hd ⊢
  change Finite.Mem r (Finite.bind _ _) ↔ _
  rw [Finite.mem_bind hd]
  constructor
  · rintro ⟨r₀, h₀, h⟩
    cases r₀ with
    | ok a => exact .inl ⟨a, h₀, h⟩
    | error e => exact .inr ⟨e, h₀, Finite.mem_singleton.mp h⟩
  · rintro (⟨a, h₀, h⟩ | ⟨e, h₀, rfl⟩)
    · exact ⟨.ok a, h₀, h⟩
    · exact ⟨.error e, h₀, Finite.mem_singleton.mpr rfl⟩

theorem mem_support_run_bind {x : ExceptT ε (OptionT SPMF) α} {k : α → ExceptT ε (OptionT SPMF) β}
    (r : Except ε β) :
    some r ∈ (x >>= k).run.run.support ↔
      (∃ a, some (.ok a) ∈ x.run.run.support ∧ some r ∈ (k a).run.run.support) ∨
        ∃ e, some (.error e) ∈ x.run.run.support ∧ r = .error e := by
  rw [ExceptT.run_bind, OptionT.run_bind, Option.elimM, SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨o, ho, h⟩
    rcases o with _ | _ | a
    · simp at h
    · simp only [Option.elim, OptionT.run_pure, SPMF.mem_support_pure_iff, Option.some.injEq] at h
      exact .inr ⟨_, ho, h⟩
    · exact .inl ⟨a, ho, h⟩
  · rintro (⟨a, ho, h⟩ | ⟨e, ho, rfl⟩)
    · exact ⟨some (.ok a), ho, h⟩
    · refine ⟨some (.error e), ho, ?_⟩
      simp [OptionT.run_pure]

/-! ## The construct lemmas -/

variable [Preorder ε]

theorem pure (a : α) : EnumeratesWith (Pure.pure a) (Pure.pure a : ExceptT ε (OptionT SPMF) α) :=
  fun _ => by
    refine ⟨fun b => ?_, fun e he => ?_⟩
    · change (Finite.singleton (Except.ok a : Except ε α)).Mem _ ↔
        _ ∈ (Pure.pure (some (Except.ok a)) : SPMF (Option (Except ε α))).support
      rw [Finite.mem_singleton, SPMF.mem_support_pure_iff]
      simp
    · change _ ∈ (Pure.pure (some (Except.ok a)) : SPMF (Option (Except ε α))).support at he
      rw [SPMF.mem_support_pure_iff] at he
      simp at he

theorem bind {y : ExceptT ε Finite α} {x : ExceptT ε (OptionT SPMF) α}
    {k' : α → ExceptT ε Finite β} {k : α → ExceptT ε (OptionT SPMF) β}
    (hk : ∀ a, EnumeratesWith (k' a) (k a)) (hy : EnumeratesWith y x) :
    EnumeratesWith (y >>= k') (x >>= k) := fun hd => by
  obtain ⟨hyd, hkd⟩ := bind_ne_undef hd
  obtain ⟨hok, herr⟩ := hy hyd
  refine ⟨fun b => ?_, fun e he => ?_⟩
  · rw [mem_run_bind hd, mem_support_run_bind]
    constructor
    · rintro (⟨a, ha, hb⟩ | ⟨e, _, h⟩)
      · exact .inl ⟨a, (hok a).mp ha, ((hk a (hkd a ha)).1 b).mp hb⟩
      · cases h
    · rintro (⟨a, ha, hb⟩ | ⟨e, _, h⟩)
      · have ha' := (hok a).mpr ha
        exact .inl ⟨a, ha', ((hk a (hkd a ha')).1 b).mpr hb⟩
      · cases h
  · rcases (mem_support_run_bind _).mp he with ⟨a, ha, he⟩ | ⟨e₀, he₀, h⟩
    · have ha' := (hok a).mpr ha
      obtain ⟨e', hm, hle⟩ := (hk a (hkd a ha')).2 e he
      exact ⟨e', (mem_run_bind hd _).mpr (.inl ⟨a, ha', hm⟩), hle⟩
    · simp only [Except.error.injEq] at h
      subst h
      obtain ⟨e', hm, hle⟩ := herr _ he₀
      exact ⟨e', (mem_run_bind hd _).mpr (.inr ⟨e', hm, rfl⟩), hle⟩

theorem map {y : ExceptT ε Finite α} {x : ExceptT ε (OptionT SPMF) α} (f : α → β)
    (hy : EnumeratesWith y x) : EnumeratesWith (f <$> y) (f <$> x) := by
  rw [map_eq_bind, map_eq_bind]
  exact bind (fun a => pure (f a)) hy

theorem default (x : ExceptT ε (OptionT SPMF) α) :
    EnumeratesWith (Inhabited.default : ExceptT ε Finite α) x := fun h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    EnumeratesWith (RandomChoice.choose lo hi h : ExceptT ε Finite _)
      (RandomChoice.choose lo hi h : ExceptT ε (OptionT SPMF) _) := fun _ => by
  have hx : ∀ r, some r ∈ (RandomChoice.choose lo hi h : ExceptT ε (OptionT SPMF) _).run.run.support ↔
      ∃ v, r = .ok v := fun r => by
    change some r ∈ (ExceptT.lift (OptionT.lift (RandomChoice.choose lo hi h : SPMF _))).run.run.support ↔ _
    simp [ExceptT.run_lift, OptionT.run_map, OptionT.run_lift]
  refine ⟨fun a => ?_, fun e he => ?_⟩
  · rw [hx]
    change (Finite.map Except.ok (RandomChoice.choose lo hi h : Finite _)).Mem _ ↔ _
    rw [Finite.mem_map]
    simp only [Except.ok.injEq, exists_eq', iff_true]
    exact ⟨a, Finite.mem_choose a, rfl⟩
  · obtain ⟨v, hv⟩ := (hx _).mp he
    cases hv

theorem admissible (x : ExceptT ε (OptionT SPMF) α) :
    Lean.Order.admissible fun y : ExceptT ε Finite α => EnumeratesWith y x :=
  Finite.admissible_defined (α := Except ε α) _

theorem fail : EnumeratesWith (Fail.fail : ExceptT ε Finite α) (Fail.fail : ExceptT ε (OptionT SPMF) α) :=
  fun _ => by
    have hx : ∀ r, some r ∉ (Fail.fail : ExceptT ε (OptionT SPMF) α).run.run.support := fun r h => by
      change some r ∈ (ExceptT.lift (failure : OptionT SPMF α)).run.run.support at h
      simp [ExceptT.run_lift, OptionT.run_failure] at h
    refine ⟨fun a => ⟨fun h => ?_, fun h => absurd h (hx _)⟩, fun e he => absurd he (hx _)⟩
    change (Finite.map Except.ok (Finite.empty : Finite α)).Mem _ at h
    rw [Finite.mem_map] at h
    obtain ⟨_, h, _⟩ := h
    exact absurd h (Finite.not_mem_empty _)

theorem failWith (e : ε) :
    EnumeratesWith (FailWith.failWith e : ExceptT ε Finite α)
      (FailWith.failWith e : ExceptT ε (OptionT SPMF) α) := fun _ => by
  have hx : ∀ r, some r ∈ (FailWith.failWith e : ExceptT ε (OptionT SPMF) α).run.run.support ↔
      r = .error e := fun r => by
    change some r ∈ (Pure.pure (some (Except.error e)) : SPMF (Option (Except ε α))).support ↔ _
    rw [SPMF.mem_support_pure_iff]
    simp
  have hy : ∀ r, (FailWith.failWith e : ExceptT ε Finite α).run.Mem r ↔ r = .error e :=
    fun _ => Finite.mem_singleton
  refine ⟨fun a => by simp [hx, hy], fun e₀ he => ?_⟩
  simp only [hx, Except.error.injEq] at he
  subst he
  exact ⟨e₀, (hy _).mpr rfl, le_rfl⟩

theorem seq {f : ExceptT ε Finite (α → β)} {f' : ExceptT ε (OptionT SPMF) (α → β)}
    {y : ExceptT ε Finite α} {x : ExceptT ε (OptionT SPMF) α}
    (hf : EnumeratesWith f f') (hy : EnumeratesWith y x) :
    EnumeratesWith (f <*> y) (f' <*> x) :=
  bind (fun g => map g hy) hf

end EnumeratesWith

@[walk_rel]
theorem genRel_enumeratesWith [Preorder ε] :
    GenRel (ExceptT ε Finite) (ExceptT ε (OptionT SPMF)) (@EnumeratesWith ε _) where
  pure := EnumeratesWith.pure
  bind := EnumeratesWith.bind
  map := EnumeratesWith.map
  default := EnumeratesWith.default
  choose := EnumeratesWith.choose
  admissible := EnumeratesWith.admissible

attribute [gen_rule] EnumeratesWith.fail EnumeratesWith.failWith EnumeratesWith.seq

/-! ## The search at `OptionT SPMF` -/

namespace Backtrack

variable [SemilatticeSup ε]

omit [SemilatticeSup ε] in
theorem mem_support_finish {acc : Option ε} {r : Except ε α} :
    some r ∈ (finish acc : OptionT SPMF (Except ε α)).run.support ↔ ∃ l, acc = some l ∧ r = .error l := by
  cases acc with
  | none =>
    change some r ∈ (Pure.pure none : SPMF (Option (Except ε α))).support ↔ _
    simp
  | some l =>
    change some r ∈ (Pure.pure (some (Except.error l)) : SPMF (Option (Except ε α))).support ↔ _
    simp

/-- A success of the search is a success of a branch of positive weight. -/
theorem mem_support_searchWith_ok : ∀ (fuel : Nat) (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α)))
    (acc : Option ε) (a : α), some (.ok a) ∈ (searchWith fuel gs acc).run.support →
      ∃ p ∈ gs, 0 < p.1 ∧ some (.ok a) ∈ (p.2 ()).run.run.support
  | _, [], acc, a, h | 0, _ :: _, acc, a, h => by
    simp only [searchWith] at h
    obtain ⟨_, _, he⟩ := mem_support_finish.mp h
    cases he
  | fuel + 1, q :: gs, acc, a, h => by
    simp only [searchWith, OptionT.run_mk, SPMF.mem_support_bind_iff] at h
    obtain ⟨n, _, h⟩ := h
    split at h
    · obtain ⟨_, _, he⟩ := mem_support_finish.mp h
      cases he
    · rename_i k g rest hpick
      obtain ⟨hm, hk, hr⟩ := pickDrop_some hpick
      rw [SPMF.mem_support_bind_iff] at h
      obtain ⟨o, ho, h⟩ := h
      rcases o with _ | _ | a'
      · obtain ⟨p, hp, hp0, hpa⟩ := mem_support_searchWith_ok fuel rest acc a h
        exact ⟨p, hr p hp, hp0, hpa⟩
      · obtain ⟨p, hp, hp0, hpa⟩ := mem_support_searchWith_ok fuel rest _ a h
        exact ⟨p, hr p hp, hp0, hpa⟩
      · simp only [SPMF.mem_support_pure_iff, Option.some.injEq, Except.ok.injEq] at h
        subst h
        exact ⟨(k, g), hm, hk, ho⟩

/-- A success of a branch of positive weight is one of the search, given the fuel to try it. -/
theorem mem_support_searchWith_ok_of_branch : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) (acc : Option ε)
    (p : Nat × (Unit → ExceptT ε (OptionT SPMF) α)), p ∈ gs → 0 < p.1 → 0 < fuel → ∀ a,
    some (.ok a) ∈ (p.2 ()).run.run.support → some (.ok a) ∈ (searchWith fuel gs acc).run.support
  | _, [], _, _, hp, _, _, _, _ => by simp at hp
  | 0, _ :: _, _, _, _, _, hf, _, _ => absurd hf (Nat.lt_irrefl 0)
  | fuel + 1, q :: gs, acc, p, hp, hk, _, a, h => by
    obtain ⟨n, hn, rest, hpick⟩ := exists_pickDrop hp hk
    simp only [searchWith, OptionT.run_mk, SPMF.mem_support_bind_iff]
    refine ⟨ULift.up ⟨n, Nat.zero_le _, by omega⟩, by simp, ?_⟩
    simp only [hpick, SPMF.mem_support_bind_iff]
    exact ⟨some (.ok a), h, by simp⟩

/-- A label the search fails with is at least the one it started with, or at least one a branch of
positive weight fails with. -/
theorem mem_support_searchWith_error : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))) (acc : Option ε) (e : ε),
    some (.error e) ∈ (searchWith fuel gs acc).run.support →
      (∃ l, acc = some l ∧ l ≤ e) ∨
        ∃ p ∈ gs, 0 < p.1 ∧ ∃ l, some (.error l) ∈ (p.2 ()).run.run.support ∧ l ≤ e
  | _, [], acc, e, h | 0, _ :: _, acc, e, h => by
    simp only [searchWith] at h
    obtain ⟨l, rfl, he⟩ := mem_support_finish.mp h
    cases he
    exact .inl ⟨_, rfl, le_rfl⟩
  | fuel + 1, q :: gs, acc, e, h => by
    simp only [searchWith, OptionT.run_mk, SPMF.mem_support_bind_iff] at h
    obtain ⟨n, _, h⟩ := h
    split at h
    · obtain ⟨l, rfl, he⟩ := mem_support_finish.mp h
      cases he
      exact .inl ⟨_, rfl, le_rfl⟩
    · rename_i k g rest hpick
      obtain ⟨hm, hk, hr⟩ := pickDrop_some hpick
      rw [SPMF.mem_support_bind_iff] at h
      obtain ⟨o, ho, h⟩ := h
      rcases o with _ | e₀ | a'
      · rcases mem_support_searchWith_error fuel rest acc e h with hl | ⟨p, hp, hp0, hpl⟩
        · exact .inl hl
        · exact .inr ⟨p, hr p hp, hp0, hpl⟩
      · rcases mem_support_searchWith_error fuel rest _ e h with ⟨l, hl, hle⟩ | ⟨p, hp, hp0, hpl⟩
        · simp only [Option.some.injEq] at hl
          refine .inr ⟨(k, g), hm, hk, e₀, ho, le_trans ?_ hle⟩
          subst hl
          cases acc with
          | none => exact le_rfl
          | some l₀ => exact le_sup_right
        · exact .inr ⟨p, hr p hp, hp0, hpl⟩
      · simp at h

end Backtrack

/-! ## The rules -/

namespace EnumeratesWith

variable [SemilatticeSup ε]

/-- The union at `ExceptT ε Finite` and the search with any fuel that can try every branch. -/
theorem union {gs' : List (Nat × (Unit → ExceptT ε Finite α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))}
    (hs : GenRel.Weighted (@EnumeratesWith ε _) gs' gs) (fuel : Nat) (hfuel : ∀ p ∈ gs, 0 < fuel) :
    EnumeratesWith (Backtrack.backtrack gs' : ExceptT ε Finite α)
      (ExceptT.mk (Backtrack.searchWith fuel gs none)) := fun hd => by
  let gsR := gs'.map fun p => (p.1, fun u => (p.2 u).run)
  change (Backtrack.backtrack gsR : Finite (Except ε α)) ≠ .undef at hd
  have hmem : ∀ r, (Backtrack.backtrack gsR : Finite (Except ε α)).Mem r ↔
      ∃ p ∈ gs', 0 < p.1 ∧ (p.2 ()).run.Mem r := fun r => by
    rw [Backtrack.mem_backtrack_finite hd]
    simp only [gsR, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hk, h⟩
      exact ⟨p, hp, hk, h⟩
    · rintro ⟨p, hp, hk, h⟩
      exact ⟨_, ⟨p, hp, rfl⟩, hk, h⟩
  have hdef : ∀ p ∈ gs', 0 < p.1 → (p.2 ()).run ≠ .undef := fun p hp hk =>
    Backtrack.backtrack_branch_defined hd (List.mem_map.mpr ⟨p, hp, rfl⟩) hk
  have hw := hs.weights
  refine ⟨fun a => ?_, fun e he => ?_⟩
  · change (Backtrack.backtrack gsR : Finite (Except ε α)).Mem _ ↔ _
    rw [hmem]
    constructor
    · rintro ⟨p', hp', hk, h⟩
      obtain ⟨g, hg, hr⟩ := Weighted.exists_right hs hp'
      exact Backtrack.mem_support_searchWith_ok_of_branch fuel gs none _ hg hk (hfuel _ hg) a
        (((hr (hdef p' hp' hk)).1 a).mp h)
    · intro h
      obtain ⟨p, hp, hk, h⟩ := Backtrack.mem_support_searchWith_ok fuel gs none a h
      obtain ⟨g', hg', hr⟩ := Weighted.exists_left hs hp
      exact ⟨(p.1, g'), hg', hk, ((hr (hdef _ hg' hk)).1 a).mpr h⟩
  · rcases Backtrack.mem_support_searchWith_error fuel gs none e he with ⟨_, h, _⟩ | ⟨p, hp, hk, l, hl, hle⟩
    · cases h
    · obtain ⟨g', hg', hr⟩ := Weighted.exists_left hs hp
      obtain ⟨e', hm, hle'⟩ := (hr (hdef _ hg' hk)).2 l hl
      exact ⟨e', (hmem _).mpr ⟨(p.1, g'), hg', hk, hm⟩, le_trans hle' hle⟩

/-- The union lists the search's successes exactly, and a label below each of its failures. -/
@[gen_rule]
theorem backtrack {gs' : List (Nat × (Unit → ExceptT ε Finite α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))}
    (hs : GenRel.Weighted (@EnumeratesWith ε _) gs' gs) :
    EnumeratesWith (Backtrack.backtrack gs') (Backtrack.backtrack gs) :=
  union hs gs.length fun _ hp => List.length_pos_of_mem hp

/-- The same for the draw, the search with fuel for one branch. -/
@[gen_rule]
theorem pick {gs' : List (Nat × (Unit → ExceptT ε Finite α))}
    {gs : List (Nat × (Unit → ExceptT ε (OptionT SPMF) α))}
    (hs : GenRel.Weighted (@EnumeratesWith ε _) gs' gs) :
    EnumeratesWith (Pick.pick gs') (Pick.pick gs) :=
  union hs 1 fun _ _ => Nat.one_pos

end EnumeratesWith

end Specimen
