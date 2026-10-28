/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.Basic
public import Basalt.OptionT

/-!
# Generators That Fail

A generator that can `fail` has no plain `SPMF` meaning (failure would be lost mass,
indistinguishable from divergence); its distribution is at `OptionT SPMF`, failure being `none`. At
`Finite`, failure is `∅`. `EnumeratesSome y x` relates the two: `y`, if defined, has as its entries
exactly the values `x` succeeds with — the `some` part of its support. It is a `GenRel`
(`genRel_enumeratesSome`), and `EnumeratesSome.fail` and `.seq` cover `Fail.fail` and `<*>`, which
`GenRel` does not.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen

open Basalt

/-- `y`, if defined, has as its entries exactly the values `x` succeeds with. -/
def EnumeratesSome {α : Type} (y : Finite α) (x : OptionT SPMF α) : Prop :=
  y ≠ .undef → ∀ a, y.Mem a ↔ some a ∈ (x.run : SPMF (Option α)).support

namespace EnumeratesSome

variable {α β : Type}

theorem pure (a : α) : EnumeratesSome (Pure.pure a) (Pure.pure a : OptionT SPMF α) := fun _ b => by
  have : (Pure.pure a : OptionT SPMF α).run = (Pure.pure (some a) : SPMF (Option α)) := rfl
  rw [this, SPMF.mem_support_pure_iff]
  exact Finite.mem_singleton.trans (Option.some_inj).symm

theorem bind {y : Finite α} {x : OptionT SPMF α} {k' : α → Finite β} {k : α → OptionT SPMF β}
    (hk : ∀ a, EnumeratesSome (k' a) (k a)) (hy : EnumeratesSome y x) :
    EnumeratesSome (y >>= k') (x >>= k) := fun hd b => by
  change y.bind k' ≠ .undef at hd
  change (y.bind k').Mem b ↔ _
  obtain ⟨hyd, hkd⟩ := Finite.bind_ne_undef hd
  have : (x >>= k : OptionT SPMF β).run = (x.run >>= fun o => match o with
      | some a => (k a).run
      | none => Pure.pure none : SPMF (Option β)) := rfl
  rw [this, Finite.mem_bind hd, SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨some a, (hy hyd a).mp ha, (hk a (hkd a ha) b).mp hb⟩
  · rintro ⟨o, ho, hb⟩
    cases o with
    | none => simp at hb
    | some a =>
      have ha := (hy hyd a).mpr ho
      exact ⟨a, ha, (hk a (hkd a ha) b).mpr hb⟩

theorem map {y : Finite α} {x : OptionT SPMF α} (f : α → β) (hy : EnumeratesSome y x) :
    EnumeratesSome (f <$> y) (f <$> x) := fun hd b => by
  change (y.map f) ≠ .undef at hd
  change (y.map f).Mem b ↔ _
  have hyd := Finite.map_ne_undef hd
  have : (f <$> x : OptionT SPMF β).run = (x.run >>= fun o => match o with
      | some a => Pure.pure (some (f a))
      | none => Pure.pure none : SPMF (Option β)) := rfl
  rw [this, Finite.mem_map, SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨some a, (hy hyd a).mp ha, by simp⟩
  · rintro ⟨o, ho, hb⟩
    cases o with
    | none => simp at hb
    | some a =>
      simp only [SPMF.mem_support_pure_iff, Option.some_inj] at hb
      exact ⟨a, (hy hyd a).mpr ho, hb⟩

theorem default (x : OptionT SPMF α) : EnumeratesSome Inhabited.default x := fun h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    EnumeratesSome (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := fun _ m => by
  have : (RandomChoice.choose lo hi h : OptionT SPMF _).run =
      ((RandomChoice.choose lo hi h : SPMF _) >>= fun a => Pure.pure (some a)) := rfl
  rw [this, SPMF.mem_support_bind_iff]
  simp only [SPMF.mem_support_choose_iff, SPMF.mem_support_pure_iff, Option.some_inj, true_and,
    exists_eq', iff_true]
  exact Finite.mem_choose m

theorem fail : EnumeratesSome (Fail.fail : Finite α) (Fail.fail : OptionT SPMF α) := fun _ a => by
  have : (Fail.fail : OptionT SPMF α).run = (Pure.pure none : SPMF (Option α)) := rfl
  rw [this, SPMF.mem_support_pure_iff]
  exact ⟨fun h => absurd h (Finite.not_mem_empty a), fun h => by cases h⟩

theorem seq {f : Finite (α → β)} {f' : OptionT SPMF (α → β)} {y : Finite α} {x : OptionT SPMF α}
    (hf : EnumeratesSome f f') (hy : EnumeratesSome y x) :
    EnumeratesSome (f <*> y) (f' <*> x) := by
  have hseq : (f' <*> x : OptionT SPMF β) = f' >>= fun g => g <$> x := rfl
  intro hd b
  change f.seq y ≠ .undef at hd
  change (f.seq y).Mem b ↔ _
  have hfd : f ≠ .undef := fun h => hd (by rw [h]; rfl)
  have hyd : y ≠ .undef := fun h => hd (by cases f <;> simp [h, Finite.seq])
  rw [Finite.mem_seq, hseq]
  have hbd : f.bind (fun g => Finite.map g y) ≠ .undef :=
    Finite.bind_defined hfd fun g _ => Finite.map_defined g hyd
  have hb := (bind (k' := fun g => g <$> y) (fun g => map g hy) hf) hbd b
  rw [← hb]
  change _ ↔ (f.bind fun g => Finite.map g y).Mem b
  rw [Finite.mem_bind hbd]
  simp only [Finite.mem_map]

theorem pickFrom (l : List β) : EnumeratesSome (pickFrom l : Finite β) (pickFrom l : OptionT SPMF β) := by
  cases l with
  | nil => exact fail
  | cons x xs => exact bind (fun _ => pure _) (choose _ _ _)

theorem admissible (x : OptionT SPMF α) :
    Lean.Order.admissible fun y : Finite α => EnumeratesSome y x :=
  Finite.admissible_defined _

end EnumeratesSome

@[walk_rel]
theorem genRel_enumeratesSome : GenRel Finite (OptionT SPMF) @EnumeratesSome where
  pure := EnumeratesSome.pure
  bind := EnumeratesSome.bind
  map := EnumeratesSome.map
  default := EnumeratesSome.default
  choose := EnumeratesSome.choose
  admissible := EnumeratesSome.admissible

attribute [gen_rule] EnumeratesSome.fail EnumeratesSome.seq

end Specimen
