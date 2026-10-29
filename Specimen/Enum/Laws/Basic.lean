/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Finite
public import Basalt.GenRel
public import Basalt.Order
public import Basalt.SPMF.Support
public import Basalt.Walk.Attr
public import Basalt.Laws

/-!
# An Enumeration Is the Support

A generator run at `Finite`, where its result is defined, lists exactly the values it can produce:
its `SPMF` support. That is a free theorem, so it is proved per generator, as a relation between the
two interpretations: `Enumerates y x` says `y`, if defined, has `x`'s support as its entries. It is
a `GenRel` (`genRel_enumerates`), so `walk fixpoint` proves it for a generator construct by
construct (`IsEnumerated`), and `IsEnumerated.support_eq` turns it into the statement.

Where the result is `undef` — the generator's choices do not form a finite tree — nothing is
claimed; `undef` is the bottom of the flat order, which is what makes the relation admissible for
fixpoint induction.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen

open Basalt


/-! ## The relation -/

/-- `y`, if defined, has exactly `x`'s support as its entries. -/
def Enumerates {α : Type} (y : Finite α) (x : SPMF α) : Prop :=
  y ≠ .undef → ∀ a, y.Mem a ↔ a ∈ x.support

namespace Enumerates

variable {α β : Type}

theorem pure (a : α) : Enumerates (Pure.pure a) (Pure.pure a : SPMF α) := fun _ b => by
  show (Finite.singleton a).Mem b ↔ _
  simp

theorem bind {y : Finite α} {x : SPMF α} {k' : α → Finite β} {k : α → SPMF β}
    (hk : ∀ a, Enumerates (k' a) (k a)) (hy : Enumerates y x) :
    Enumerates (y >>= k') (x >>= k) := fun hd b => by
  change (y.bind k').Mem b ↔ _
  change y.bind k' ≠ .undef at hd
  obtain ⟨hyd, hkd⟩ := Finite.bind_ne_undef hd
  rw [Finite.mem_bind hd, SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, (hy hyd a).mp ha, (hk a (hkd a ha) b).mp hb⟩
  · rintro ⟨a, ha, hb⟩
    have ha' := (hy hyd a).mpr ha
    exact ⟨a, ha', (hk a (hkd a ha') b).mpr hb⟩

theorem map {y : Finite α} {x : SPMF α} (f : α → β) (hy : Enumerates y x) :
    Enumerates (f <$> y) (f <$> x) := fun hd b => by
  change (y.map f).Mem b ↔ _
  change y.map f ≠ .undef at hd
  have hyd := Finite.map_ne_undef hd
  rw [Finite.mem_map, SPMF.mem_support_map_iff]
  exact ⟨fun ⟨a, ha, hb⟩ => ⟨a, (hy hyd a).mp ha, hb⟩, fun ⟨a, ha, hb⟩ => ⟨a, (hy hyd a).mpr ha, hb⟩⟩

theorem default (x : SPMF α) : Enumerates Inhabited.default x := fun h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    Enumerates (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h) := fun _ a => by
  simp only [SPMF.mem_support_choose_iff, iff_true]
  exact Finite.mem_choose a

/-- Fixpoint induction on the `Finite` side: the relation holds of `undef`, the bottom of a flat
order, so of the limit of every chain it holds along. -/
theorem admissible (x : SPMF α) : Lean.Order.admissible fun y : Finite α => Enumerates y x :=
  Finite.admissible_defined _

end Enumerates

@[walk_rel]
theorem genRel_enumerates : GenRel Finite SPMF @Enumerates where
  pure := Enumerates.pure
  bind := Enumerates.bind
  map := Enumerates.map
  default := Enumerates.default
  choose := Enumerates.choose
  admissible := Enumerates.admissible

/-! ## Per generator -/

/-- `gen`'s enumeration, wherever it is defined, is its support. A free theorem, which Lean cannot
prove once for every generator: the field is proved by `walk fixpoint`, with a callee's law passed
by its field. -/
structure IsEnumerated {α : Type} (gen : {G : Type → Type} → [Gen G] → G α) : Prop where
  enumerates : Enumerates (gen (G := Finite)) (gen (G := SPMF))

/-- The statement: a defined enumeration's entries are exactly the values the generator can
produce. -/
theorem IsEnumerated.support_eq {α : Type} {gen : {G : Type → Type} → [Gen G] → G α}
    (h : IsEnumerated gen) (hd : gen (G := Finite) ≠ .undef) :
    {a | (gen (G := Finite)).Mem a} = (gen (G := SPMF)).support :=
  Set.ext (h.enumerates hd)

/-- With the generator's correctness: a defined enumeration lists exactly the values satisfying `P`.
Soundness gives that every entry satisfies `P`, completeness that every value satisfying `P` is an
entry. -/
theorem IsEnumerated.mem_iff {α : Type} {gen : {G : Type → Type} → [Gen G] → G α} {P : α → Prop}
    (h : IsEnumerated gen) (hsc : IsSoundAndComplete (gen (G := SPMF)) P)
    (hd : gen (G := Finite) ≠ .undef) (a : α) :
    (gen (G := Finite)).Mem a ↔ P a :=
  (h.enumerates hd a).trans ⟨hsc.sound a, hsc.complete a⟩

/-- Soundness alone: every entry of a defined enumeration satisfies `P`. -/
theorem IsEnumerated.sound {α : Type} {gen : {G : Type → Type} → [Gen G] → G α} {P : α → Prop}
    (h : IsEnumerated gen) (hs : IsSoundFor (gen (G := SPMF)) P)
    (hd : gen (G := Finite) ≠ .undef) {a : α} (ha : (gen (G := Finite)).Mem a) : P a :=
  hs a ((h.enumerates hd a).mp ha)

end Specimen
