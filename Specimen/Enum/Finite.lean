/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Segev Elazar-Mittelman
-/
module

public import Basalt.Gen
public import Specimen.Enum.Fail
public import Basalt.Order

/-!
# Exhaustive Interpretation: `Finite`

FEAT's finite sets as a generator interpretation: a `Finite` is a set presented by a cardinality and
an indexing function, and a `choose` is every value of its range, so a generator run here is the
collection of everything it can produce, one entry per path. Counting is arithmetic — a union adds,
a product (`<*>`) multiplies, and `bind` visits only the values on its left — so a count never needs
the values themselves where the parts are independent.

The order is flat, with `undef` at the bottom, as `partial_fixpoint` needs. `undef` is the honest
answer where there is no finite one: a generator whose choices do not form a finite tree (an
unbounded retry, an infinite support) is `undef` here. `fail` is `∅`, which is not `undef`: an
empty set, known to be empty.
-/

@[expose] public section

open Lean.Order

namespace Specimen


/-! ## Finite sets -/

/-- A set of `card` values, presented by an indexing function (since Lean does not allow infinite
lists).  -/
inductive Finite (α : Type u) : Type u where
  /-- The undefined set, the bottom of the flat order on `Finite`. -/
  | undef : Finite α
  /-- The set of the `card` values `index 0, …, index (card - 1)`. -/
  | mk (card : Nat) (index : Fin card → α) : Finite α

namespace Finite

/-- The empty set; distinct from `undef`, which is a set whose cardinality is unknown. -/
def empty : Finite α := .mk 0 Fin.elim0

/-- The one-element set. -/
def singleton (a : α) : Finite α := .mk 1 fun _ => a

/-- FEAT's `fCard`. -/
def card? : Finite α → Option Nat
  | .undef => none
  | .mk n _ => some n

/-- FEAT's `fIndex`, bounds-checked. -/
def get? : Finite α → Nat → Option α
  | .undef, _ => none
  | .mk n f, i => if h : i < n then some (f ⟨i, h⟩) else none

/-- The values of a defined set, in index order. -/
def toList? : Finite α → Option (List α)
  | .undef => none
  | .mk _ f => some (List.ofFn f)

/-- FEAT's `fPlus`: the disjoint union, indexing `x` before `y`. -/
def union : Finite α → Finite α → Finite α
  | .undef, _ => .undef
  | _, .undef => .undef
  | .mk m f, .mk n g =>
    .mk (m + n) fun i =>
      if h : i.val < m then f ⟨i.val, h⟩ else g ⟨i.val - m, by have := i.isLt; omega⟩

/-- The union of a list of sets, in order. -/
def flatten (xs : List (Finite α)) : Finite α := xs.foldr union empty

/-- `flatten` by halves, so each part sits under logarithmically many unions instead of under every
part before it. What the compiler runs for `flatten` (`flatten_eq_flattenBal`). -/
def flattenBal : List (Finite α) → Finite α
  | [] => empty
  | [x] => x
  | x :: y :: zs =>
    union (flattenBal ((x :: y :: zs).take ((zs.length + 2) / 2)))
      (flattenBal ((x :: y :: zs).drop ((zs.length + 2) / 2)))
termination_by xs => xs.length
decreasing_by all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

theorem mk_eq_mk {m n : Nat} {f : Fin m → α} {g : Fin n → α} (h : m = n)
    (hfg : ∀ i : Fin m, f i = g (i.cast h)) : Finite.mk m f = .mk n g := by
  subst h
  congr
  funext i
  exact hfg i

theorem empty_union (x : Finite α) : empty.union x = x := by
  cases x with
  | undef => rfl
  | mk n g =>
    refine mk_eq_mk (Nat.zero_add n) fun i => ?_
    simp only [Nat.not_lt_zero, ↓reduceDIte]
    congr 1

theorem union_empty (x : Finite α) : x.union empty = x := by
  cases x with
  | undef => rfl
  | mk m f =>
    refine mk_eq_mk (Nat.add_zero m) fun i => ?_
    simp only [show i.val < m from i.isLt, ↓reduceDIte]
    rfl

theorem union_assoc (x y z : Finite α) : (x.union y).union z = x.union (y.union z) := by
  cases x with
  | undef => rfl
  | mk m f =>
    cases y with
    | undef => cases z <;> rfl
    | mk n g =>
      cases z with
      | undef => rfl
      | mk k h =>
        refine mk_eq_mk (Nat.add_assoc m n k) fun i => ?_
        simp only [Fin.val_cast]
        by_cases h₁ : i.val < m
        · have : i.val < m + n := by omega
          simp [h₁, this]
        · by_cases h₂ : i.val < m + n
          · have : i.val - m < n := by omega
            simp [h₁, h₂, this]
          · have : ¬ i.val - m < n := by omega
            simp only [h₁, h₂, this, ↓reduceDIte]
            congr 1
            ext
            simp only
            omega

theorem flatten_append (xs ys : List (Finite α)) :
    flatten (xs ++ ys) = (flatten xs).union (flatten ys) := by
  induction xs with
  | nil => exact (empty_union _).symm
  | cons x xs ih =>
    show x.union (flatten (xs ++ ys)) = (x.union (flatten xs)).union (flatten ys)
    rw [ih, union_assoc]

theorem flattenBal_eq : ∀ xs : List (Finite α), flattenBal xs = flatten xs
  | [] => by rw [flattenBal]; rfl
  | [x] => by rw [flattenBal]; exact (union_empty x).symm
  | x :: y :: zs => by
    have h₁ := flattenBal_eq ((x :: y :: zs).take ((zs.length + 2) / 2))
    have h₂ := flattenBal_eq ((x :: y :: zs).drop ((zs.length + 2) / 2))
    rw [flattenBal, h₁, h₂, ← flatten_append, List.take_append_drop]
termination_by xs => xs.length
decreasing_by all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

@[csimp] theorem flatten_eq_flattenBal : @flatten = @flattenBal := by
  funext α xs
  exact (flattenBal_eq xs).symm

/-- The union of `f a` over the values `a` of `x`, indexed in the order `x` indexes them. -/
def bind (x : Finite α) (f : α → Finite β) : Finite β :=
  match x with
  | .undef => .undef
  | .mk _ index => flatten (List.ofFn fun i => f (index i))

/-- `fmap` reindexing, so the cardinality is untouched. -/
def map (f : α → β) : Finite α → Finite β
  | .undef => .undef
  | .mk n index => .mk n (f ∘ index)

/-- FEAT's product: every function of `f` applied to every value of `x`, indexed in the order `bind`
would index them, but without visiting the values of `f` to find the cardinality. -/
def seq (f : Finite (α → β)) (x : Finite α) : Finite β :=
  match f, x with
  | .undef, _ => .undef
  | _, .undef => .undef
  | .mk m f, .mk n g =>
    .mk (m * n) fun i =>
      have hn : 0 < n := Nat.pos_of_ne_zero fun h => by have := i.isLt; simp [h] at this
      f ⟨i.val / n, (Nat.div_lt_iff_lt_mul hn).mpr i.isLt⟩ (g ⟨i.val % n, Nat.mod_lt _ hn⟩)

instance : Monad Finite where
  pure := Finite.singleton
  bind := Finite.bind
  map := Finite.map
  seq f x := Finite.seq f (x ())

/-- `default` is `undef`: the bottom element, the least defined set. -/
instance : Inhabited (Finite α) where
  default := .undef

instance instPartialOrder : PartialOrder (Finite α) := FlatOrder.instOrder (b := .undef)

instance instCCPO : CCPO (Finite α) := FlatOrder.instCCPO (b := .undef)

theorem eq_undef_or_eq {x y : Finite α} (h : x ⊑ y) : x = .undef ∨ x = y := by
  cases h with
  | bot => exact .inl rfl
  | refl => exact .inr rfl

@[simp] theorem union_undef_left {y : Finite α} : union .undef y = .undef := rfl

@[simp] theorem union_undef_right {x : Finite α} : union x .undef = .undef := by cases x <;> rfl

theorem union_mono {x₁ x₂ y₁ y₂ : Finite α} (hx : x₁ ⊑ x₂) (hy : y₁ ⊑ y₂) :
    union x₁ y₁ ⊑ union x₂ y₂ := by
  rcases eq_undef_or_eq hx with rfl | rfl
  · rw [union_undef_left]
    exact FlatOrder.rel.bot
  · rcases eq_undef_or_eq hy with rfl | rfl
    · rw [union_undef_right]
      exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl

theorem flatten_eq_undef {xs : List (Finite α)} (h : Finite.undef ∈ xs) :
    flatten xs = .undef := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · show union x (flatten xs) = .undef
      rw [ih h, union_undef_right]

theorem flatten_ofFn_mono {n : Nat} {f g : Fin n → Finite α} (h : ∀ i, f i ⊑ g i) :
    flatten (List.ofFn f) ⊑ flatten (List.ofFn g) := by
  induction n with
  | zero => exact FlatOrder.rel.refl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact union_mono (h 0) (ih fun i => h i.succ)

instance : MonoBind Finite where
  bind_mono_left h := by
    rcases eq_undef_or_eq h with rfl | rfl
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right {_ _ x f₁ f₂} h := by
    cases x with
    | undef => exact FlatOrder.rel.refl
    | mk n index =>
      show Finite.bind (.mk n index) f₁ ⊑ Finite.bind (.mk n index) f₂
      by_cases hu : ∃ i, f₁ (index i) = .undef
      · obtain ⟨i, hi⟩ := hu
        rw [show Finite.bind (.mk n index) f₁ = .undef from
          flatten_eq_undef (List.mem_ofFn.mpr ⟨i, hi⟩)]
        exact FlatOrder.rel.bot
      · have heq : ∀ i, f₁ (index i) = f₂ (index i) := fun i =>
          (eq_undef_or_eq (h (index i))).resolve_left (fun hb => hu ⟨i, hb⟩)
        rw [show Finite.bind (.mk n index) f₁ = Finite.bind (.mk n index) f₂ from
          congrArg flatten (congrArg List.ofFn (funext heq))]
        exact FlatOrder.rel.refl


theorem map_mono {f : α → β} {x y : Finite α} (h : x ⊑ y) : x.map f ⊑ y.map f := by
  rcases eq_undef_or_eq h with rfl | rfl
  · exact FlatOrder.rel.bot
  · exact FlatOrder.rel.refl

/-- Every value of the range, once, in increasing order. -/
instance : RandomChoice Finite where
  choose lo hi _ := .mk (hi - lo + 1) fun i => .up ⟨lo + i.val, by have := i.isLt; omega⟩

/-- Nothing: the empty set, known to be empty. -/
instance : Fail Finite := ⟨.empty⟩

end Finite

/-! ## Membership -/

namespace Finite

variable {α β : Type}

/-- `a` is one of the entries of `x`. -/
def Mem (a : α) : Finite α → Prop
  | .undef => False
  | .mk _ f => ∃ i, f i = a

@[simp] theorem not_mem_undef (a : α) : ¬ (Finite.undef : Finite α).Mem a := id

@[simp] theorem mem_mk {n : Nat} {f : Fin n → α} {a : α} : (Finite.mk n f).Mem a ↔ ∃ i, f i = a :=
  Iff.rfl

@[simp] theorem not_mem_empty (a : α) : ¬ (Finite.empty : Finite α).Mem a := fun ⟨i, _⟩ => i.elim0

@[simp] theorem mem_singleton {a b : α} : (Finite.singleton a).Mem b ↔ b = a :=
  ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩

theorem union_ne_undef {x y : Finite α} (h : x.union y ≠ .undef) : x ≠ .undef ∧ y ≠ .undef := by
  refine ⟨fun hx => h ?_, fun hy => h ?_⟩
  · rw [hx]; rfl
  · rw [hy, union_undef_right]

theorem mem_union {x y : Finite α} (hx : x ≠ .undef) (hy : y ≠ .undef) {a : α} :
    (x.union y).Mem a ↔ x.Mem a ∨ y.Mem a := by
  cases x with
  | undef => exact absurd rfl hx
  | mk m f =>
    cases y with
    | undef => exact absurd rfl hy
    | mk n g =>
      simp only [union, mem_mk]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h : i.val < m
        · exact .inl ⟨⟨i.val, h⟩, by simpa [h] using hi⟩
        · exact .inr ⟨⟨i.val - m, by have := i.isLt; omega⟩, by simpa [h] using hi⟩
      · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
        · exact ⟨⟨j.val, by have := j.isLt; omega⟩, by simp [j.isLt, hj]⟩
        · refine ⟨⟨m + j.val, by have := j.isLt; omega⟩, ?_⟩
          have h : ¬ m + j.val < m := by omega
          simp only [h, ↓reduceDIte]
          simpa using hj

theorem flatten_ne_undef {xs : List (Finite α)} (h : flatten xs ≠ .undef) :
    ∀ x ∈ xs, x ≠ .undef := fun _ hx hu => h (flatten_eq_undef (hu ▸ hx))

theorem mem_flatten {xs : List (Finite α)} (h : flatten xs ≠ .undef) {a : α} :
    (flatten xs).Mem a ↔ ∃ x ∈ xs, x.Mem a := by
  induction xs with
  | nil => simp [flatten]
  | cons x xs ih =>
    have hu := union_ne_undef (x := x) (y := flatten xs) h
    show (x.union (flatten xs)).Mem a ↔ _
    rw [mem_union hu.1 hu.2, ih hu.2]
    simp

theorem bind_ne_undef {x : Finite α} {f : α → Finite β} (h : x.bind f ≠ .undef) :
    x ≠ .undef ∧ ∀ a, x.Mem a → f a ≠ .undef := by
  cases x with
  | undef => exact absurd rfl h
  | mk n idx =>
    refine ⟨by simp, fun a ha => ?_⟩
    rw [mem_mk] at ha
    obtain ⟨i, rfl⟩ := ha
    exact flatten_ne_undef h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem mem_bind {x : Finite α} {f : α → Finite β} (h : x.bind f ≠ .undef) {b : β} :
    (x.bind f).Mem b ↔ ∃ a, x.Mem a ∧ (f a).Mem b := by
  cases x with
  | undef => exact absurd rfl h
  | mk n idx =>
    show (flatten (List.ofFn fun i => f (idx i))).Mem b ↔ _
    rw [mem_flatten h]
    simp only [List.mem_ofFn, mem_mk]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hb⟩
      exact ⟨idx i, ⟨i, rfl⟩, hb⟩
    · rintro ⟨_, ⟨i, rfl⟩, hb⟩
      exact ⟨f (idx i), ⟨i, rfl⟩, hb⟩

theorem map_ne_undef {x : Finite α} {f : α → β} (h : x.map f ≠ .undef) : x ≠ .undef := by
  intro hx; subst hx; exact h rfl

theorem mem_map {x : Finite α} {f : α → β} {b : β} :
    (x.map f).Mem b ↔ ∃ a, x.Mem a ∧ b = f a := by
  cases x with
  | undef => simp [map]
  | mk n idx =>
    simp only [map, mem_mk, Function.comp]
    exact ⟨fun ⟨i, hi⟩ => ⟨idx i, ⟨i, rfl⟩, hi.symm⟩, fun ⟨_, ⟨i, hi⟩, hb⟩ => ⟨i, hi ▸ hb.symm⟩⟩

theorem mem_choose {lo hi : Nat} {h : lo ≤ hi} (a : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}) :
    (RandomChoice.choose lo hi h : Finite _).Mem a := by
  rw [show (RandomChoice.choose lo hi h : Finite _) =
      .mk (hi - lo + 1) (fun i => .up ⟨lo + i.val, by have := i.isLt; omega⟩) from rfl, mem_mk]
  obtain ⟨⟨v, hv⟩⟩ := a
  exact ⟨⟨v - lo, by omega⟩, by simp only [ULift.up.injEq, Subtype.mk.injEq]; omega⟩

/-- A property that claims something only of defined results is admissible: the limit of a chain
along which it holds is either `undef`, where it claims nothing, or one of the chain. -/
theorem admissible_defined (Q : Finite α → Prop) :
    Lean.Order.admissible fun y : Finite α => y ≠ .undef → Q y := by
  rw [admissible_iff]
  intro c hc hall hd
  have : ∃ y, c y ∧ y ≠ .undef := by
    refine Classical.byContradiction fun hno => hd ?_
    have hle : CCPO.csup hc ⊑ (Finite.undef : Finite α) := csup_le hc fun y hy => by
      have : y = .undef := Classical.byContradiction fun hy' => hno ⟨y, hy, hy'⟩
      rw [this]; exact PartialOrder.rel_refl
    exact (eq_undef_or_eq hle).elim id id
  obtain ⟨y, hy, hyd⟩ := this
  have : y = CCPO.csup hc := (eq_undef_or_eq (le_csup hc hy)).resolve_left hyd
  exact this ▸ hall y hy (this ▸ hyd)

theorem mem_seq {f : Finite (α → β)} {x : Finite α} {b : β} :
    (f.seq x).Mem b ↔ ∃ g, f.Mem g ∧ ∃ a, x.Mem a ∧ b = g a := by
  cases f with
  | undef => simp [seq]
  | mk m F =>
    cases x with
    | undef => simp [seq]
    | mk n X =>
      simp only [seq, mem_mk]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, hi.symm⟩
      · rintro ⟨_, ⟨⟨j, hj⟩, rfl⟩, _, ⟨⟨l, hl⟩, rfl⟩, rfl⟩
        have hn : 0 < n := by omega
        have hlt : n * j + l < m * n := by
          have h1 : n * j + l < n * (j + 1) := by rw [Nat.mul_succ]; omega
          have h2 : n * (j + 1) ≤ n * m := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_comm m n]; omega
        refine ⟨⟨n * j + l, hlt⟩, ?_⟩
        have hdiv : (n * j + l) / n = j := by
          rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hl, Nat.add_zero]
        have hmod : (n * j + l) % n = l := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
        simp only [hdiv, hmod]

/-! ## Definedness

A result built from defined parts is defined. Fixpoint induction cannot show this — it is
termination, false of `undef` — so a generator's definedness is proved from these, by induction on
whatever makes its recursion terminate. -/

@[simp] theorem singleton_ne_undef (a : α) : Finite.singleton a ≠ .undef := by simp [singleton]

@[simp] theorem empty_ne_undef : (Finite.empty : Finite α) ≠ .undef := by simp [empty]

@[simp] theorem pure_ne_undef (a : α) : (Pure.pure a : Finite α) ≠ .undef := singleton_ne_undef a

@[simp] theorem fail_ne_undef : (Fail.fail : Finite α) ≠ .undef := empty_ne_undef

@[simp] theorem choose_ne_undef (lo hi : Nat) (h : lo ≤ hi) :
    (RandomChoice.choose lo hi h : Finite _) ≠ .undef := by
  rw [show (RandomChoice.choose lo hi h : Finite _) =
    .mk (hi - lo + 1) (fun i => .up ⟨lo + i.val, by have := i.isLt; omega⟩) from rfl]
  simp

theorem union_defined {x y : Finite α} (hx : x ≠ .undef) (hy : y ≠ .undef) :
    x.union y ≠ .undef := by
  cases x with
  | undef => exact absurd rfl hx
  | mk => cases y with
    | undef => exact absurd rfl hy
    | mk => simp [union]

theorem flatten_defined {xs : List (Finite α)} (h : ∀ x ∈ xs, x ≠ .undef) : flatten xs ≠ .undef := by
  induction xs with
  | nil => exact empty_ne_undef
  | cons x xs ih =>
    exact union_defined (h x (List.mem_cons_self ..)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem bind_defined {x : Finite α} {f : α → Finite β} (hx : x ≠ .undef)
    (hf : ∀ a, x.Mem a → f a ≠ .undef) : x >>= f ≠ .undef := by
  cases x with
  | undef => exact absurd rfl hx
  | mk n idx =>
    refine flatten_defined fun z hz => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hf _ ⟨i, rfl⟩

theorem map_defined {x : Finite α} (f : α → β) (hx : x ≠ .undef) : f <$> x ≠ .undef := by
  cases x with
  | undef => exact absurd rfl hx
  | mk => simp [Functor.map, map]

theorem seq_defined {f : Finite (α → β)} {x : Finite α} (hf : f ≠ .undef) (hx : x ≠ .undef) :
    f <*> x ≠ .undef := by
  cases f with
  | undef => exact absurd rfl hf
  | mk => cases x with
    | undef => exact absurd rfl hx
    | mk => simp [Seq.seq, seq]

theorem pickFrom_defined (xs : List β) : (pickFrom xs : Finite β) ≠ .undef := by
  cases xs with
  | nil => exact fail_ne_undef
  | cons x xs => exact bind_defined (choose_ne_undef _ _ _) fun _ _ => pure_ne_undef _

theorem mem_pickFrom {xs : List β} {c : β} (hc : (pickFrom xs : Finite β).Mem c) : c ∈ xs := by
  cases xs with
  | nil => exact absurd hc (not_mem_empty c)
  | cons x xs =>
    have hd : (pickFrom (x :: xs) : Finite β) ≠ .undef := pickFrom_defined _
    unfold pickFrom at hc hd
    obtain ⟨i, _, hi⟩ := (mem_bind hd).mp hc
    exact (mem_singleton.mp hi) ▸ List.getElem_mem _

theorem branches_defined {bs : List (Unit → Finite β)} (h : ∀ b ∈ bs, b () ≠ .undef) :
    (branches bs : Finite β) ≠ .undef :=
  bind_defined (pickFrom_defined _) fun c hc => h c (mem_pickFrom hc)

end Finite

end Specimen
