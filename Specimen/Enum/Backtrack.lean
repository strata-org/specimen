/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.Combinators
public import Specimen.Enum.Fail
public import Specimen.Enum.Finite
public import Basalt.Sized

/-!
# Weighted Backtracking

`backtrack` tries weighted branches in a random order, without replacement, until one does not fail.
It is a class because what that means depends on the interpretation: a search where failure can be
observed (`OptionT G`), and the union of the branches at an enumeration (`Finite`).
-/

@[expose] public section

namespace Specimen


variable {G : Type → Type} in
/-- No value at any size. -/
instance instFailWithSize [Fail G] : Fail (WithSize G) := ⟨fun _ => Fail.fail⟩

/-- Try the branches, each drawn with probability proportional to its weight among those not yet
tried, until one does not fail; fail if every one does. A branch of weight `0` is never tried.

Not `Alternative`: `x <|> y` tries `x` first, so an enumeration reading it as a union would list
values of `y` its distribution never produces. Here every branch of positive weight is tried first
with positive probability, so its values are exactly the branches' values, and an enumeration may
read it as their union (`EnumeratesSome.backtrack`). -/
class Backtrack (G : Type → Type) where
  backtrack {α : Type} : List (Nat × (Unit → G α)) → G α

namespace Backtrack

variable {G : Type → Type} {α β : Type}

/-- The total weight. -/
def sumWeights (gs : List (Nat × β)) : Nat := (gs.map Prod.fst).sum

@[simp] theorem sumWeights_nil : sumWeights ([] : List (Nat × β)) = 0 := rfl

@[simp] theorem sumWeights_cons (p : Nat × β) (rest : List (Nat × β)) :
    sumWeights (p :: rest) = p.1 + sumWeights rest := by
  simp [sumWeights]

/-- The entry whose weight interval contains `n`, its weight, and the others; `none` past the total
weight. -/
def pickDrop : List (Nat × β) → Nat → Option (Nat × β × List (Nat × β))
  | [], _ => none
  | (k, g) :: rest, n =>
    if n < k then some (k, g, rest)
    else (pickDrop rest (n - k)).map fun (k', g', rest') => (k', g', (k, g) :: rest')

open RandomChoice in
/-- The search, with failure observed as `none`: draw a branch by weight, and on `none` draw again
from the rest. Structural on a fuel of the number of branches. -/
def search [Monad G] [RandomChoice G] : Nat → List (Nat × (Unit → OptionT G α)) → OptionT G α
  | _, [] => failure
  | 0, _ => failure
  | fuel + 1, gs@(_ :: _) => OptionT.mk do
    let n ← choose 0 (sumWeights gs - 1) (Nat.zero_le _)
    match pickDrop gs n.down.val with
    | none => pure none
    | some (_, g, rest) =>
      match ← (g ()).run with
      | some a => pure (some a)
      | none => (search fuel rest).run

/-- Where failure is `none`, the search itself. -/
instance instOptionT [Monad G] [RandomChoice G] : Backtrack (OptionT G) where
  backtrack gs := search gs.length gs

/-- At an enumeration, the branches of positive weight, side by side. Running the search here
instead would enumerate the search: one path per unit of weight and per order of retries, each
repeating the values of the branches it tries. -/
instance instFinite : Backtrack Finite where
  backtrack gs := Finite.flatten (gs.filterMap fun p => if p.1 = 0 then none else some (p.2 ()))

/-- At every size, the backtracking of the branches at that size. -/
instance instWithSize [Backtrack G] : Backtrack (WithSize G) where
  backtrack gs n := Backtrack.backtrack (gs.map fun p => (p.1, fun _ : Unit => (p.2 ()).run n))

end Backtrack

/-! ## Monotonicity -/

section monotonicity

open Lean.Order

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

/-- The monotonicity `backtrack` must satisfy for a recursive generator that uses it to be definable
by `partial_fixpoint`; the analogue of `MonoBind` for `Backtrack`. Branches are related as
`frequency`'s are: weight for weight, each pair related. -/
class MonoBacktrack (G : Type → Type) [Backtrack G] [∀ α, PartialOrder (G α)] where
  backtrack_mono {α : Type} {gs₁ gs₂ : List (Nat × (Unit → G α))} :
    gs₁ ⊑ gs₂ → Backtrack.backtrack gs₁ ⊑ Backtrack.backtrack gs₂

@[partial_fixpoint_monotone]
theorem monotone_backtrack {G : Type → Type} [Backtrack G] [∀ α, PartialOrder (G α)]
    [MonoBacktrack G] {α : Type} {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Nat × (Unit → G α))) (hgs : monotone gs) :
    monotone fun x => Backtrack.backtrack (gs x) :=
  fun x y hxy => MonoBacktrack.backtrack_mono (hgs x y hxy)

namespace Backtrack

variable {β : Type}

theorem rel_cons_iff [PartialOrder β] {a b : β} {as bs : List β} :
    (a :: as) ⊑ (b :: bs) ↔ a ⊑ b ∧ as ⊑ bs := by
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨h 0 (by simp) (by simp), by simpa using hl, fun i h1 h2 => ?_⟩
    have := h (i + 1) (by simp; omega) (by simp; omega)
    rwa [List.getElem_cons_succ, List.getElem_cons_succ] at this
  · rintro ⟨hab, hl, h⟩
    refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
    cases i with
    | zero => simpa using hab
    | succ i => simpa using h i (by simp at h1; omega) (by simp at h2; omega)

theorem length_eq_of_rel [PartialOrder β] {as bs : List β} (h : as ⊑ bs) :
    as.length = bs.length := h.1

theorem sumWeights_eq_of_rel [PartialOrder β] :
    ∀ {gs₁ gs₂ : List (Nat × β)}, gs₁ ⊑ gs₂ → sumWeights gs₁ = sumWeights gs₂
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => absurd (length_eq_of_rel h) (by simp)
  | _ :: _, _ :: _, h => by
    obtain ⟨⟨hw, _⟩, ht⟩ := rel_cons_iff.mp h
    rw [sumWeights_cons, sumWeights_cons, hw, sumWeights_eq_of_rel ht]

/-- Related lists select related entries at every offset, with related rests. -/
theorem pickDrop_rel [PartialOrder β] :
    ∀ {gs₁ gs₂ : List (Nat × β)}, gs₁ ⊑ gs₂ → ∀ n,
      (pickDrop gs₁ n = none ∧ pickDrop gs₂ n = none) ∨
      ∃ k g₁ g₂ r₁ r₂, pickDrop gs₁ n = some (k, g₁, r₁) ∧ pickDrop gs₂ n = some (k, g₂, r₂) ∧
        g₁ ⊑ g₂ ∧ r₁ ⊑ r₂
  | [], [], _, _ => .inl ⟨rfl, rfl⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => absurd (length_eq_of_rel h) (by simp)
  | (w₁, g₁) :: gs₁, (w₂, g₂) :: gs₂, h, n => by
    obtain ⟨⟨hw, hg⟩, ht⟩ := rel_cons_iff.mp h
    simp only at hw
    subst hw
    by_cases hn : n < w₁
    · exact .inr ⟨w₁, g₁, g₂, gs₁, gs₂, by simp [pickDrop, hn], by simp [pickDrop, hn], hg, ht⟩
    · simp only [pickDrop, hn, ↓reduceIte]
      rcases pickDrop_rel ht (n - w₁) with ⟨h₁, h₂⟩ | ⟨k, g₁', g₂', r₁, r₂, h₁, h₂, hg', hr⟩
      · exact .inl ⟨by simp [h₁], by simp [h₂]⟩
      · exact .inr ⟨k, g₁', g₂', (w₁, g₁) :: r₁, (w₁, g₂) :: r₂, by simp [h₁], by simp [h₂], hg',
          rel_cons_iff.mpr ⟨⟨rfl, hg⟩, hr⟩⟩

theorem flatten_branches_mono {α : Type} :
    ∀ {gs₁ gs₂ : List (Nat × (Unit → Finite α))}, gs₁ ⊑ gs₂ →
      Finite.flatten (gs₁.filterMap fun p => if p.1 = 0 then none else some (p.2 ())) ⊑
        Finite.flatten (gs₂.filterMap fun p => if p.1 = 0 then none else some (p.2 ()))
  | [], [], _ => PartialOrder.rel_refl
  | [], _ :: _, h | _ :: _, [], h => absurd (length_eq_of_rel h) (by simp)
  | (w₁, g₁) :: gs₁, (w₂, g₂) :: gs₂, h => by
    obtain ⟨⟨hw, hg⟩, ht⟩ := rel_cons_iff.mp h
    simp only at hw
    subst hw
    by_cases hw0 : w₁ = 0
    · simpa [hw0] using flatten_branches_mono ht
    · simp only [List.filterMap_cons, hw0, ↓reduceIte]
      exact Finite.union_mono (hg ()) (flatten_branches_mono ht)

instance instMonoFinite : MonoBacktrack Finite where
  backtrack_mono h := flatten_branches_mono h

/-- Two draws from the same range, followed by continuations related at every value. -/
theorem choose_bind_mono {G : Type → Type} [Gen G] {β : Type} {s₁ s₂ : Nat} (hs : s₁ = s₂)
    {h₁ : 0 ≤ s₁} {h₂ : 0 ≤ s₂} {k₁ : ULift {x : Nat // 0 ≤ x ∧ x ≤ s₁} → G β}
    {k₂ : ULift {x : Nat // 0 ≤ x ∧ x ≤ s₂} → G β}
    (hk : ∀ n hn₁ hn₂, k₁ (.up ⟨n, hn₁⟩) ⊑ k₂ (.up ⟨n, hn₂⟩)) :
    (RandomChoice.choose 0 s₁ h₁ >>= k₁) ⊑ (RandomChoice.choose 0 s₂ h₂ >>= k₂) := by
  subst hs
  exact MonoBind.bind_mono_right fun ⟨⟨n, hn⟩⟩ => hk n hn hn

theorem search_mono {G : Type → Type} [Gen G] {α : Type} :
    ∀ (fuel : Nat) {gs₁ gs₂ : List (Nat × (Unit → OptionT G α))}, gs₁ ⊑ gs₂ →
      search fuel gs₁ ⊑ search fuel gs₂
  | _, [], [], _ => PartialOrder.rel_refl
  | _, [], _ :: _, h | _, _ :: _, [], h => absurd (length_eq_of_rel h) (by simp)
  | 0, _ :: _, _ :: _, _ => PartialOrder.rel_refl
  | fuel + 1, p₁ :: gs₁, p₂ :: gs₂, h => by
    have hw := sumWeights_eq_of_rel h
    refine choose_bind_mono (G := G) (by rw [hw]) fun n _ _ => ?_
    rcases pickDrop_rel h n with ⟨h₁, h₂⟩ | ⟨k, g₁, g₂, r₁, r₂, h₁, h₂, hg, hr⟩
    · simp only [h₁, h₂]
      exact PartialOrder.rel_refl
    · simp only [h₁, h₂]
      refine PartialOrder.rel_trans (MonoBind.bind_mono_left (m := G) (hg ()))
        (MonoBind.bind_mono_right (m := G) fun o => ?_)
      cases o with
      | some _ => exact PartialOrder.rel_refl
      | none => exact search_mono fuel hr

instance instMonoOptionT {G : Type → Type} [Gen G] : MonoBacktrack (OptionT G) where
  backtrack_mono {_ gs₁ gs₂} h := by
    show search gs₁.length gs₁ ⊑ search gs₂.length gs₂
    rw [length_eq_of_rel h]
    exact search_mono _ h

theorem map_run_rel {G : Type → Type} [Gen G] {α : Type} (n : Nat) :
    ∀ {gs₁ gs₂ : List (Nat × (Unit → WithSize G α))}, gs₁ ⊑ gs₂ →
      (gs₁.map fun p => (p.1, fun _ : Unit => (p.2 ()).run n)) ⊑
        (gs₂.map fun p => (p.1, fun _ : Unit => (p.2 ()).run n))
  | [], [], _ => PartialOrder.rel_refl
  | [], _ :: _, h | _ :: _, [], h => absurd (length_eq_of_rel h) (by simp)
  | (w₁, g₁) :: gs₁, (w₂, g₂) :: gs₂, h => by
    obtain ⟨⟨hw, hg⟩, ht⟩ := rel_cons_iff.mp h
    exact rel_cons_iff.mpr ⟨⟨hw, fun _ => hg () n⟩, map_run_rel n ht⟩

instance instMonoWithSize {G : Type → Type} [Gen G] [Backtrack G] [MonoBacktrack G] :
    MonoBacktrack (WithSize G) where
  backtrack_mono h n := MonoBacktrack.backtrack_mono (G := G) (map_run_rel n h)

end Backtrack

end monotonicity

end Specimen
