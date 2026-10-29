/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Backtrack
public import Specimen.Enum.Weighted
public import Specimen.Enum.Pick

/-!
# Graded Enumeration

Two ways to bucket a generator's outputs, neither asking anything of the generator.

* **By size**, for a sized generator: `WithSize G`, bucket `n` being what it produces at size `n`,
  the size its author reads with `sized`. Under exact sizing (`Sized.pay`/`splitBind`/`done`) these
  are FEAT's tiers; under a size that biases choices, `WithSize WFinite`'s buckets are the
  distributions drawn from at each size.
* **By cost**, for any generator: `CostGraded G`, bucket `n` being what it produces in exactly `n`
  choices — `SPMF.Cost`'s notion of cost, indexed rather than tagged.

`CostGraded G` is FEAT's convolution over any enumeration interpretation `G`: `bind` takes, for
every way to split the cost `n`, `x` at `k` and its continuation at `n - k`, and unions them; `pure`
costs nothing and a `choose` exactly one. The split has to be a union without weights — every split,
each path keeping its own weight — so `G` supplies one (`Union`). Only an enumeration has such a
thing: a random interpretation cannot take both branches, and building the split from `choose`
would make it a random choice, weighting every path by `1 / (n + 1)` per split. (That is what
`Sized.splitBind` does, rightly: written into a generator, the random split is the program.)
`CostGraded Finite` is the cost-graded enumeration, and `CostGraded WFinite` the same with each
path's probability.

Indexed, not tagged: a tagged `Finite (α × Nat)` is the whole enumeration at once, `undef` for a
generator with an infinite support, whereas tier `n` here depends only on smaller tiers, so every
tier is finite and defined for a geometric list or `genType`. A tier is `undef` only where the
generator recurses without choosing: a generator that is not productive.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen


/-- A union without weights: both sides, every entry as it was. What an enumeration has and a random
interpretation does not. -/
class Union (G : Type → Type) where
  union : G α → G α → G α

/-- The monotonicity `Union` needs for a `partial_fixpoint` through `CostGraded`. -/
class MonoUnion (G : Type → Type) [Union G] [∀ α, PartialOrder (G α)] where
  union_mono {x₁ x₂ y₁ y₂ : G α} : x₁ ⊑ x₂ → y₁ ⊑ y₂ → Union.union x₁ y₁ ⊑ Union.union x₂ y₂

instance : Union Finite := ⟨Finite.union⟩
instance : MonoUnion Finite := ⟨Finite.union_mono⟩
instance : Union WFinite := ⟨Finite.union⟩
instance : MonoUnion WFinite := ⟨Finite.union_mono⟩

/-- `G`, graded by the number of choices a run makes. -/
def CostGraded (G : Type → Type) (α : Type) : Type := Nat → G α

namespace CostGraded

variable {G : Type → Type} {α β : Type}

/-- The union over every split of `n`: `x` at `k`, its continuation at `n - k`. -/
def bind [Monad G] [Fail G] [Union G] (x : CostGraded G α) (f : α → CostGraded G β) :
    CostGraded G β := fun n =>
  (List.range (n + 1)).foldr (fun k acc => Union.union (x k >>= fun a => f a (n - k)) acc) Fail.fail

instance [Monad G] [Fail G] [Union G] : Monad (CostGraded G) where
  pure a n := if n = 0 then pure a else Fail.fail
  bind := CostGraded.bind

/-- Every value of the range, for exactly one choice. -/
instance [Monad G] [Fail G] [RandomChoice G] : RandomChoice (CostGraded G) where
  choose lo hi h n := if n = 1 then RandomChoice.choose lo hi h else Fail.fail

instance [Fail G] : Fail (CostGraded G) := ⟨fun _ => Fail.fail⟩

instance [Gen G] : Inhabited (CostGraded G α) := ⟨fun _ => default⟩

instance instCCPO [Gen G] : CCPO (CostGraded G α) := inferInstanceAs (CCPO (Nat → G α))

theorem foldr_union_mono [Gen G] [Union G] [MonoUnion G] {z : G β} {l : List Nat}
    {f₁ f₂ : Nat → G β} (h : ∀ k, f₁ k ⊑ f₂ k) :
    l.foldr (fun k acc => Union.union (f₁ k) acc) z ⊑ l.foldr (fun k acc => Union.union (f₂ k) acc) z := by
  induction l with
  | nil => exact PartialOrder.rel_refl
  | cons k l ih => exact MonoUnion.union_mono (h k) ih

instance [Gen G] [Fail G] [Union G] [MonoUnion G] : MonoBind (CostGraded G) where
  bind_mono_left h _ := foldr_union_mono fun k => MonoBind.bind_mono_left (h k)
  bind_mono_right h _ := foldr_union_mono fun _ => MonoBind.bind_mono_right fun a => h a _

/-- The branches of positive weight at cost `n`, unioned: `backtrack`'s tier `n + 1`. -/
def backtrackTier [Fail G] [Union G] (gs : List (Nat × (Unit → CostGraded G α))) (n : Nat) : G α :=
  gs.foldr (fun p acc => if p.1 = 0 then acc else Union.union (p.2 () n) acc) Fail.fail

/-- At cost `n + 1`, the branches of positive weight at cost `n`, the pick being one choice; at cost
`0`, nothing. That is the cost of a search whose first pick succeeds. A search that fails other
branches first reaches the same values at higher costs, which no tier lists, so the tiers are
complete only up to cost (`CostEnumeratesSome`). -/
instance instBacktrack [Fail G] [Union G] : Backtrack (CostGraded G) where
  backtrack gs
    | 0 => Fail.fail
    | n + 1 => backtrackTier gs n

/-- The same tiers as `backtrack`: the draw costs one choice, and its branch what it costs. With no
retry, the tiers are exact for `pick`; `CostEnumeratesSome` asks only that they be complete up to
cost. -/
instance instPick [Fail G] [Union G] : Pick (CostGraded G) := ⟨fun gs _ => Backtrack.backtrack gs⟩

section monotonicity

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

theorem backtrackTier_mono [Gen G] [Fail G] [Union G] [MonoUnion G] (n : Nat) :
    ∀ {gs₁ gs₂ : List (Nat × (Unit → CostGraded G α))}, gs₁ ⊑ gs₂ →
      backtrackTier gs₁ n ⊑ backtrackTier gs₂ n
  | [], [], _ => PartialOrder.rel_refl
  | [], _ :: _, h | _ :: _, [], h => absurd (Backtrack.length_eq_of_rel h) (by simp)
  | (w₁, g₁) :: gs₁, (w₂, g₂) :: gs₂, h => by
    obtain ⟨⟨hw, hg⟩, ht⟩ := Backtrack.rel_cons_iff.mp h
    simp only at hw
    subst hw
    by_cases hw0 : w₁ = 0
    · simpa [backtrackTier, hw0] using backtrackTier_mono n ht
    · simp only [backtrackTier, List.foldr_cons, hw0, ↓reduceIte]
      exact MonoUnion.union_mono (hg () n) (backtrackTier_mono n ht)

instance instMonoBacktrack [Gen G] [Fail G] [Union G] [MonoUnion G] :
    MonoBacktrack (CostGraded G) where
  backtrack_mono h
    | 0 => PartialOrder.rel_refl
    | n + 1 => backtrackTier_mono n h

instance instMonoPick [Gen G] [Fail G] [Union G] [MonoUnion G] : MonoPick (CostGraded G) where
  pick_mono h := MonoBacktrack.backtrack_mono (G := CostGraded G) h

end monotonicity

/-- The entries of cost exactly `n`, if defined. -/
def tier? (x : CostGraded Finite α) (n : Nat) : Option (List α) := (x n).toList?

/-- How many entries (paths) cost exactly `n`. -/
def card? (x : CostGraded Finite α) (n : Nat) : Option Nat := (x n).card?

/-- The first entry of the cheapest tier up to `b` that has one, the tiers tried in order, so no
costlier tier is built: the smallest witness a checker's premise wants. -/
def firstUpTo? (x : CostGraded Finite α) (b : Nat) : Option α :=
  (List.range (b + 1)).findSome? fun n => (x n).get? 0

/-- The paths costing at most `b`, with their probabilities, if every tier up to `b` is defined. -/
def upTo? (x : CostGraded WFinite α) (b : Nat) : Option (List (α × Rat)) :=
  ((List.range (b + 1)).mapM fun n => WFinite.entries? (x n)).map List.flatten

end CostGraded

end Specimen
