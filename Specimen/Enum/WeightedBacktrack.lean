/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Mathlib.Algebra.Field.Rat
public import Specimen.Enum.Backtrack
public import Specimen.Enum.Weighted
public import Specimen.Enum.Pick

/-!
# Backtracking at `WFinite`

The exact distribution of `backtrack`: each branch of positive weight run once, its entries weighted
by the probability that the search reaches it. Running the search here instead would list an entry
per order of retries; this lists one per entry of a branch. `pick` is the same with one draw.
-/

@[expose] public section

open Lean.Order

namespace Specimen


namespace Backtrack

variable {β S ι : Type}

/-- Each entry, with the others in order. -/
def picks : List β → List (β × List β)
  | [] => []
  | p :: rest => (p, rest) :: (picks rest).map fun e => (e.1, p :: e.2)

/-- The search's average over branches `(weight, failure probability, index)`: a branch drawn by
weight contributes `v` of its index, and on failure the search goes on among the rest; `b` once none
is left to draw. Structural on a fuel of the number of branches, as `search` is. -/
def mix [Semiring S] [Inv S] (v : ι → S) (b : S) : Nat → List (Nat × S × ι) → S
  | 0, _ => b
  | fuel + 1, ds =>
    if sumWeights ds = 0 then b
    else (sumWeights ds : S)⁻¹ *
      ((picks ds).map fun e => (e.1.1 : S) * (v e.1.2.2 + e.1.2.1 * mix v b fuel e.2)).sum

/-- The entries whose bit is set in `m`, in order. -/
def subMask : List β → Nat → List β
  | [], _ => []
  | d :: ds, m => if m % 2 = 1 then d :: subMask ds (m / 2) else subMask ds (m / 2)

/-- `G` at each entry whose bit is set in `m`, and `m` with that bit cleared. -/
def maskSum [AddMonoid S] : List β → Nat → (β → Nat → S) → S
  | [], _, _ => 0
  | d :: ds, m, G => (if m % 2 = 1 then G d (m - 1) else 0) +
    maskSum ds (m / 2) fun x m' => G x (2 * m' + m % 2)

/-- `mix` at the branches of mask `m`, from its values at smaller masks. -/
def mixStep [Semiring S] [Inv S] (v : ι → S) (b : S) (ds : List (Nat × S × ι)) (T : Array S)
    (m : Nat) : S :=
  let r := subMask ds m
  if sumWeights r = 0 then b
  else (sumWeights r : S)⁻¹ * maskSum ds m fun d m' => (d.1 : S) * (v d.2.2 + d.2.1 * T.getD m' b)

/-- `mix` at every mask, in increasing order. -/
def mixTable [Semiring S] [Inv S] (v : ι → S) (b : S) (ds : List (Nat × S × ι)) : Array S :=
  (List.range (2 ^ ds.length)).foldl (fun T m => T.push (mixStep v b ds T m)) #[]

/-- `mix` over every branch, computed once per set of branches left rather than once per order
of retries (`mixDP_eq`). -/
def mixDP [Semiring S] [Inv S] (v : ι → S) (b : S) (ds : List (Nat × S × ι)) : S :=
  (mixTable v b ds).getD (2 ^ ds.length - 1) b

end Backtrack

namespace WFinite

variable {α : Type}

/-- What the entries' weights leave of `1`: a defined `WFinite` is a finite tree, so the missing
mass is failure. -/
def failMass : WFinite α → ℚ≥0
  | .undef => 0
  | .mk _ f => Rat.toNNRat (1 - (List.ofFn fun i => (f i).2).sum)

/-- Each branch's weight and result, a branch of weight `0` not run. -/
def runBranches (gs : List (Nat × (Unit → WFinite α))) : List (Nat × WFinite α) :=
  gs.map fun p => (p.1, if p.1 = 0 then Finite.empty else p.2 ())

/-- The probability that the search reaches branch `i`. -/
def reach (ys : List (Nat × WFinite α)) (i : Fin ys.length) : ℚ≥0 :=
  Backtrack.mixDP (fun j => if j = i then 1 else 0) 0
    (List.ofFn fun j : Fin ys.length => (ys[j].1, failMass ys[j].2, j))

/-- Each branch's entries, weighted by `r` of it. -/
def runWith (ys : List (Nat × WFinite α)) (r : Fin ys.length → ℚ≥0) : WFinite α :=
  Finite.flatten (List.ofFn fun i : Fin ys.length =>
    Finite.map (fun q => (q.1, (r i : ℚ) * q.2)) ys[i].2)

/-- Each branch's entries, weighted by the probability that the search reaches it. -/
def backtrackRun (ys : List (Nat × WFinite α)) : WFinite α := runWith ys (reach ys)

/-- The probability that one draw picks branch `i`: the search's, with fuel for one. -/
def pickReach (ys : List (Nat × WFinite α)) (i : Fin ys.length) : ℚ≥0 :=
  Backtrack.mix (fun j => if j = i then 1 else 0) 0 1
    (List.ofFn fun j : Fin ys.length => (ys[j].1, failMass ys[j].2, j))

/-- The search's distribution: an entry per entry of a branch of positive weight, `undef` if one
is. -/
instance instBacktrack : Backtrack WFinite where
  backtrack gs := backtrackRun (runBranches gs)

/-- The draw's distribution: each branch's entries weighted by its share of the weight. -/
instance instPick : Pick WFinite where
  pick gs := runWith (runBranches gs) (pickReach (runBranches gs))

end WFinite

/-! ## Monotonicity -/

section monotonicity

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

namespace WFinite

variable {α : Type}

theorem runWith_eq_undef {ys : List (Nat × WFinite α)} {r : Fin ys.length → ℚ≥0} {i : Fin ys.length}
    (h : ys[i].2 = .undef) : runWith ys r = .undef :=
  Finite.flatten_eq_undef (List.mem_ofFn.mpr ⟨i, by simp only [h]; rfl⟩)

/-- Anything the branches' results determine, `undef` where one of them is, is monotone in the
branches: a branch `undef` on the left makes the left `undef`, and otherwise the branches are the
same. -/
theorem runBranches_mono {β : Type} (F : List (Nat × WFinite α) → WFinite β)
    (hF : ∀ ys (i : Fin ys.length), ys[i].2 = .undef → F ys = .undef)
    {gs₁ gs₂ : List (Nat × (Unit → WFinite α))} (h : gs₁ ⊑ gs₂) :
    F (runBranches gs₁) ⊑ F (runBranches gs₂) := by
  by_cases hu : ∃ i : Fin (runBranches gs₁).length, (runBranches gs₁)[i].2 = .undef
  · obtain ⟨i, hi⟩ := hu
    rw [hF _ i hi]
    exact FlatOrder.rel.bot
  · push Not at hu
    suffices hys : runBranches gs₁ = runBranches gs₂ by rw [hys]; exact PartialOrder.rel_refl
    refine List.ext_getElem (by simp [runBranches, h.1]) fun i h₁ h₂ => ?_
    have hi := hu ⟨i, h₁⟩
    simp only [runBranches, List.length_map] at h₁ h₂
    obtain ⟨hw, hg⟩ := h.2 i h₁ h₂
    simp only [runBranches, List.getElem_map, Fin.getElem_fin] at hi ⊢
    rw [hw] at hi ⊢
    by_cases hw0 : gs₂[i].1 = 0
    · simp [hw0]
    · simp only [hw0, ↓reduceIte] at hi ⊢
      rcases Finite.eq_undef_or_eq (hg ()) with h' | h'
      · exact absurd h' hi
      · rw [h']

/-- Weighting the branches by anything they determine is monotone in them. -/
theorem runWith_runBranches_mono (r : ∀ ys : List (Nat × WFinite α), Fin ys.length → ℚ≥0)
    {gs₁ gs₂ : List (Nat × (Unit → WFinite α))} (h : gs₁ ⊑ gs₂) :
    runWith (runBranches gs₁) (r _) ⊑ runWith (runBranches gs₂) (r _) :=
  runBranches_mono (fun ys => runWith ys (r ys)) (fun _ _ hi => runWith_eq_undef hi) h

instance instMonoBacktrack : MonoBacktrack WFinite where
  backtrack_mono h := runWith_runBranches_mono reach h

instance instMonoPick : MonoPick WFinite where
  pick_mono h := runWith_runBranches_mono pickReach h

end WFinite

end monotonicity

end Specimen
