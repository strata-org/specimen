/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.BacktrackWith
public import Specimen.Enum.WeightedBacktrack

/-!
# Backtracking Over Failures That Say Why, at `WFinite`

The exact distribution of `backtrack` over labelled failures, each branch of positive weight run
once: its successes weighted by the probability that the search reaches them, as without labels, and
its failure the join of the branches' own, each branch failing independently, one entry per label.
`pick` weights each branch's entries, labels included, by its share of the weight.
-/

@[expose] public section

open Lean.Order

namespace Specimen


namespace WFinite

variable {ε α β : Type}

/-- `p` added to the entries, its weight added to an entry's with the same value. -/
def addEntry [DecidableEq β] (p : β × Rat) : List (β × Rat) → List (β × Rat)
  | [] => [p]
  | q :: qs => if q.1 = p.1 then (q.1, q.2 + p.2) :: qs else q :: addEntry p qs

/-- One entry per value, weighted by the total weight of its entries, entries of weight `0`
dropped. -/
def merge [DecidableEq β] : WFinite β → WFinite β
  | .undef => .undef
  | .mk _ f =>
    let l := ((List.ofFn f).foldr addEntry []).filter fun p => p.2 ≠ 0
    .mk l.length fun i => l[i]

/-- The successes of a run. -/
def oks (y : WFinite (Except ε α)) : WFinite α :=
  WFinite.bind y fun r => match r with
    | .ok a => (pure a : WFinite α)
    | .error _ => Fail.fail

/-- How a run fails: refuted with what its entries leave of `1`, or with each label it fails with. -/
def failures (y : WFinite (Except ε α)) : WFinite (Option ε) :=
  Finite.union (Finite.singleton (none, (failMass y : Rat)))
    (WFinite.bind y fun r => match r with
      | .ok _ => Fail.fail
      | .error l => (pure (some l) : WFinite (Option ε)))

/-- How the branches so far failed, joined with how one more fails, run independently. -/
def joinStep [Max ε] [DecidableEq ε] (D : WFinite (Option ε)) (y : WFinite (Except ε α)) :
    WFinite (Option ε) :=
  merge (WFinite.bind D fun acc =>
    WFinite.bind (failures y) fun o => (pure (Option.merge max acc o) : WFinite (Option ε)))

/-- How every branch failing ends the search: refuted if every one was, else the labels joined. -/
def joinFailures [Max ε] [DecidableEq ε] (ys : List (Nat × WFinite (Except ε α))) :
    WFinite (Option ε) :=
  ys.foldl (fun D p => joinStep D p.2) (pure none : WFinite (Option ε))

/-- The search's distribution from its branches' results: the successes as `backtrack` weighs them,
then the labels the search ends with. -/
def backtrackWithRun [Max ε] [DecidableEq ε] (ys : List (Nat × WFinite (Except ε α))) :
    WFinite (Except ε α) :=
  Finite.union
    (Finite.map (fun q => (.ok q.1, q.2)) (backtrackRun (ys.map fun p => (p.1, oks p.2))))
    (WFinite.bind (joinFailures ys) fun o => match o with
      | none => Fail.fail
      | some l => (pure (.error l) : WFinite (Except ε α)))

/-- The search over labelled failures: an entry per success of a branch of positive weight and one
per label, `undef` if a branch of positive weight is. -/
instance instBacktrackExceptT [Max ε] [DecidableEq ε] : Backtrack (ExceptT ε WFinite) where
  backtrack gs :=
    ExceptT.mk (backtrackWithRun (runBranches (gs.map fun p => (p.1, fun u => (p.2 u).run))))

/-- The draw over labelled failures: each branch's entries weighted by its share of the weight. -/
instance instPickExceptT : Pick (ExceptT ε WFinite) where
  pick gs h := ExceptT.mk (Pick.pick (gs.map fun p => (p.1, fun u => (p.2 u).run)) (by simpa using h))

end WFinite

/-! ## Monotonicity -/

section monotonicity

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

namespace WFinite

variable {ε α : Type}

theorem backtrackWithRun_eq_undef [Max ε] [DecidableEq ε] {ys : List (Nat × WFinite (Except ε α))}
    (i : Fin ys.length) (hi : ys[i].2 = .undef) : backtrackWithRun ys = .undef := by
  have h : backtrackRun (ys.map fun p => (p.1, oks p.2)) = .undef :=
    runWith_eq_undef (i := ⟨i, by simp⟩) (by
      simp only [List.getElem_map, Fin.getElem_fin]
      rw [show ys[i.val].2 = .undef from hi]
      rfl)
  simp only [backtrackWithRun, h]
  rfl

instance instMonoBacktrackExceptT [Max ε] [DecidableEq ε] : MonoBacktrack (ExceptT ε WFinite) where
  backtrack_mono h := runBranches_mono backtrackWithRun (fun _ i hi => backtrackWithRun_eq_undef i hi)
    (Backtrack.map_runE_rel h)

instance instMonoPickExceptT : MonoPick (ExceptT ε WFinite) where
  pick_mono {_ _ _ h₁ h₂} h :=
    MonoPick.pick_mono (G := WFinite) (h₁ := by simpa using h₁) (h₂ := by simpa using h₂)
      (Backtrack.map_runE_rel h)

end WFinite

end monotonicity

end Specimen
