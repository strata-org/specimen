/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.BacktrackWith
public import Specimen.Enum.Graded

/-!
# Graded Backtracking Over Failures That Say Why

At `ExceptT ε (CostGraded G)` a search is `CostGraded`'s union of the branches unwrapped, labelled
failures being entries like any other: tier `n + 1` is each branch of positive weight at tier `n`.
-/

@[expose] public section

open Lean.Order

namespace Specimen


namespace Backtrack

variable {ε : Type} {G : Type → Type}

/-- The union, one tier up, labelled failures being entries like any other. -/
instance instExceptTCostGraded [Fail G] [Union G] : Backtrack (ExceptT ε (CostGraded G)) :=
  ⟨fun gs => ExceptT.mk (Backtrack.backtrack (gs.map fun p => (p.1, fun u => (p.2 u).run)))⟩

instance instMonoExceptTCostGraded [Gen G] [Fail G] [Union G] [MonoUnion G] :
    MonoBacktrack (ExceptT ε (CostGraded G)) where
  backtrack_mono h := MonoBacktrack.backtrack_mono (G := CostGraded G) (map_runE_rel h)

end Backtrack

namespace Pick

variable {ε : Type} {G : Type → Type}

/-- The same tiers as `backtrack`, as without labels. -/
instance instExceptTCostGraded [Fail G] [Union G] : Pick (ExceptT ε (CostGraded G)) :=
  ⟨fun gs _ => Backtrack.backtrack gs⟩

instance instMonoExceptTCostGraded [Gen G] [Fail G] [Union G] [MonoUnion G] :
    MonoPick (ExceptT ε (CostGraded G)) where
  pick_mono h := MonoBacktrack.backtrack_mono (G := ExceptT ε (CostGraded G)) h

end Pick

end Specimen
