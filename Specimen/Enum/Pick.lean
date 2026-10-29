/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Backtrack

/-!
# Weighted Choice Without Retry

`pick` runs one branch, drawn with probability proportional to its weight, and fails if that branch
does: `frequency` for a generator that can fail. It is a class for the reason `Backtrack` is: an
enumeration reads it as the union of its branches, where enumerating the draw would repeat each
branch once per unit of weight.
-/

@[expose] public section

namespace Specimen


/-- One branch, drawn with probability proportional to its weight, run without retry; `fail` if
every weight is `0`. -/
class Pick (G : Type → Type) where
  pick {α : Type} : List (Nat × (Unit → G α)) → G α

namespace Pick

open Backtrack

variable {G : Type → Type} {α : Type}

/-- Where failure is `none`, the search with fuel for one branch: a draw by weight, and on failure
no retry. -/
instance instOptionT [Monad G] [RandomChoice G] : Pick (OptionT G) := ⟨fun gs => search 1 gs⟩

/-- At an enumeration, the branches of positive weight, side by side: what `backtrack` is there. -/
instance instFinite : Pick Finite := ⟨fun gs => Backtrack.backtrack gs⟩

/-- At every size, the choice among the branches at that size. -/
instance instWithSize [Pick G] : Pick (WithSize G) where
  pick gs n := Pick.pick (gs.map fun p => (p.1, fun _ : Unit => (p.2 ()).run n))

end Pick

/-! ## Monotonicity -/

section monotonicity

open Lean.Order Backtrack

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

/-- The monotonicity `pick` must satisfy for a recursive generator that uses it to be definable by
`partial_fixpoint`, branches related as `frequency`'s are. -/
class MonoPick (G : Type → Type) [Pick G] [∀ α, PartialOrder (G α)] where
  pick_mono {α : Type} {gs₁ gs₂ : List (Nat × (Unit → G α))} :
    gs₁ ⊑ gs₂ → Pick.pick gs₁ ⊑ Pick.pick gs₂

@[partial_fixpoint_monotone]
theorem monotone_pick {G : Type → Type} [Pick G] [∀ α, PartialOrder (G α)] [MonoPick G]
    {α : Type} {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Nat × (Unit → G α))) (hgs : monotone gs) :
    monotone fun x => Pick.pick (gs x) :=
  fun x y hxy => MonoPick.pick_mono (hgs x y hxy)

namespace Pick

instance instMonoFinite : MonoPick Finite where
  pick_mono h := MonoBacktrack.backtrack_mono (G := Finite) h

instance instMonoOptionT {G : Type → Type} [Gen G] : MonoPick (OptionT G) where
  pick_mono h := search_mono 1 h

instance instMonoWithSize {G : Type → Type} [Gen G] [Pick G] [MonoPick G] :
    MonoPick (WithSize G) where
  pick_mono h n := MonoPick.pick_mono (G := G) (map_run_rel n h)

end Pick

end monotonicity

end Specimen
