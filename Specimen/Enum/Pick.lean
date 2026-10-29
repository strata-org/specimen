/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.PlausibleGen
public import Specimen.Enum.Backtrack

/-!
# Weighted Choice Without Retry

`pick` runs one branch, drawn with probability proportional to its weight, and fails if that branch
does: `frequency` for a generator that can fail. It is a class for the reason `Backtrack` is: an
enumeration reads it as the union of its branches, where enumerating the draw would repeat each
branch once per unit of weight. A branch of weight `0` is never run; that some branch has positive
weight is a proof `pick` takes, so `pick` needs no failure of its own and runs where there is none
(`Plausible.Gen`, `SPMF`). `pickOr` is the choice whose weights may all be `0`.
-/

@[expose] public section

namespace Specimen


/-- One branch of positive weight, drawn with probability proportional to its weight, run without
retry. -/
class Pick (G : Type → Type) where
  pick {α : Type} (gs : List (Nat × (Unit → G α)))
    (h : 0 < Backtrack.sumWeights gs := by gen_side_condition) : G α

namespace Pick

open Backtrack

variable {G : Type → Type} {α : Type}

/-- Where failure is `none`, the search with fuel for one branch: a draw by weight, and on failure
no retry. -/
instance instOptionT [Monad G] [RandomChoice G] : Pick (OptionT G) := ⟨fun gs _ => search 1 gs⟩

/-- At an enumeration, the branches of positive weight, side by side: what `backtrack` is there. -/
instance instFinite : Pick Finite := ⟨fun gs _ => Backtrack.backtrack gs⟩

/-- At every size, the choice among the branches at that size. -/
instance instWithSize [Pick G] : Pick (WithSize G) where
  pick gs h n := Pick.pick (gs.map fun p => (p.1, fun _ : Unit => (p.2 ()).run n)) (by simpa using h)

/-- Where nothing fails, `frequency` is the draw. -/
abbrev ofFrequency [Gen G] : Pick G := ⟨fun gs h => frequency gs h⟩

instance instPlausibleGen : Pick Plausible.Gen := ofFrequency

end Pick

/-- The draw among the branches of positive weight, or `dflt` if there are none. -/
def pickOr [Pick G] {α : Type} (dflt : Unit → G α) (gs : List (Nat × (Unit → G α))) : G α :=
  if h : 0 < Backtrack.sumWeights gs then Pick.pick gs h else dflt ()

/-! ## Monotonicity -/

section monotonicity

open Lean.Order Backtrack

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

/-- The monotonicity `pick` must satisfy for a recursive generator that uses it to be definable by
`partial_fixpoint`, branches related as `frequency`'s are. -/
class MonoPick (G : Type → Type) [Pick G] [∀ α, PartialOrder (G α)] where
  pick_mono {α : Type} {gs₁ gs₂ : List (Nat × (Unit → G α))} {h₁ : 0 < sumWeights gs₁}
    {h₂ : 0 < sumWeights gs₂} : gs₁ ⊑ gs₂ → Pick.pick gs₁ h₁ ⊑ Pick.pick gs₂ h₂

@[partial_fixpoint_monotone]
theorem monotone_pick {G : Type → Type} [Pick G] [∀ α, PartialOrder (G α)] [MonoPick G]
    {α : Type} {γ : Sort w} [PartialOrder γ]
    (gs : γ → List (Nat × (Unit → G α))) (h : ∀ x, 0 < sumWeights (gs x)) (hgs : monotone gs) :
    monotone fun x => Pick.pick (gs x) (h x) :=
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
