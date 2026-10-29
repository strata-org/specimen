/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.ExceptT
public import Specimen.Enum.Pick

/-!
# Backtracking Over Failures That Say Why

At `ExceptT ε (OptionT G)` a search retries a branch that fails with a label as it does one that is
refuted, and ends refuted only if every branch it tried was; otherwise it fails with the labels it saw
joined by `max`, so the order it tried them in does not show. At `ExceptT ε Finite` both are the union of the
branches, as without labels.
-/

@[expose] public section

open Lean.Order RandomChoice

namespace Specimen


namespace Backtrack

variable {ε : Type} {G : Type → Type} {α : Type}

/-- How a search with nothing left to try ends: refuted if every branch it tried was, otherwise
failed with the labels it saw. -/
def finish [Monad G] : Option ε → OptionT G (Except ε α)
  | none => failure
  | some e => pure (.error e)

/-- The search, a failure with a label retried as a refutation is, the labels joined. Structural on
a fuel of the number of branches. -/
def searchWith [Monad G] [RandomChoice G] [Max ε] :
    Nat → List (Nat × (Unit → ExceptT ε (OptionT G) α)) → Option ε → OptionT G (Except ε α)
  | _, [], acc => finish acc
  | 0, _, acc => finish acc
  | fuel + 1, gs@(_ :: _), acc => OptionT.mk do
    let n ← choose 0 (sumWeights gs - 1) (Nat.zero_le _)
    match pickDrop gs n.down.val with
    | none => (finish acc).run
    | some (_, g, rest) =>
      match ← (g ()).run.run with
      | some (.ok a) => pure (some (.ok a))
      | some (.error e) => (searchWith fuel rest (some (acc.elim e (max · e)))).run
      | none => (searchWith fuel rest acc).run

/-- The search over labelled failures. -/
instance instExceptTOptionT [Monad G] [RandomChoice G] [Max ε] :
    Backtrack (ExceptT ε (OptionT G)) :=
  ⟨fun gs => ExceptT.mk (searchWith gs.length gs none)⟩

/-- The union, labelled failures being entries like any other. -/
instance instExceptTFinite : Backtrack (ExceptT ε Finite) :=
  ⟨fun gs => ExceptT.mk (Backtrack.backtrack (gs.map fun p => (p.1, fun u => (p.2 u).run)))⟩

end Backtrack

namespace Pick

variable {ε : Type} {G : Type → Type}

/-- One draw, no retry: the search with fuel for one branch. -/
instance instExceptTOptionT [Monad G] [RandomChoice G] [Max ε] : Pick (ExceptT ε (OptionT G)) :=
  ⟨fun gs => ExceptT.mk (Backtrack.searchWith 1 gs none)⟩

instance instExceptTFinite : Pick (ExceptT ε Finite) :=
  ⟨fun gs => Backtrack.backtrack gs⟩

end Pick

/-! ## Monotonicity -/

section monotonicity

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

namespace Backtrack

variable {ε : Type}

theorem searchWith_mono {G : Type → Type} [Gen G] [Max ε] {α : Type} :
    ∀ (fuel : Nat) {gs₁ gs₂ : List (Nat × (Unit → ExceptT ε (OptionT G) α))} (acc : Option ε),
      gs₁ ⊑ gs₂ → searchWith fuel gs₁ acc ⊑ searchWith fuel gs₂ acc
  | _, [], [], _, _ => PartialOrder.rel_refl
  | _, [], _ :: _, _, h | _, _ :: _, [], _, h => absurd (length_eq_of_rel h) (by simp)
  | 0, _ :: _, _ :: _, _, _ => PartialOrder.rel_refl
  | fuel + 1, p₁ :: gs₁, p₂ :: gs₂, acc, h => by
    have hw := sumWeights_eq_of_rel h
    refine choose_bind_mono (G := G) (by rw [hw]) fun n _ _ => ?_
    rcases pickDrop_rel h n with ⟨h₁, h₂⟩ | ⟨k, g₁, g₂, r₁, r₂, h₁, h₂, hg, hr⟩
    · simp only [h₁, h₂]
      exact PartialOrder.rel_refl
    · simp only [h₁, h₂]
      refine PartialOrder.rel_trans (MonoBind.bind_mono_left (m := G) (hg ()))
        (MonoBind.bind_mono_right (m := G) fun o => ?_)
      rcases o with _ | _ | _
      · exact searchWith_mono fuel acc hr
      · exact searchWith_mono fuel _ hr
      · exact PartialOrder.rel_refl

/-- Unwrapping `ExceptT` keeps branches related: its order is the base's. -/
theorem map_runE_rel {G : Type → Type} [Gen G] {α : Type} :
    ∀ {gs₁ gs₂ : List (Nat × (Unit → ExceptT ε G α))}, gs₁ ⊑ gs₂ →
      (gs₁.map fun p => (p.1, fun u => (p.2 u).run)) ⊑
        (gs₂.map fun p => (p.1, fun u => (p.2 u).run))
  | [], [], _ => PartialOrder.rel_refl
  | [], _ :: _, h | _ :: _, [], h => absurd (length_eq_of_rel h) (by simp)
  | (w₁, g₁) :: gs₁, (w₂, g₂) :: gs₂, h => by
    obtain ⟨⟨hw, hg⟩, ht⟩ := rel_cons_iff.mp h
    exact rel_cons_iff.mpr ⟨⟨hw, fun u => hg u⟩, map_runE_rel ht⟩

instance instMonoExceptTOptionT {G : Type → Type} [Gen G] [Max ε] :
    MonoBacktrack (ExceptT ε (OptionT G)) where
  backtrack_mono {_ gs₁ gs₂} h := by
    show searchWith gs₁.length gs₁ none ⊑ searchWith gs₂.length gs₂ none
    rw [length_eq_of_rel h]
    exact searchWith_mono _ none h

instance instMonoExceptTFinite : MonoBacktrack (ExceptT ε Finite) where
  backtrack_mono h := MonoBacktrack.backtrack_mono (G := Finite) (map_runE_rel h)

end Backtrack

namespace Pick

variable {ε : Type}

instance instMonoExceptTOptionT {G : Type → Type} [Gen G] [Max ε] :
    MonoPick (ExceptT ε (OptionT G)) where
  pick_mono h := Backtrack.searchWith_mono 1 none h

instance instMonoExceptTFinite : MonoPick (ExceptT ε Finite) where
  pick_mono h := MonoBacktrack.backtrack_mono (G := ExceptT ε Finite) h

end Pick

end monotonicity

end Specimen
