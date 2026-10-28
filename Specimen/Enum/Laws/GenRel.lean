/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.GenRel

/-!
# Branches related weight for weight

A branch on either side of `GenRel.Weighted` has a partner of the same weight on the other side,
related by `R`; the backtracking laws find the branch a search took this way.
-/

@[expose] public section

namespace Specimen

namespace Weighted

variable {M N : Type → Type} {α : Type} {R : ∀ {α : Type}, M α → N α → Prop}

theorem exists_left {gs' : List (Nat × (Unit → M α))} {gs : List (Nat × (Unit → N α))}
    (hs : GenRel.Weighted @R gs' gs) {p : Nat × (Unit → N α)} (hp : p ∈ gs) :
    ∃ g', (p.1, g') ∈ gs' ∧ R (g' ()) (p.2 ()) := by
  induction hs with
  | nil => cases hp
  | @cons w g' g _ _ h _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨g', List.mem_cons_self .., h⟩
    · obtain ⟨g'', hm, hr⟩ := ih hp
      exact ⟨g'', List.mem_cons_of_mem _ hm, hr⟩

theorem exists_right {gs' : List (Nat × (Unit → M α))} {gs : List (Nat × (Unit → N α))}
    (hs : GenRel.Weighted @R gs' gs) {p : Nat × (Unit → M α)} (hp : p ∈ gs') :
    ∃ g, (p.1, g) ∈ gs ∧ R (p.2 ()) (g ()) := by
  induction hs with
  | nil => cases hp
  | @cons w g' g _ _ h _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨g, List.mem_cons_self .., h⟩
    · obtain ⟨g'', hm, hr⟩ := ih hp
      exact ⟨g'', List.mem_cons_of_mem _ hm, hr⟩

end Weighted

end Specimen
