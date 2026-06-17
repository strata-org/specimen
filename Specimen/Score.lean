import Lean

open Lean

/-- A type-erased score value. Used by the modular scoring framework.
    All scoring layers agree on the same concrete type (enforced by the registry),
    so casts between layers always succeed. -/
structure Score where
  val : Dynamic
  reprFn : Dynamic → String := fun _ => "<score>"

private structure ScorePlaceholder deriving TypeName
instance : Inhabited Score := ⟨{ val := Dynamic.mk ({} : ScorePlaceholder) }⟩
instance : Repr Score where reprPrec s _ := s.reprFn s.val
