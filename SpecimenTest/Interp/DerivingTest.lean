import Specimen.Interp

/-!
# Deriving `ToVal` and `OfVal`

The bridge is what stops the interpreter being pointed at a real project: Cedar has perfectly good
`Arbitrary` instances for `CedarType`, `Name`, `EntityUID`, `Prim` and the rest, and not one of its
schedules can run, because nothing converts those values into `Val`. Both directions are purely
structural, so they are derived rather than written out per project.

The cases that matter are the ones a hand-written instance gets wrong:

* **nested recursion** — `CedarType.record` holds a `Map Attr (Qualified CedarType)`, so the recursion
  leaves the type, passes through two containers, and comes back. A function that only calls itself on
  same-typed fields cannot do that; the derived one makes its own instance available while being defined.
* **mutual families**, where each type needs the other's instance.
* **wrong shapes**, which must be reported rather than silently mismatched — including the right
  constructor name at the wrong arity.
-/

open Specimen Specimen.Interp

namespace SpecimenTest.InterpDeriving

/-- A plain enumeration: no fields, nothing to recurse into. -/
inductive Colour3 where | red | green | blue
  deriving Repr, DecidableEq, ToVal, OfVal

/-- Directly recursive, with a `Nat` field — which `Val.mkCtor` normalises to a literal, so the derived
    instance agrees with `instToValNat` rather than emitting a `Nat.succ` tower. -/
inductive Tree3 where
  | leaf
  | node (l : Tree3) (v : Nat) (r : Tree3)
  deriving Repr, DecidableEq, ToVal, OfVal

/-- Parametric *and* recursive, with the recursion under a `List`. -/
inductive Rose (α : Type) where
  | mk (v : α) (kids : List (Rose α))
  deriving Repr, ToVal, OfVal

/-- A container that is not the recursive type itself. -/
structure Wrap (α : Type) where
  contents : α
  deriving Repr, ToVal, OfVal

/-- `CedarType.record`'s shape: recursion through `Wrap` and `List` before returning to `Nest`. This is
    the case that needs the family's own instance in scope while the function is being defined. -/
inductive Nest where
  | done
  | more (w : Wrap (List Nest)) (tag : String)
  deriving Repr, ToVal, OfVal

mutual
/-- Half of a mutual family; each constructor mentions the other type. -/
inductive Even3 where | zero | succ (n : Odd3)
/-- The other half. -/
inductive Odd3 where | succ (n : Even3)
end
deriving instance Repr, DecidableEq, ToVal, OfVal for Even3
deriving instance Repr, DecidableEq, ToVal, OfVal for Odd3

-- The name stored in the `Val` is **fully qualified**, which is what `Match` steps compare against.
-- `Val`'s own renderer abbreviates it, so read the field rather than the rendering.
/-- info: (`SpecimenTest.InterpDeriving.Colour3.green, true) -/
#guard_msgs in
#eval match toVal Colour3.green with
  | .ctor n args => (n, args.isEmpty)
  | .lit _ => (`unexpected, false)

-- A `Nat` field lands as a literal rather than a `Nat.succ` tower, so a derived instance agrees with
-- `instToValNat` on a type that happens to contain a `Nat`.
/-- info: node leaf 2 (node leaf 3 leaf) -/
#guard_msgs in
#eval toVal (Tree3.node .leaf 2 (.node .leaf 3 .leaf))

/-- info: (`SpecimenTest.InterpDeriving.Tree3.node, some (Lean.Literal.natVal 2)) -/
#guard_msgs in
#eval match toVal (Tree3.node .leaf 2 .leaf) with
  | .ctor n [_, .lit l, _] => (n, some l)
  | _ => (`unexpected, none)

-- Round trips, on every shape: enum, direct recursion, parametric, nested-through-container, mutual.
/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval
  let roundTrips {α : Type} [ToVal α] [OfVal α] [BEq α] (a : α) : Bool :=
    match (ofVal (toVal a) : Except String α) with
    | .ok b => a == b
    | .error _ => false
  [ roundTrips Colour3.blue
  , roundTrips (Tree3.node .leaf 2 (.node .leaf 3 .leaf))
  , roundTrips (Even3.succ (Odd3.succ Even3.zero))
  , roundTrips (Odd3.succ Even3.zero)
    -- `Rose`/`Nest` have no `BEq`; compare their renderings instead.
  , (match (ofVal (toVal (Rose.mk (1 : Nat) [Rose.mk 2 []])) : Except String (Rose Nat)) with
     | .ok b => reprStr b == reprStr (Rose.mk (1 : Nat) [Rose.mk 2 []])
     | .error _ => false) ]

-- Nested recursion really does traverse, rather than bottoming out at the container.
/-- info: Except.ok "SpecimenTest.InterpDeriving.Nest.more { contents := [SpecimenTest.InterpDeriving.Nest.done] } \"x\"" -/
#guard_msgs in
#eval (ofVal (toVal (Nest.more ⟨[Nest.done]⟩ "x")) : Except String Nest) |>.map reprStr

-- A `Val` of the wrong shape is reported. Both failures matter: an unknown constructor, and the *right*
-- constructor at the wrong arity — the latter would otherwise be a silent mismatch, since arity is part
-- of the pattern rather than checked afterwards.
/-- info: [true, true] -/
#guard_msgs in
#eval
  let isErr {α : Type} (r : Except String α) : Bool :=
    match r with | .error _ => true | .ok _ => false
  [ isErr (ofVal (Val.ctor `Bogus.nope []) : Except String Colour3)
  , isErr (ofVal (Val.ctor ``Tree3.node [toVal Tree3.leaf]) : Except String Tree3) ]

/-- An indexed family, to check the handler declines rather than deriving something wrong. -/
inductive Fin3 : Nat → Type where
  | zero : Fin3 0
  | succ {n : Nat} : Fin3 n → Fin3 (n + 1)

-- An indexed inductive is refused with an explanation rather than deriving something wrong: a `Val`
-- records a constructor and its arguments, and the indices are not recoverable from it.
/-- error: cannot derive Specimen.Interp.ToVal for the indexed inductive type 'SpecimenTest.InterpDeriving.Fin3': a `Val` records a constructor and its arguments, not the indices the type is family-indexed by -/
#guard_msgs in
deriving instance ToVal for Fin3

end SpecimenTest.InterpDeriving
