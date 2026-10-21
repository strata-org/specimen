import Basalt.Graded
import Basalt.GradedSound

/-!
# The `Graded` algebra, pinned by its interpretations

`Basalt/Graded.lean` claims two things that are easy to break silently. This file holds them down.

**One body, three interpretations.** `treeStep` below is written against `Graded` alone and specialises
to values, cardinality and specification. If someone adds a `bind` to `Graded`, the `Cnt` instance stops
existing and this file stops compiling — which is the point, because that is the mistake worth catching.

**The split is forced, not stylistic.** `Cnt α := Nat → Nat` is *phantom* in `α`, so `bind`'s
continuation could never be invoked; and `guard` is value-dependent, which the last test measures
directly — two enumerations with identical count profiles have different guarded counts. So with any
checked premise, `Cnt` is an upper bound rather than exact.

The recursive occurrence is passed in as a parameter rather than tied recursively. That is the same shape
`Producer.iterate`'s `step` has, and it is what keeps the body structurally recursive when iterated —
recursing at an unbounded index `enum (n - i)` inside `pair` would not pass the termination checker.
-/

open Basalt

/-- Uniquely named and not `Tree`: the suite already has a root-level `inductive Tree` that collides
with `DeriveTreeGenerator`. Not `private`, so `#eval` prints a readable constructor name. -/
inductive GradedTestTree where
  | leaf
  | node : GradedTestTree → GradedTestTree → GradedTestTree
  deriving Repr, DecidableEq

/-- One level of the grammar `T ::= leaf | node T T`, written against `Graded` only. -/
private def treeStep [Graded f] (rec : f GradedTestTree) : f GradedTestTree :=
  Choice.union (Graded.single GradedTestTree.leaf)
    (Graded.pay (Graded.gmap (fun p => GradedTestTree.node p.1 p.2) (Graded.pair rec rec)))

private def treeIter [Graded f] : Nat → f GradedTestTree
  | 0 => Choice.nothing
  | n + 1 => treeStep (treeIter n)

-- Counting gives the Catalan numbers — level `n` is the trees with `n` internal nodes. This is the
-- whole reason `Graded` is applicative: the count is computable without ever seeing a value.
/-- info: [1, 1, 2, 5, 14, 42, 132] -/
#guard_msgs in
#eval ((List.range 7).map fun n => (treeIter (f := Cnt) 8 n : Nat))

-- The *same body* at the value interpretation must agree with the counts.
/-- info: [1, 1, 2, 5, 14, 42, 132] -/
#guard_msgs in
#eval ((List.range 7).map fun n => (treeIter (f := Lv) 8 n).length)

-- Levels are *disjoint* — level `n` holds exactly the size-`n` trees, not everything up to `n`. That is
-- what makes each value produced once, unlike a cumulative budget that re-enumerates every smaller level.
/-- info: [GradedTestTree.leaf] -/
#guard_msgs in
#eval (treeIter (f := Lv) 8 0)

-- `guard` is value-dependent, so it cannot live in `Graded`: these two enumerations have identical
-- count profiles and different guarded counts.
/-- info: profiles equal: true, guarded counts: 1 vs 2 -/
#guard_msgs in
#eval (do
  let x : Lv Nat := Choice.union (Graded.single 0) (Graded.single 1)
  let y : Lv Nat := Choice.union (Graded.single 0) (Graded.single 2)
  let keepEven : Nat → V := fun k => if k % 2 == 0 then .yes else .no
  let px := (List.range 3).map fun n => (x n).length
  let py := (List.range 3).map fun n => (y n).length
  IO.println s!"profiles equal: {px == py}, guarded counts: \
    {(GradedBind.guard keepEven x 0).length} vs {(GradedBind.guard keepEven y 0).length}"
  : IO Unit)

-- `inconclusive` keeps the element, flagged inconclusive, rather than dropping it — dropping would be an
-- unsound completeness claim.
/-- info: [(0, true), (1, false)] -/
#guard_msgs in
#eval (
  let x : Lv Nat := Choice.union (Graded.single 0) (Graded.single 1)
  let p : Nat → V := fun k => if k == 0 then .yes else .inconclusive
  GradedBind.guard p x 0)

/-! ## Graded leaves

The invariant that lets levels replace a round-robin interleave is that *every* enumeration is graded, so
no level is infinite. These pin it for the leaves: each level below is finite, and `Nat`'s are singletons
rather than "all of `Nat` at level 0". -/

-- `Nat` graded by magnitude: level `n` is exactly `{n}`.
/-- info: [[0], [1], [2], [3], [4]] -/
#guard_msgs in
#eval ((List.range 5).map fun n => gradedIter (f := Lv) natStep 8 n)

-- ... so every level has exactly one element — finite, which is the whole point.
/-- info: [1, 1, 1, 1, 1] -/
#guard_msgs in
#eval ((List.range 5).map fun n => (gradedIter (f := Cnt) natStep 8 n : Nat))

-- `Bool` is finite, so it lives entirely at level 0 and later levels are empty.
/-- info: [2, 0, 0] -/
#guard_msgs in
#eval ((List.range 3).map fun n => (gradedIter (f := Cnt) boolStep 8 n : Nat))

-- `List Bool`: a cons costs one level, and the element enumeration contributes 2 at level 0, so the
-- counts double — `2 ^ n` lists of length `n`. Convolution with a level-0-only element degenerates to
-- exactly that, which is the sanity check that `pair` is accounting correctly.
/-- info: [1, 2, 4, 8, 16] -/
#guard_msgs in
#eval ((List.range 5).map fun n =>
  (gradedIter (f := Cnt) (listStep (gradedIter boolStep 8)) 8 n : Nat))

-- The same body at the value interpretation agrees, and level 2 really is the length-2 lists.
/-- info: [[false, false], [false, true], [true, false], [true, true]] -/
#guard_msgs in
#eval (gradedIter (f := Lv) (listStep (gradedIter boolStep 8)) 8 2)

/-! ## The same agreements, as theorems

The `#eval`s above pin concrete *numbers* — that level 4 really has 14 trees, that level 2 really is the
four length-2 lists. `Basalt/GradedSound.lean` pins the *correspondence*, for every level and every
number of levels rather than the handful sampled here. Both are wanted: the theorems cannot notice if
`pair` is uniformly wrong in a way all three carriers share, and the `#eval`s cannot cover all `n`.

Assembling them for `treeStep` costs three lines, which is the property being demonstrated — a new
enumeration shape reuses the per-operation closure lemmas instead of reproving anything. -/

private theorem agrees_treeStep (x : Lv GradedTestTree) (s : SetE GradedTestTree) (h : Agrees x s) :
    Agrees (treeStep x) (treeStep s) :=
  (agrees_single GradedTestTree.leaf).union (((h.pair h).gmap _).pay)

private theorem counts_treeStep (x : Lv GradedTestTree) (c : Cnt GradedTestTree) (h : Counts x c) :
    Counts (treeStep x) (treeStep c) :=
  (counts_single GradedTestTree.leaf).union (((h.pair h).gmap _).pay)

private theorem agrees_treeIter : ∀ levels, Agrees (treeIter levels) (treeIter levels)
  | 0 => agrees_nothing
  | n + 1 => agrees_treeStep _ _ (agrees_treeIter n)

private theorem counts_treeIter : ∀ levels, Counts (treeIter levels) (treeIter levels)
  | 0 => counts_nothing
  | n + 1 => counts_treeStep _ _ (counts_treeIter n)

/-- The Catalan agreement the two `#eval`s above sample, for all levels and all `n`: the value
enumeration's level `n` has exactly as many elements as the cardinality interpretation says. -/
theorem treeIter_length_eq_count (levels n : Nat) :
    (treeIter (f := Lv) levels n).length = treeIter (f := Cnt) levels n :=
  counts_treeIter levels n

/-- And the values are exactly the specified ones — `→` soundness, `←` completeness, at level `n`
precisely rather than merely somewhere within budget. -/
theorem treeIter_mem_iff (levels n : Nat) (t : GradedTestTree) :
    t ∈ treeIter (f := Lv) levels n ↔ treeIter (f := SetE) levels n t :=
  agrees_treeIter levels n t
