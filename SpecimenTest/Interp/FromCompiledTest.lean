import Specimen.Interp.FromCompiled
import SpecimenTest.Interp.BSTInterpTest
import SpecimenTest.Interp.PinnedOrderTest

/-!
# Learning from the deriver's own choice

`deriveChoice` claims two things, and each is checked here on `BST`.

1. **The book it returns rebuilds the compiled generator.** Not just for the root: a closure built from
   the book brings up every mode the root needs, and every generator mode the deriver *also* derived
   must lower, constructor for constructor, to the schedule it emitted. `PinnedOrderTest` checks the
   root's constructors against the raw orders; this checks the book end to end, through
   `deriveClosureWith`, which is the path learning actually takes.
2. **Learning can start from it, and the result reads as a diff.** `learnSchedules` from the compiled
   book runs, and `PlanBook.diff` against that book is what learning changed. On `BST` it changes
   nothing — branch and bound already found the discard-free schedule, the closure is ideal, and the
   search stops in its first round — so the diff is empty. A hand-made change shows what a non-empty
   report looks like.
-/

open Lean Schedules Specimen Specimen.Interp SpecimenTest.InterpBST SpecimenTest.PinnedOrder

namespace SpecimenTest.FromCompiled

-- 22 orders over 11 modes, where the closure needs two. The search derives modes speculatively to score
-- candidates it then discards — `BST[1,2]`, `BST[0,1,2]`, `Between[0,1,2]` and five more — and records
-- a settled order for each, plus the `Between` checker. Those entries are harmless in the book (a mode
-- the closure never asks for is never looked up), and only `BST[2]` and `Between[1]` are comparable:
-- all four of their constructors agree.
/-- info: [from-compiled] 22 settled orders, 20 at generator modes; both books' closures reproduce all 4 compiled generator schedules across 2 mode(s) -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let choice ← deriveChoice bstKey
  let mut counts : List (Nat × Nat) := []
  for (label, book) in [("full", choice.book), ("generator-only", choice.generatorBook)] do
    match leaves.deriveClosureWith specs [bstKey] book with
    | .error e => throwError "the closure from the deriver's {label} book did not build: {e}"
    | .ok env =>
      let mut compared := 0
      let mut modes : List SpecKey := []
      let mut bad : List String := []
      for (key, rel) in env.relations.toList do
        if key.deriveSort != .Generator then continue
        for (ctor, sched) in rel.allSchedules do
          let some comp := choice.schedule? key ctor | continue
          -- On `BST` the interpreter's own default already matches the compiled schedule
          -- (`BSTInterpTest`), so agreement alone would pass with the book ignored. Require the book to
          -- be what planned it.
          if (book.find? key ctor).isNone then
            bad := bad ++ [s!"{renderSpecKey key} · {ctor} (not planned from the book)"]
          compared := compared + 1
          unless modes.contains key do modes := modes ++ [key]
          unless normSteps sched.1 == normSteps comp.1 do
            bad := bad ++ [s!"{renderSpecKey key} · {ctor}"]
      unless bad.isEmpty do
        throwError "{label} book: constructors whose closure schedule differs from the compiled one: {bad}"
      counts := counts ++ [(compared, modes.length)]
  let some (compared, modes) := counts.head? | throwError "no closure was built"
  unless counts.all (· == (compared, modes)) do throwError "the two books disagree: {counts}"
  IO.println s!"[from-compiled] {choice.book.size} settled orders, {choice.generatorBook.size} at \
    generator modes; both books' closures reproduce all {compared} compiled generator schedules \
    across {modes} mode(s)"

-- Learning from the compiled book: it builds, measures, finds nothing avoidable, and changes nothing.
/--
info: [from-compiled] last round: ideal: 4 constructor(s) across the closure · worst checking · 0 avoidable rejection(s)
[plan-diff] the learned book agrees with the start book everywhere
-/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let start ← compiledBook bstKey
  let (learned, trace) ← leaves.learnSchedules specs bstKey 4 [toVal 0, toVal 6] (n := 60)
    (rounds := 2) (start := start) (objectiveKind := .coverage)
  match trace.head? with
  | some t => unless t.accepted do throwError "learning could not measure the compiled book: {t.note}"
  | none => throwError "learning returned an empty trace"
  IO.println s!"[from-compiled] last round: {(trace.getLast?.map (·.note)).getD ""}"
  IO.println (PlanBook.renderDiff specs (PlanBook.diff specs start learned))

-- What a real departure renders as: `BstNode` with the tree premise first, which makes `BST lo x l`
-- produce the pivot too and demotes `Between` to a check.
/--
info: [plan-diff] 1 constructor(s) where the learned book departs from the start book:
  BST[2] as Generator · BST.BstNode
    start   [0, 1, 2]  Between lo x hi; BST lo x l; BST x hi r
    learned [1, 0, 2]  BST lo x l; Between lo x hi; BST x hi r
-/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let start ← compiledBook bstKey
  let learned := start.set bstKey ``BST.BstNode [.use 1, .use 0, .use 2]
  IO.println (PlanBook.renderDiff specs (PlanBook.diff specs start learned))

-- Two plans that differ as lists but lower to one schedule are not a change: with the tree premise
-- first, `Between` is settled at once and hoisted to a check, so `[1, 0, 2]` and `[1, 2, 0]` agree.
-- An elective `inst` is a change, and is flagged as unpinnable.
/--
info: [plan-diff] the learned book agrees with the start book everywhere
[plan-diff] 1 constructor(s) where the learned book departs from the start book:
  BST[2] as Generator · BST.BstNode
    start   [0, 1, 2]  Between lo x hi; BST lo x l; BST x hi r
    learned [x←, 0, 1, 2]  x ← arbitrary; Between lo x hi; BST lo x l; BST x hi r
    ! not pinnable: elective inst of [x]
-/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let start ← compiledBook bstKey
  let a := start.set bstKey ``BST.BstNode [.use 1, .use 0, .use 2]
  let b := start.set bstKey ``BST.BstNode [.use 1, .use 2, .use 0]
  IO.println (PlanBook.renderDiff specs (PlanBook.diff specs a b))
  let c := start.set bstKey ``BST.BstNode [.inst `x, .use 0, .use 1, .use 2]
  IO.println (PlanBook.renderDiff specs (PlanBook.diff specs start c))

-- `deriveChoice` answers for branch and bound, not for a pin in force, and leaves the pinned and the
-- recorded orders as it found them: a pin installed for a `derive_mutual` elsewhere in the file must neither leak into the choice
-- nor be lost, and the choice must not pick up orders recorded before it.
/-- info: [from-compiled] pin ignored and restored; earlier recorded orders excluded and restored -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let pin : PinnedOrders := [(bstKey, ``BST.BstNode, [2, 1, 0])]
  let earlier : PinnedOrders := [(bstKey, `earlier, [7])]
  PinnedOrders.install pin
  setChosenOrders earlier
  let c ← deriveChoice bstKey
  let pinsAfter ← getPinnedOrders
  let chosenAfter ← getChosenOrders
  PinnedOrders.install []
  setChosenOrders []
  unless c.orders.find? bstKey ``BST.BstNode == some [0, 1, 2] do
    throwError "the pin leaked into the choice: {c.orders.find? bstKey ``BST.BstNode}"
  if c.orders.any (fun (_, n, _) => n == `earlier) then
    throwError "orders recorded before the call leaked into the choice"
  unless pinsAfter.find? bstKey ``BST.BstNode == some [2, 1, 0] && pinsAfter.length == 1 do
    throwError "the pin was not restored"
  unless chosenAfter.length == 1 && chosenAfter.find? bstKey `earlier == some [7] do
    throwError "the earlier recorded orders were not restored"
  IO.println "[from-compiled] pin ignored and restored; earlier recorded orders excluded and restored"

-- A book read off the deriver is keyed at `typeArgs := []`, the only keys the compile-time pipeline
-- mints, so an instantiated mode of a polymorphic relation falls back to it; its own entry still wins.
-- The fallback is for type arguments only, never for a different mode.
def instantiatedKey : SpecKey := { bstKey with typeArgs := ["0:Nat"] }
#guard (PlanBook.ofOrders [(bstKey, ``BST.BstNode, [2, 1, 0])]).find? instantiatedKey ``BST.BstNode
  == some [.use 2, .use 1, .use 0]
#guard ((PlanBook.ofOrders [(bstKey, ``BST.BstNode, [2, 1, 0])]).set instantiatedKey ``BST.BstNode
  [.use 0, .use 1, .use 2]).find? instantiatedKey ``BST.BstNode == some [.use 0, .use 1, .use 2]
#guard (PlanBook.ofOrders [(bstKey, ``BST.BstNode, [2, 1, 0])]).find?
  { instantiatedKey with outputIndices := [1, 2] } ``BST.BstNode == none

end SpecimenTest.FromCompiled
