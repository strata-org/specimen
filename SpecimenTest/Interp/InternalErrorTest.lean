import SpecimenTest.Interp.BSTInterpTest
import SpecimenTest.Interp.CheckEnumTest

/-!
# Internal errors are not discards

The runtime interpreter's `backtrack` absorbed every error as "this branch failed", so an `[interp]`
error inside a callee — an arity mismatch, a leaf that cannot read its argument — came out as "all
branches failed", a definitive discard at the calling step, and another constructor was tried. A rule
that could never run was therefore invisible; that is how the instance-argument bug hid, where every call
from Cedar's `HasType.hasAttrRecordNotFound` to `MapNotContainsKey` died on an arity mismatch. The checker's
`checkerBacktrack` did the same in its own way, turning the error into "inconclusive" and dropping its
message.

The interpreter now uses its own `backtrackInterp` / `checkerBacktrackInterp`, which re-throw
misconfiguration and are otherwise identical. The shared combinators that emitted code uses are untouched,
and the first tests pin both halves of that. Every test after them fails on the old behaviour.

(The compile-time deriver's silent constructor drops are reported by `trace.specimen.droppedCtors`, not
tested here.)
-/

open Lean Plausible Schedules Specimen Specimen.Interp SpecimenTest.InterpBST

namespace SpecimenTest.InterpInternalErrors

/-! ## `backtrackInterp` re-throws internal errors; the shared `backtrack` does not change -/

def brokenGen : Gen Nat := throw (interpError "deliberately broken")
def discardGen : Gen Nat := throw Plausible.Gen.genericFailure

-- Whichever branch is drawn first, the internal error is what comes out. Under `backtrack` this was "all
-- branches failed" under every seed.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let mut ok := true
  for seed in [1, 2, 3, 4, 5, 6, 7, 8] do
    match ← runSeeded (some seed)
        (attempt (backtrackInterp [(1, brokenGen), (1, discardGen)])) 3 with
    | .error e => ok := ok && isInterpError e
    | .ok _ => ok := false
  return ok

-- The emitted-code combinators are untouched: a discard is still absorbed, fuel exhaustion is still
-- inconclusive, and — deliberately — an `[interp]` error is still just a failed branch there, since emitted
-- generators never raise one. `backtrackInterp` absorbs a plain discard exactly as `backtrack` does.
/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  let r₁ ← runSeeded (some 1)
    (attempt (GeneratorCombinators.backtrack [(1, discardGen), (1, (pure 7 : Gen Nat))])) 3
  let r₂ ← runSeeded (some 1)
    (attempt (GeneratorCombinators.backtrackArr #[(1, discardGen), (1, (pure 7 : Gen Nat))])) 3
  let r₃ ← runSeeded (some 1)
    (attempt (GeneratorCombinators.backtrack [(1, (throw Gen.outOfFuelError : Gen Nat)), (1, discardGen)])) 3
  let r₄ ← runSeeded (some 1)
    (attempt (GeneratorCombinators.backtrack [(1, brokenGen), (1, (pure 7 : Gen Nat))])) 3
  let r₅ ← runSeeded (some 1) (attempt (backtrackInterp [(1, discardGen), (1, (pure 7 : Gen Nat))])) 3
  return (r₁ matches .ok 7 && r₂ matches .ok 7 && r₄ matches .ok 7 && r₅ matches .ok 7,
          match r₃ with | .error e => Gen.GenError.isInconclusive e | .ok _ => false,
          true)

/-! ## In the interpreter

    `leaves` with the `≤` checker broken: it cannot read its arguments. `Between.BetweenN` checks `≤`,
    every `Between[1]` call ends in `BetweenN`, and `BST.BstNode` calls `Between[1]` first. -/

def brokenLeaves : InterpEnv :=
  leaves.addChecker ``LE.le (checkerOfList fun _ => .error "deliberately broken")

def brokenEnv : Except String InterpEnv := brokenLeaves.deriveClosure specs [bstKey]

-- The `Check` passes the leaf's `[interp]` answer on instead of calling it a rejection. Before: 0
-- misconfigured, 50 discarded at the check.
/-- info: (50, 0) -/
#guard_msgs in
#eval show IO (Nat × Nat) from do
  match brokenEnv with
  | .error _ => return (0, 0)
  | .ok env => do
    let p ← env.profileCtor betweenKey ``Between.BetweenN 6 [toVal 0, toVal 10] 50 (some 11)
    return (p.interpErrors, p.discards)

-- A *callee's* misconfiguration now reaches `runCtorOnce`. Before, `Between[1]`'s `backtrack` turned it
-- into "all branches failed", which `blaming` filed as 50 discards at `BstNode`'s first step.
/-- info: (50, 0) -/
#guard_msgs in
#eval show IO (Nat × Nat) from do
  match brokenEnv with
  | .error _ => return (0, 0)
  | .ok env => do
    let p ← env.profileCtor bstKey ``BST.BstNode 6 [toVal 0, toVal 10] 50 (some 11)
    return (p.interpErrors, p.discards)

-- From the top. Before, the root `backtrack` fell back to `BstLeaf` every time `BstNode` failed, so every
-- sample succeeded and nothing said the environment was broken.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  match brokenEnv with
  | .error _ => return (false, false)
  | .ok env => do
    let s ← env.sample bstKey 6 [toVal 0, toVal 10] 200 0 (seed := some 11)
    return (s.interpErrors > 0, (s.firstInterpError.getD "").endsWith "deliberately broken")

-- The retry log names where the error started — `Between[1]`'s `BetweenN`, not the root it surfaced
-- from — and keeps it out of the absorbed-failure count.
/-- info: (true, "Between[1] as Generator", `Between.BetweenN) -/
#guard_msgs in
#eval show IO (Bool × String × Name) from do
  match brokenEnv with
  | .error _ => return (false, "", .anonymous)
  | .ok env => do
    let (_, log) ← withRetryLog (env.sample bstKey 6 [toVal 0, toVal 10] 50 0 (seed := some 11))
    match log.firstInternal with
    | some (k, c, _) => return (log.totalInternal > 0, renderSpecKey k, c)
    | none => return (false, "", .anonymous)

-- A mode handed the wrong number of inputs says so at its own frame, with dispatch on or off. Before,
-- every branch failed on the same `bindInputs` mismatch and `backtrack` answered "all branches failed";
-- with `dispatchInputs` the filter could reject every branch first, so not even a branch saw it.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  match derivedEnv with
  | .error _ => return (false, false)
  | .ok env => do
    let run := fun (e : InterpEnv) => runSeeded (some 1)
      (attempt (e.generate betweenKey 6 [toVal 0, toVal 10, toVal 99])) 6
    let isArity := fun (r : Except GenError (List Val)) =>
      match r with | .error e => isInterpError e | .ok _ => false
    return (isArity (← run env), isArity (← run { env with dispatchInputs := true }))

-- A plan whose attempts all died on an internal error no longer outranks one that merely discards.
-- Before, its `discards` were 0, so it scored 0‰ and won.
#guard
  let clean : PlanOutcome := .ran expectedBstNode { attempts := 10, successes := 5 }
    { ctorName := ``BST.BstNode, attempts := 10, successes := 5,
      perStep := [{ stepIdx := 0, rendered := "", discards := 5 }] }
  let dead : PlanOutcome := .ran expectedBstNode { attempts := 10, interpErrors := 10 }
    { ctorName := ``BST.BstNode, attempts := 10, interpErrors := 10 }
  clean.better dead && !dead.better clean

/-! ## Derived checkers are published under the name their callers use

A generator's `Check` on a premise of *another* relation names it (`Source.NonRec`); a check on the same
relation or a mutual sibling names the checker mode's recursive function (`Source.Rec`/`.MutRec`), and
`Gen.checkSource` looks that up by function name. So `publishInterpretedCheckers` installs both names:
under the relation name alone, every Cedar `Check (.MutRec aux_hasTypeRecord_ …)` dies on "no checker for
`aux_…`", and `backtrackInterp` reports it rather than absorbing it. -/

-- Every derived checker mode is reachable both ways after publishing.
/-- info: true -/
#guard_msgs in
#eval match SpecimenTest.InterpCheckEnum.checkerEnv with
  | .error _ => false
  | .ok env =>
    let pub := env.publishInterpretedCheckers
    let checkerModes := env.relations.toList.filter (fun ((k, _) : SpecKey × RelSchedule) =>
      k.deriveSort == DeriveSort.Checker)
    !checkerModes.isEmpty && checkerModes.all (fun ((k, rel) : SpecKey × RelSchedule) =>
      pub.checkers.contains k.inductiveName && pub.checkers.contains rel.recFnName)

end SpecimenTest.InterpInternalErrors
