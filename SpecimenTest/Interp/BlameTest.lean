import Specimen.Interp.Blame
import SpecimenTest.Interp.BSTInterpTest

/-!
# Dataflow and blame

`Interp.Dataflow` reads what each step of an installed schedule reads and binds, and `Interp.Blame` turns a
root sample's retry log into premises worth reordering. These pin the parts that are easy to get subtly
wrong: which names a step reads, who bound them, whether a rejection was decided by the mode's inputs, and
that every candidate move can be pinned.
-/

open Lean Schedules Specimen Specimen.Interp SpecimenTest.InterpBST

namespace SpecimenTest.InterpBlame

/-- Everything the tests read off one derived closure. Bundled and `Option`-free at the use sites, since
    `InterpEnv` and `Schedule` have no `Inhabited` instance to `.get!` through. -/
structure Fixture where
  env : InterpEnv
  node : CtorSpec
  nodeSched : Schedule
  nodeProv : CtorProvenance
  nodeInputs : List Name
  betweenSched : Schedule
  betweenInputs : List Name

def fixture? : Option Fixture := do
  let env ← (leaves.deriveClosureWith specs [bstKey] ({} : PlanBook)).toOption
  let node ← bstSpec.ctors.find? (·.ctorName == ``BST.BstNode)
  let bst ← env.relations[bstKey]?
  let btw ← env.relations[betweenKey]?
  let nodeSched ← bst.ctorSchedule? ``BST.BstNode
  let nodeProv ← bst.provenanceOf? ``BST.BstNode
  let betweenSched ← btw.ctorSchedule? ``Between.BetweenN
  return { env, node, nodeSched, nodeProv, nodeInputs := bst.inputNames, betweenSched,
           betweenInputs := btw.inputNames }

/-- Runs `f` on the fixture, reporting `none` if the closure did not come up as expected — so a broken
    fixture reads as a failure rather than as a passing vacuous test. -/
def onFixture {α : Type} (f : Fixture → α) : Option α := fixture?.map f

/-! ## A booked candidate is what the closure installs

The learner compares a candidate's measurement against the incumbent's; if the closure quietly kept the
incumbent's order, every candidate would tie and nothing would ever be learned, with no error anywhere.
`BookMeasure.installs` guards each measurement; this pins that the guard passes on real candidates. -/

/-- info: some true -/
#guard_msgs in
#eval onFixture fun fx =>
  let cands := levelCandidates bstSpec bstKey fx.node fx.nodeProv.plan [0, 1, 2]
  !cands.isEmpty && cands.all (fun ((p, _) : Plan × Schedule) =>
    match leaves.deriveClosureWith specs [bstKey] (({} : PlanBook).set bstKey ``BST.BstNode p) with
    | .ok env => ((env.relations[bstKey]?).bind (·.provenanceOf? ``BST.BstNode)).map (·.plan) == some p
    | .error _ => false)

/-! ## Reads and binds

`BstNode`'s schedule at `BST[2]`: the bounds come in as inputs, `Between lo x hi` produces `x`, then the
two recursive calls produce the subtrees. Every step's reads must be bound before it. -/

-- No step reads a name that nothing bound: inputs, or an earlier step's binding.
/-- info: some true -/
#guard_msgs in
#eval onFixture fun fx =>
  let fs := Dataflow.flows fx.nodeInputs fx.nodeSched.1
  (fs.zipIdx).all (fun ((f : Dataflow.StepFlow), i) =>
    f.reads.all (fun v => (Dataflow.binderOf fx.nodeInputs fs v i).isSome))

-- Every variable the schedule binds is bound exactly once; the inputs are never re-bound.
/-- info: some true -/
#guard_msgs in
#eval onFixture fun fx =>
  let fs := Dataflow.flows fx.nodeInputs fx.nodeSched.1
  let bound := fs.flatMap (·.binds)
  bound.length == bound.eraseDups.length && fx.nodeInputs.all (fun v => !bound.contains v)

/-! ## The chain

`BstNode`'s premises are `Between lo x hi` (0), `BST lo x l` (1), `BST x hi r` (2). Each recursive call
reads `x`, which `Between` produced, so the chain from either of them reaches premise 0 — and that is the
premise a mutation should consider, not just the one that rejected. -/

/-- info: some (true, true) -/
#guard_msgs in
#eval onFixture fun fx =>
  let chain := Dataflow.chainOf fx.nodeInputs fx.nodeSched.1 fx.nodeProv.origins fx.node 1
  ((chain.levels[0]?) == some [1], (chain.levels[1]?) == some [0])

-- `Between`'s own chain reaches the inputs (`lo`, `hi`) and no producer, so its rejections are the
-- caller's to fix — which is what licenses going up a frame.
/-- info: some (true, true) -/
#guard_msgs in
#eval onFixture fun fx =>
  let chain := Dataflow.chainOf fx.nodeInputs fx.nodeSched.1 fx.nodeProv.origins fx.node 0
  (chain.levels.length == 1, chain.readsInputs)

/-! ## Input-determined rejections

`Between[1]`'s `BetweenN` checks `lo ≤ x` and `x ≤ hi` against values its caller chose. Every `Check` in it
reads only input-determined names, so `failsOnInputs` holds — the signal that blame belongs up a frame. -/

/-- info: some true -/
#guard_msgs in
#eval onFixture fun fx =>
  let steps := fx.betweenSched.1
  let checks := steps.zipIdx.filterMap (fun ((st : ScheduleStep), i) =>
    match st with | .Check .. => some i | _ => none)
  !checks.isEmpty && checks.all (Dataflow.failsOnInputs fx.betweenInputs steps)

/-! ## Candidates are pinnable

Every anchor move that lowers is a premise order — `repair` inserts only the `inst`s an order *forces* —
so `toPinnedOrders` keeps all of them. This is what the old `inst`-inserting generator could not promise:
on Cedar 184 of 240 of its candidates could not be pinned. -/

/-- info: some true -/
#guard_msgs in
#eval onFixture fun fx =>
  let cands := levelCandidates bstSpec bstKey fx.node fx.nodeProv.plan [0, 1, 2]
  !cands.isEmpty && cands.all (fun ((p, _) : Plan × Schedule) =>
    (PlanBook.unpinnableInsts bstSpec bstKey fx.node p).isNone)

-- The installed schedule is never offered back, and no two candidates lower to the same schedule.
/-- info: some (true, true) -/
#guard_msgs in
#eval onFixture fun fx =>
  let cands := levelCandidates bstSpec bstKey fx.node fx.nodeProv.plan [0, 1, 2]
  let scheds := cands.map (fun ((_, s) : Plan × Schedule) => s.1)
  (!scheds.contains fx.nodeSched.1, scheds.length == scheds.eraseDups.length)

/-! ## Blame from a sample

With `attributeNoApply`, a mode whose every constructor is refused on its inputs reports that, so a call to
it is blamed at the *call site* rather than inside the callee. `BST 5 6` is the standing example: no `x`
satisfies `5 ≤ x ≤ 6`… except 5 and 6, so `Between` mostly refuses, and `BstNode` is blamed for calling it. -/

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let some fx := fixture? | return false
  let env := { fx.env with attributeNoApply := true }
  let (_, log) ← withRetryLog (env.sample bstKey 4 [toVal 5, toVal 6] 200 0 (some 11))
  let causes := env.rootCausesOf log
  -- Something is blamed, every blamed premise really is a premise of its constructor, and nothing is
  -- attributed to a prologue step.
  return !causes.isEmpty && causes.all (fun t =>
    match specs.find? (·.inductiveName == t.key.inductiveName) with
    | some rel => (rel.ctors.find? (·.ctorName == t.ctorName)).any (fun c => t.premise < c.hypotheses.length)
    | none => false)

-- Attribution does not change what is generated: the same seed gives the same successes either way.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let some fx := fixture? | return false
  let a ← fx.env.sample bstKey 4 [toVal 0, toVal 10] 200 0 (some 11)
  let b ← { fx.env with attributeNoApply := true }.sample bstKey 4 [toVal 0, toVal 10] 200 0 (some 11)
  return a.successes == b.successes && a.kPathCount == b.kPathCount


/-! ## Rule paths count only the derivations that were kept

A rule path is recorded when a constructor branch succeeds, but the branch's parent can still fail and
discard it. Under a plan that builds both subtrees *before* checking `Between`, that happens constantly.
Every kept derivation node records exactly one path, ending in its own constructor, and every `BST` node
is a `Leaf` or `Node` of the output — so the paths ending in a `BST` constructor must number exactly the
`Leaf`s and `Node`s generated. Without the rollback in `tryCatchPaths` they outnumber them. -/

/-- info: (true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  let late : Plan := [.use 1, .use 2, .use 0]
  match leaves.deriveClosureWith specs [bstKey] (({} : PlanBook).set bstKey ``BST.BstNode late) with
  | .error _ => return (false, false)
  | .ok env =>
    let ((outs, log), paths) ← withRulePathsAll (withRetryLog
      (runSeeded (some 11) (attemptN 100 (env.generate bstKey 5 [toVal 0, toVal 10])) 5))
    let nodes := (outs.filterMap (·.toOption)).foldl (fun acc vs =>
      acc + ((vs.flatMap Val.ctorNames).filter (fun n =>
        n == ``BinaryTree.Leaf || n == ``BinaryTree.Node)).length) 0
    let bstPaths := paths.filter (fun p =>
      p.getLast? == some ``BST.BstLeaf || p.getLast? == some ``BST.BstNode)
    return (log.totalFailures > 0, bstPaths.length == nodes)


/-! ## Per-premise floors

`drawSplit` with minimums meets each minimum first, as far as the budget reaches, and never hands out
more than the budget; with no minimums it is the even split draw for draw. -/

/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  let mut met := true
  let mut within := true
  let mut same := true
  for seed in List.range 50 do
    for n in [0, 1, 2, 3, 5, 8] do
      let parts ← runSeeded (some seed) (drawSplit .starsAndBars n 2 1000 [2, 0]) n
      met := met && (parts.headD 0 ≥ min 2 n)
      within := within && (parts.foldl (· + ·) 0 ≤ n) && parts.length == 2
      let plain ← runSeeded (some seed) (drawSplit .starsAndBars n 2 1000) n
      let plain' ← runSeeded (some seed) (drawSplitEven .starsAndBars n 2 1000) n
      same := same && plain == plain'
  return (met, within, same)

end SpecimenTest.InterpBlame
