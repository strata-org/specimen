import Specimen
import Specimen.Interp
import SpecimenTest.CommonDefinitions.BinaryTree
import SpecimenTest.Interp.BSTInterpTest

/-!
# Round-trip: does a pinned premise order reproduce the schedule the interpreter measured?

Pinning transfers an *order*; a measurement is about a *schedule*. Those coincide only if the
compile-time deriver's lowering and the interpreter's `reschedule` agree, and they are two independent
implementations of the same transformation — which has gone wrong before here
(`patternOfConstructorExpr` keeping `.TyCtor` args made every `LubRecord.cons` attempt fail, and silently
disabled STLC's `lookup`).

Compared **up to the self-recursion name**. `Source.Rec` carries the name the emitted code calls itself
by, and the two sides mint it differently — the deriver from `defaultRecFnName deriveSort`, the
interpreter from its `RelSpec`'s own `recFnName` — so raw equality fails on `aux_arb` vs `aux_bst` while
the steps are structurally identical. `MutRec` is deliberately *not* normalised: there the name selects
which sibling is called, so erasing it would hide a real difference.

Both orders are checked. The declared one is the weak case; `[1, 0, 2]` is the real test, since putting
`BST lo x l` first makes that premise produce both `x` and `l` — a call to `BST[1,2]`, a mode no
unpinned derivation produces — and demotes `Between` to a check.
-/

open Lean Schedules Specimen Specimen.Interp SpecimenTest.InterpBST

namespace SpecimenTest.PinnedOrder

/-- Erase the self-recursion name so the two lowerings are comparable. -/
def normSource : Source → Source
  | .Rec _ args => .Rec `«self» args
  | s => s

def normStep : ScheduleStep → ScheduleStep
  | .Unconstrained v src ps => .Unconstrained v (normSource src) ps
  -- Output *type* annotations are erased too: the interpreter is untyped by design and records `none`
  -- where the deriver records `some (TyCtor Nat [])`. Structurally identical.
  | .SuchThat outs src ps => .SuchThat (outs.map (fun (n, _) => (n, none))) (normSource src) ps
  | .Check src pol => .Check (normSource src) pol
  | s => s

def normSteps (steps : List ScheduleStep) : List ScheduleStep := steps.map normStep

def bstNodeCtor? : Option CtorSpec :=
  bstSpec.ctors.find? (fun c => c.ctorName == ``BST.BstNode)

/-- Lowers `order` with the interpreter, pins the same order into the deriver, and reports whether the
    two agree (up to the normalisations above). -/
def roundTrip (order : List Nat) : Elab.Command.CommandElabM Bool := do
  let some c := bstNodeCtor? | return false
  let plan : Plan := order.map PlanStep.use
  match repair bstSpec bstKey c plan with
  | .error e =>
    IO.println s!"order {order}: interpreter refused the plan: {e.message}"
    return false
  | .ok (repaired, interpSched) =>
    let memo ← IO.mkRef (∅ : Std.HashMap SpecKey MemoEntry)
    pinnedOrdersRef.set [(bstKey, ``BST.BstNode, order)]
    try
      -- `derive_mutual` sets `multiOutput` via `withScope`; a direct call must do the same, or it runs
      -- the deprecated single-output path where a premise order does not determine the schedule.
      Elab.Command.withScope (fun sc => { sc with opts := sc.opts.set `specimen.multiOutput true }) do
        let _ ← Elab.Command.liftTermElabM (deriveBestInductiveSchedule bstKey memo)
    catch e =>
      IO.println s!"order {order}: derivation failed: {(← e.toMessageData.toString).take 300}"
    pinnedOrdersRef.set []
    let m ← memo.get
    match m[bstKey]? with
    | some (.done indSched) =>
      let all := indSched.baseSchedules ++ indSched.recSchedules
      match all.find? (fun p => p.1 == ``BST.BstNode) with
      | none =>
        IO.println s!"order {order}: no BstNode schedule; has {all.map Prod.fst}"
        return false
      | some (_, compiledSched) =>
        let a := normSteps compiledSched.1
        let b := normSteps interpSched.1
        unless a == b do
          IO.println s!"order {order} · plan: {ppPlan c repaired} — MISMATCH"
          for (x, y) in a.zip b do
            if x != y then
              IO.println s!"    compiled: {repr x}"
              IO.println s!"    interp  : {repr y}"
              break
          if a.length != b.length then
            IO.println s!"    length differs: {a.length} vs {b.length}"
        return a == b
    | some (.failed msg) =>
      IO.println s!"order {order}: derivation recorded failure: {msg}"
      return false
    | _ =>
      IO.println s!"order {order}: no schedule in memo"
      return false

-- Every permutation of `BstNode`'s three premises must lower identically on both sides.
--
-- `[0,1,2]` is the declared order and the weak case. `[1,0,2]` puts `BST lo x l` first, so that premise
-- produces both `x` and `l` — a call to `BST[1,2]`, a mode no unpinned derivation produces — and demotes
-- `Between` to a check. `[2,1,0]` is the case that caught the check-placement divergence: the deriver
-- promotes a premise to a check as soon as its arguments are settled, and the interpreter now does the
-- same (`rescheduleLowered`'s `hoistChecks`).
#eval show Elab.Command.CommandElabM Unit from do
  let mut bad : List (List Nat) := []
  for order in [[0, 1, 2], [1, 0, 2], [2, 1, 0], [0, 2, 1], [1, 2, 0], [2, 0, 1]] do
    unless ← roundTrip order do bad := bad ++ [order]
  if bad.isEmpty then
    IO.println "[pinned-order] all 6 premise orders round-trip identically"
  else
    throwError "pinned orders that did not round-trip: {bad}"

/-! ## Does the emitted pin table compile?

`toPinnedOrdersSource` claims to emit *compilable* Lean, which is the only reason its names are
`` ` ``` ``-quoted: a pin naming a constructor that has been renamed should fail here rather than
silently never matching at derive time. Pinning the string would not check that claim, so the emitted
text is parsed and elaborated instead. -/

def sourceBook : PlanBook :=
  { entries := [(bstKey, ``BST.BstNode, [2, 1, 0].map PlanStep.use)] }

-- `ofInterpDefaults` is the book meant for compile time (pinned constructors skip the search; no saving is
-- quoted until it is re-measured — see its docstring). It must book *every* constructor that has a viable
-- plan, since a constructor left unpinned is one that still pays for the search.
#guard (PlanBook.ofInterpDefaults bstSpec bstKey).size == bstSpec.ctors.length

#eval show Elab.Command.CommandElabM Unit from do
  let src := sourceBook.toPinnedOrdersSource [bstSpec] "bstPinnedOrders"
  -- Elaborate it command by command, exactly as pasting it into a file would.
  for cmd in src.splitOn "\n\n" do
    let cmd := cmd.trim
    if cmd.isEmpty || cmd.startsWith "--" then continue
    match Parser.runParserCategory (← getEnv) `command cmd with
    | .error e => throwError "emitted pin source does not parse: {e}\n{cmd}"
    | .ok stx => Elab.Command.elabCommand stx
  -- `run_cmd PinnedOrders.install` is part of what was emitted, so the ref now holds the pin.
  let installed ← pinnedOrdersRef.get
  pinnedOrdersRef.set []
  unless installed.find? bstKey ``BST.BstNode == some [2, 1, 0] do
    throwError "emitted source elaborated but installed {repr installed}"
  IO.println "[pinned-order] emitted pin table compiles and installs the order it names"

/-! ## Starting from the deriver's own choice

Learning should begin from what `derive_mutual`'s branch and bound settled on, not from the interpreter's
default. That needs the settled order back out (`chosenOrdersRef`), and it is only a faithful starting
point if the interpreter lowers that order to the *same schedule* the deriver emitted — for every
constructor, not just the pinned one above. -/

#eval show Elab.Command.CommandElabM Unit from do
  chosenOrdersRef.set []
  let memo ← IO.mkRef (∅ : Std.HashMap SpecKey MemoEntry)
  Elab.Command.withScope (fun sc => { sc with opts := sc.opts.set `specimen.multiOutput true }) do
    let _ ← Elab.Command.liftTermElabM (deriveBestInductiveSchedule bstKey memo)
  let chosen := (← chosenOrdersRef.get).filter (fun (k, _, _) => k == bstKey)
  let some (.done ind) := (← memo.get)[bstKey]? | throwError "BST did not derive"
  let compiled := ind.baseSchedules ++ ind.recSchedules
  unless chosen.length == bstSpec.ctors.length do
    throwError "recorded {chosen.length} settled orders for {bstSpec.ctors.length} constructors"
  let book := PlanBook.ofOrders chosen
  let mut bad : List Name := []
  for c in bstSpec.ctors do
    let some plan := book.find? bstKey c.ctorName | bad := bad ++ [c.ctorName]; continue
    match repair bstSpec bstKey c plan, compiled.find? (fun p => p.1 == c.ctorName) with
    | .ok (_, interp), some (_, comp) =>
      unless normSteps interp.1 == normSteps comp.1 do bad := bad ++ [c.ctorName]
    | _, _ => bad := bad ++ [c.ctorName]
  unless bad.isEmpty do
    throwError "settled orders that do not lower to the compiled schedule: {bad}"
  IO.println s!"[pinned-order] deriver's settled orders reproduce all {chosen.length} compiled schedules"

end SpecimenTest.PinnedOrder
