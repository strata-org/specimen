import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import Specimen.MExp
import Specimen.Schedules
import Specimen.DeriveSchedules
import Specimen.Debug
import Specimen.Utils
import Specimen.TheoremChecker
import Specimen.LazyList
import Specimen.Tactic.Schedule
import Specimen.Tactic.TestLoop
import Specimen.Tactic.Shrink
import Specimen.Tactic.Widget

import Plausible.Tactic
import Plausible.DeriveShrinkable

import Lean.Elab.Tactic
import Lean.Elab.Command

open Lean Elab Tactic Meta Term Command
open Idents Schedules Plausible Plausible.Decorations MExp

/-! # Property testing for theorem statements

Analogous to QuickChick's `quickchick`. Given a proposition of the form
`∀ x₁ … xₙ, H₁ → … → Hₘ → C`, the statement is treated as a virtual constructor whose
variables are all outputs: the hypotheses become a schedule that generates witnesses
satisfying them, and `C` is checked against each. Transitive dependencies are derived
through the same schedule search as `derive_mutual`.

Two entry points, both accepting an optional size configuration in any order:

```lean
specimen_test (min := 1, max := 8, tests := 200) (∀ n, P n → Q n)   -- command
example : ∀ n, P n → Q n := by specimen                             -- tactic
```

The tactic tests the current goal and leaves it open; a counterexample is reported as an
error naming each variable and its value. Generation size ramps linearly from `min` to
`max` across the run, so the defaults `min := 1`, `max := 100`, `tests := 100` try each
size once.

Shrinking is controlled by `specimen.shrink`, `specimen.shrinkBreadth` and
`specimen.shrinkDepth`; see `Specimen/Debug.lean`.
-/

namespace Specimen.Tactic


syntax minField := &"min" " := " num
syntax maxField := &"max" " := " num
syntax testsField := &"tests" " := " num
syntax configField := minField <|> maxField <|> testsField
syntax sizeConfig := atomic("(" configField) ("," configField)* ")"

/-- Property-based testing for a proposition over inductive relations. The `min`, `max` and
    `tests` fields are each optional and may appear in any order, e.g.
    `specimen_test (min := 5, max := 200, tests := 500) (prop)`. -/
syntax (name := specimenTestCmd) "specimen_test " (sizeConfig)? term : command

/-- Recursively search a syntax tree for a node of the given kind, returning its num arg. -/
private partial def findFieldNum (stx : Syntax) (kind : Name) : Option Nat :=
  if stx.getKind == kind then
    -- Field is `&"<name>" " := " num`, so num is the last arg
    stx.getArgs.back?.bind (·.isNatLit?)
  else
    stx.getArgs.foldl (fun acc arg => acc <|> findFieldNum arg kind) none

/-- Extract the numeric value of a `min`/`max`/`tests` field from a `sizeConfig` node. -/
private def extractSizeField (cfg : Syntax) (fieldName : String) : Option Nat :=
  let kind := match fieldName with
    | "min" => `Specimen.Tactic.minField
    | "max" => `Specimen.Tactic.maxField
    | _ => `Specimen.Tactic.testsField
  findFieldNum cfg kind

@[command_elab specimenTestCmd]
unsafe def elabSpecimenTest : CommandElab := fun stx => do
  match stx with
  | `(specimen_test $[$cfg:sizeConfig]? $prop:term) => do
    let minSize : Nat := match cfg with
      | some c => (extractSizeField c.raw "min").getD 1
      | none => 1
    let maxSize : Nat := match cfg with
      | some c => (extractSizeField c.raw "max").getD 100
      | none => 100
    let numTests : Nat := match cfg with
      | some c => (extractSizeField c.raw "tests").getD 100
      | none => 100
    let memo ← IO.mkRef ({} : Std.HashMap SpecKey MemoEntry)

    -- Elaborate the proposition and compute its schedule
    let scheduleStartTime ← IO.monoNanosNow
    let scheduleResult ← withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
      liftTermElabM do
        let e ← elabTerm prop (some (mkSort .zero))
        let tgt ← instantiateMVars e
        let termElabCtx ← readThe Lean.Elab.Term.Context
        let deriveDep : SpecKey → MetaM Unit := fun depKey => do
          let _ ← (deriveBestInductiveSchedule depKey memo).run termElabCtx
        getTheoremSchedule tgt (memoRef := some memo) (deriveDep := deriveDep)
    let scheduleEndTime ← IO.monoNanosNow
    let scheduleTimeUs := (scheduleEndTime - scheduleStartTime) / 1000

    match scheduleResult with
    | none => throwError "specimen: unable to compute a testing schedule for this proposition.\n\
        It must be of the form `∀ x₁ ... xₙ, H₁ → ... → Hₘ → C` where\n\
        the hypotheses and conclusion involve inductive relations."
    | some (steps, sort, varNamesTypes, schedulesConsidered, theoremScore) =>
      -- Ensure the conclusion's relation has a DecOpt instance derived
      match sort with
      | .TheoremSchedule (conclusionName, _) true =>
        withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
          liftTermElabM do
            let conclusionKey : SpecKey := { inductiveName := conclusionName, outputIndices := [], deriveSort := .Checker }
            let termElabCtx ← readThe Lean.Elab.Term.Context
            let _ ← (deriveBestInductiveSchedule conclusionKey memo).run termElabCtx
      | _ => pure ()

      -- Derive DecOpt checkers for all hypothesis relations (needed by validShrinks/shrinkDiag)
      for step in steps do
        match step with
        | .SuchThat _ (.NonRec (hypName, _)) _ =>
          withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
            liftTermElabM do
              let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
              let termElabCtx ← readThe Lean.Elab.Term.Context
              let _ ← (deriveBestInductiveSchedule hypCheckerKey memo).run termElabCtx
        | .Check (.NonRec (hypName, _)) _ =>
          withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
            liftTermElabM do
              let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
              let termElabCtx ← readThe Lean.Elab.Term.Context
              let _ ← (deriveBestInductiveSchedule hypCheckerKey memo).run termElabCtx
        | _ => pure ()

      let finalMemo ← memo.get
      let directDeps : Array ScheduleDep := (collectNonRecDeps steps).toArray
      let mut usedKeys : Std.HashSet SpecKey := {}
      -- Include the conclusion checker in the used keys
      match sort with
      | .TheoremSchedule (conclusionName, _) true =>
        let conclusionKey : SpecKey := { inductiveName := conclusionName, outputIndices := [], deriveSort := .Checker }
        usedKeys := collectUsedDeps conclusionKey finalMemo usedKeys
      | _ => pure ()
      -- Include hypothesis checkers (for validShrinks)
      for step in steps do
        match step with
        | .SuchThat _ (.NonRec (hypName, _)) _ =>
          let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
          usedKeys := collectUsedDeps hypCheckerKey finalMemo usedKeys
        | .Check (.NonRec (hypName, _)) _ =>
          let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
          usedKeys := collectUsedDeps hypCheckerKey finalMemo usedKeys
        | _ => pure ()
      for dep in directDeps do
        if dep.kind == DepKind.relation || dep.kind == DepKind.checker then
          let depKey : SpecKey := { inductiveName := dep.inductiveName, outputIndices := dep.outputIndices, deriveSort := dep.deriveSort }
          usedKeys := collectUsedDeps depKey finalMemo usedKeys

      -- Compile & emit all dependency instances using the SAME machinery as derive_mutual
      -- (so mutually-recursive components — e.g. the two modes of `typing` — go into a
      -- single `mutual … end` block with a consistent sibling-name mapping).
      let components := computeSpecSCC usedKeys.toList finalMemo
      let debugLog := Lean.Option.get (← getOptions) specimen.debug
      if debugLog then
        logInfo m!"specimen: {components.length} SCC components, {usedKeys.size} used keys"
        for comp in components do
          let compDesc := comp.map (fun k =>
            m!"{k.inductiveName} outputs={k.outputIndices} sort={repr k.deriveSort}")
          logInfo m!"  component: {compDesc}"
      let constraintMap ← liftTermElabM <| propagateConstraints components finalMemo
      let (compiledComponents, compiledCodeMap) ←
        compileSpecComponents components finalMemo constraintMap
      emitSpecComponents compiledComponents .global

      -- Compile the theorem schedule into a checker def (before widget so we can show the code)
      let defName ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_theorem_checker)
      let varNames := varNamesTypes.map Prod.fst
      let varTypes := varNamesTypes.map Prod.snd
      let defCmd ← withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
        liftTermElabM <| compileTheoremDef steps sort (mkSort .zero) defName varNames varTypes
      let theoremCodeStr ← liftTermElabM <| try
        let fmt ← Lean.PrettyPrinter.ppCommand defCmd
        pure fmt.pretty
      catch _ => pure "(failed to pretty-print)"
      if debugLog then
        logInfo m!"── emitting theorem checker {defName}:\n{theoremCodeStr}"
      elabCommand defCmd

      -- Compile the validShrinks function
      let shrinkBreadth := Lean.Option.get (← getOptions) specimen.shrinkBreadth
      let shrinksName ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_valid_shrinks)
      let shrinksCmd ← liftTermElabM <| compileValidShrinksDef steps sort shrinksName varNames varTypes shrinkBreadth
      elabCommand shrinksCmd

      -- Compile the shrink diagnostic function (for HTML trace)
      let shrinkDiagName ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_shrink_diag)
      let shrinkDiagCmd ← liftTermElabM <| compileShrinkDiagDef steps sort shrinkDiagName varNames varTypes shrinkBreadth
      elabCommand shrinkDiagCmd

      -- Build rich HTML widget (emitted after test result for better infoview order)
      let richOutput := Lean.Option.get (← getOptions) specimen.richOutput
      let widgetMsg ← if richOutput then
        some <$> liftTermElabM
          (theoremWidgetHtml steps sort theoremScore scheduleTimeUs schedulesConsidered
            theoremCodeStr finalMemo usedKeys components compiledCodeMap)
      else pure none

      -- Run the test loop
      let checkerIdent : TSyntax `term := mkIdent defName
      let shrinksIdent : TSyntax `term := mkIdent shrinksName
      let diagIdent : TSyntax `term := mkIdent shrinkDiagName

      let testExpr ← buildTestExpr varNames varTypes checkerIdent shrinksIdent diagIdent
        minSize maxSize numTests richOutput

      let e ← liftTermElabM <| Term.elabTerm testExpr none
      let expectedType ← liftTermElabM <| inferType e
      let action ← liftTermElabM <| unsafe Lean.Meta.evalExpr
        (IO (String × Nat × List (String × List (String × String × String)))) expectedType e
      let (resultMsg, _shrinkCount, shrinkTree) ← action

      -- Emit the test result first (appears at top of infoview)
      if resultMsg.startsWith "Found counter-example!" then
        logError resultMsg
      else
        logInfo resultMsg

      -- Build shrink tree HTML widget if there was shrinking
      if !shrinkTree.isEmpty then
        let shrinkHtml ← liftTermElabM (shrinkTreeHtml shrinkTree)
        logInfo shrinkHtml

      -- Emit the main widget after test result
      if let some msg := widgetMsg then
        logInfo msg

  | _ => throwUnsupportedSyntax

/-- Run a `CommandElabM` action from within `CoreM`, building a command context/state
    from the current core context/state and syncing the environment, name generators,
    messages, traces, and info trees back afterward.

    This is the inverse of `Lean.Elab.Command.runCore` (which runs `CoreM` inside
    `CommandElabM`). It lets the `specimen` tactic reuse the `specimen_test` command
    logic (which emits derived instances via `elabCommand`). -/
def runCommandElabMInCore (x : CommandElabM α) : CoreM α := do
  let coreCtx ← readThe Core.Context
  let coreState ← getThe Core.State
  let opts ← getOptions
  let cmdCtx : Lean.Elab.Command.Context := {
    fileName       := coreCtx.fileName
    fileMap        := coreCtx.fileMap
    currRecDepth   := coreCtx.currRecDepth
    currMacroScope := coreCtx.currMacroScope
    ref            := coreCtx.ref
    snap?          := none
    cancelTk?      := coreCtx.cancelTk?
  }
  -- Preserve the current namespace and open declarations so name resolution
  -- inside the emitted commands matches the tactic's context.
  let scope : Lean.Elab.Command.Scope := {
    header       := ""
    opts         := opts
    currNamespace := coreCtx.currNamespace
    openDecls    := coreCtx.openDecls
  }
  let cmdState : Lean.Elab.Command.State := {
    env            := coreState.env
    messages       := coreState.messages
    scopes         := [scope]
    nextMacroScope := coreState.nextMacroScope
    maxRecDepth    := coreCtx.maxRecDepth
    ngen           := coreState.ngen
    auxDeclNGen    := coreState.auxDeclNGen
    infoState      := coreState.infoState
    traceState     := coreState.traceState
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run cmdState) with
  | .error e => throw e
  | .ok (a, sNew) =>
    modifyThe Core.State fun s => { s with
      env            := sNew.env
      messages       := sNew.messages
      nextMacroScope := sNew.nextMacroScope
      ngen           := sNew.ngen
      auxDeclNGen    := sNew.auxDeclNGen
      infoState      := sNew.infoState
      traceState     := sNew.traceState
    }
    return a

/-- Property-based testing of the current proof goal.

    Closes the goal over its local hypotheses with `mkForallFVars`, leaving the proof state
    untouched, then tests the result as `specimen_test` does. Derived generators and checkers
    live in the environment only for the duration of the test.

    This is a diagnostic: it reports whether a counterexample was found and neither alters
    the goal nor claims to prove it. Accepts the same size configuration as `specimen_test`,
    e.g. `specimen (min := 5, max := 200)`. -/
syntax (name := specimenTac) "specimen" (sizeConfig)? : tactic

@[tactic specimenTac]
unsafe def evalSpecimenTac : Tactic := fun stx => do
  match stx with
  | `(tactic| specimen $[$cfg:sizeConfig]?) => withMainContext do
    -- Build the closed ∀-proposition from the goal + local hypotheses WITHOUT
    -- mutating the proof state (no revert): abstract the local fvars over the target.
    let tgt ← getMainTarget
    let fvars := (← getLocalHyps)
    let closedProp ← instantiateMVars (← mkForallFVars fvars tgt)
    -- Delaborate the closed proposition into a term syntax
    let tgtStx ← PrettyPrinter.delab closedProp
    -- Build the `specimen_test` command syntax (forwarding any size config)
    let cmdStx ← match cfg with
      | some c => `(command| specimen_test $c:sizeConfig $tgtStx:term)
      | none => `(command| specimen_test $tgtStx:term)
    -- Inside a proof the enclosing declaration elaborates on an async branch that limits
    -- `addDecl` to that declaration's name prefix (`Environment.AsyncContext.mayContain`),
    -- while derived instances are named after their types. Unlocking is safe because the
    -- defs are transient: the goal stays open and `savedEnv` is restored below.
    let savedEnv ← getEnv
    try
      modifyEnv (·.unlockAsync)
      runCommandElabMInCore (Lean.Elab.Command.elabCommand cmdStx)
      setEnv savedEnv
    catch e =>
      setEnv savedEnv
      throw e
  | _ => throwUnsupportedSyntax

end Specimen.Tactic
