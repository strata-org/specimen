import Lean.Expr
import Lean.LocalContext

import Specimen.UnificationMonad
import Specimen.Schedules
import Specimen.DeriveSchedules
import Specimen.MExp
import Specimen.MakeConstrainedProducerInstance
import Plausible.DeriveArbitrary
import Specimen.TSyntaxCombinators
import Specimen.PatternCoverage
import Specimen.Utils
import Specimen.Debug
import Plausible.Arbitrary

import Lean.Elab.Command
import ProofWidgets.Component.HtmlDisplay

import Lean.Meta.Basic

open Lean Elab Command Meta Term Parser
open Idents Schedules ProofWidgets


----------------------------------------------------------------------------------------------------------------------------------
-- Adapted from "Generating Good Generators for Inductive Relations" (POPL '18) & "Testing Theorems, Fully Automatically" (2025)
-- as well as the QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newUnifyQC.ml.cppo
----------------------------------------------------------------------------------------------------------------------------------

/-- Creates the initial constraint map where all inputs are `Fixed`, while the outputs & all universally-quantified variables are `Undef`.
    - `forAllVariables` is a list of (variable name, variable type) pairs -/
def mkInitialUnknownMap (inputNames: List Name)
  (outputNamesTypes : List (Name × Expr))
  (forAllVariables : List (Name × Expr)) : UnknownMap :=
  let inputConstraints := inputNames.map (fun n => (n, .Fixed))
  let outputConstraints := outputNamesTypes.map (fun (n, ty) => (n, .Undef ty))
  let filteredForAllVariables := forAllVariables.filter (fun (x, _) => x ∉ inputNames)
  let forAllVarsConstraints := (fun (x, ty) => (x, .Undef ty)) <$> filteredForAllVariables
  Std.HashMap.ofList $ inputConstraints ++ outputConstraints ++ forAllVarsConstraints

/-- Creates the initial `UnifyState` for a producer, with the `UnifyState` corresponding to a constructor of an inductive relation.
    The arguments to this function are:
    - `inputNames`: the names of all inputs to the producer
    - `outputNamesTypes`: names & types of the outputs (variables to be produced)
    - `forAllVariables`: the names & types for universally-quantified variables in the constructor's type
    - `hypotheses`: the hypotheses for the constructor (represented as a constructor name applied to some list of arguments) -/
def mkProducerInitialUnifyState (inputNames : List Name)
  (outputNamesTypes : List (Name × Expr))
  (forAllVariables : List (Name × Expr))
  (hypotheses : List (Name × List ConstructorExpr)) : UnifyState :=
  let outputNames := outputNamesTypes.map Prod.fst
  let outputTypes := outputNamesTypes.map Prod.snd
  let forAllVarNames := Prod.fst <$> forAllVariables
  let constraints := mkInitialUnknownMap inputNames outputNamesTypes forAllVariables
  let unknowns := Std.HashSet.ofList (outputNames ++ inputNames ++ forAllVarNames)
  { constraints := constraints
    equalities := ∅
    patterns := []
    unknowns := unknowns
    outputNames := outputNames
    outputTypes := outputTypes
    inputNames := inputNames
    hypotheses := hypotheses }

/-- Creates the initial `UnifyState` for a checker, with the `UnifyState` corresponding to a constructor of an inductive relation.
    The arguments to this function are:
    - `inputNames`: the names of all inputs to the producer
    - `forAllVariables`: the names & types for universally-quantified variables in the constructor's type
    - `hypotheses`: the hypotheses for the constructor (represented as a constructor name applied to some list of arguments)

    Note that this function is the same as `mkProducerInitialUnifyState`, except it doesn't take in the name & type of the output variable,
    since checkers don't need to produce values (they just need to return an `Option Bool`). -/
def mkCheckerInitialUnifyState (inputNames : List Name)
  (forAllVariables : List (Name × Expr))
  (hypotheses : List (Name × List ConstructorExpr)) : UnifyState :=
  let forAllVarNames := Prod.fst <$> forAllVariables
  let inputConstraints := inputNames.zip (List.replicate inputNames.length .Fixed)
  let filteredForAllVariables := forAllVariables.filter (fun (x, _) => x ∉ inputNames)
  let forAllVarsConstraints := (fun (x, ty) => (x, .Undef ty)) <$> filteredForAllVariables
  let constraints := Std.HashMap.ofList $ inputConstraints ++ forAllVarsConstraints
  let unknowns := Std.HashSet.ofList (inputNames ++ forAllVarNames)
  { emptyUnifyState with
    constraints := constraints
    unknowns := unknowns
    inputNames := inputNames
    hypotheses := hypotheses
  }

/-- Converts a expression `e` to a *constructor expression* `C r1 … rn`,
    where `C` is a constructor and the `ri` are arguments,
    returning `some (C, #[r1, …, rn])`
    - If `e` is not an application, this function returns `none`  -/
def convertToCtorExpr (e : Expr) : MetaM (Option (Name × Array Expr)) :=
  if e.isConst then
    -- Nullary constructors are identified by name
    return some (e.constName!, #[])
  else if e.isApp then do
    -- Constructors with arguments
    let (ctorName, args) := e.getAppFnArgs
    let mut actualArgs := #[]
    for arg in args do
      -- Figure out whether `argType` is `Type u` for some universe `u`
      let argType ← inferType arg
      -- If `argType` is `Type u` or `Sort u`, then we know `arg` itself must be a type
      -- (i.e. it is part of an explicit type application), so we can omit it from `actualArgs`
      if argType.isSort then
        continue
      else if argType.isApp then
        -- Handle case where `argType` is a typeclass instance
        -- (e.g. `LT Nat` is supplied as an argument to `<`)
        -- Typeclass instance arguments which are explicit type applications
        -- can be omitted from `actualArgs`
        let (typeCtorName, _) := argType.getAppFnArgs
        let env ← getEnv
        if Lean.isClass env typeCtorName then
          continue
        else
          actualArgs := actualArgs.push arg
      else
        actualArgs := actualArgs.push arg
    return some (ctorName, actualArgs)
  else
    return none


/-- Takes an unknown `u`, and finds the `Range` `r` that corresponds to
    `u` in the `constraints` map.

    However, there are 3 conditions in which we generate a fresh unknown `u'`
    and update the `constraints` map with the binding `u' ↦ Unknown u`:

    1. `u` isn't present in the `constraints` map (i.e. no such `r` exists)
    2. `r = .Fixed`
    3. `r = .Undef τ` for some type τ
    (We need to hand latter two conditions are )

    We need to handle conditions (2) and (3) because the top-level ranges
    passed to `UnifyM.unify` cannot be `Fixed` or `Undef`, as stipulated
    in the QuickChick codebase / the Generating Good Generators paper. -/
def processCorrespondingRange (u : Unknown) : UnifyM Range :=
  UnifyM.withConstraints $ fun k =>
    match k[u]? with
    | some .Fixed | some (.Undef _) | none => do
      let u' ← UnifyM.registerFreshUnknown
      UnifyM.update u' (.Unknown u)
      return .Unknown u'
    | some r => return r

/-- Converts an `Expr` to a `Range`, using the `LocalContext` to find the user-facing names
    corresponding to `FVarId`s -/
partial def convertExprToRangeInCurrentContext (e : Expr) : UnifyM Range := do
  match (← convertToCtorExpr e) with
  | some (f, args) => do
    let argRanges ← args.toList.mapM convertExprToRangeInCurrentContext
    return (Range.Ctor f argRanges)
  | none =>
    if e.isFVar then do
      let localCtx ← getLCtx
      match localCtx.findFVar? e with
      | some localDecl =>
        let u := localDecl.userName
        return (.Unknown u)
      | none =>
        let namesInContext := (fun e => getUserNameInContext! localCtx e.fvarId!) <$> localCtx.getFVars
        throwError m!"{e} missing from LocalContext, which only contains {namesInContext}"
    else
      match e with
      | .const u _ => return (.Unknown u)
      | .lit literal => return .Lit literal
      | _ => throwError m!"Cannot convert expression {e} to Range"

/-- Converts a hypothesis (reprented as a `TSyntax term`) to a `Range` -/
partial def convertHypothesisTermToRange (term : TSyntax `term) : UnifyM Range := do
  match term with
  | `($ctor:ident $args:term*) => do
    let argRanges ← Array.toList <$> args.mapM convertHypothesisTermToRange
    return (.Ctor ctor.getId argRanges)
  | `($ctor:ident) =>
    -- Use `getConstInfo` to determine if the identifier is a variable name or
    -- a nullary constructor of an inductive type
    let name := ctor.getId
    let constInfo ← getConstInfo name
    if constInfo.isCtor then
      return (Range.Ctor name [])
    else if constInfo.isDefinition then
      throwError m!"Cannot convert definition {term} to a Range"
    else /- TODO: Does this case need to exist? -/
      return (.Unknown name)
  | _ => throwError m!"unable to convert {term} to a Range"

/-- Converts a `Pattern` to a `TSyntax term` -/
partial def convertPatternToTerm (pattern : Pattern) : MetaM (TSyntax `term) :=
  match pattern with
  | .UnknownPattern name => return (mkIdent name)
  | .CtorPattern ctorName args => do
    let ctorIdent := mkIdent ctorName
    let argSyntaxes ← args.mapM convertPatternToTerm
    argSyntaxes.foldlM (fun acc arg => `($acc $arg)) ctorIdent
  | .LitPattern l => mkLiteral l


/-- Converts a `Range` to a `ConstructorExpr`
    (helper function used by `convertRangeToCtorAppForm`) -/
partial def convertRangeToConstructorExpr (r : Range) : UnifyM ConstructorExpr :=
  match r with
  | .Unknown u => return (.Unknown u)
  | .Ctor ctorName args => do
    let updatedArgs ← args.mapM convertRangeToConstructorExpr
    return (.Ctor ctorName updatedArgs)
  | .Lit l =>
    return .Lit l
  | _ => throwError m!"Unable to convert {r} to a constructor expression"

/-- Converts a `Range` that is either an `Unknown` or `Ctor` to
    a term in *constructor application form*, represented as a pair of type `(Name × List ConstructorExpr)`
    (constructor name applied to zero or more arguments which may themselves be `ConstructorExpr`s) -/
def convertRangeToCtorAppForm (r : Range) : UnifyM (Name × List ConstructorExpr) :=
  match r with
  | Range.Unknown u => return (u, [])
  | Range.Ctor c rs => do
    let args ← rs.mapM convertRangeToConstructorExpr
    return (c, args)
  | _ => throwError m!"Unable to convert {r} to a constructor expression"

/-- Given a `conclusion` to a constructor, a list of `outputVars` and a `deriveSort`,
    figures out the appropriate `ScheduleSort`.

    - The `returnOption` boolean argument is used to determine
      whether producers should return their results wrapped in an `Option` or not.

    - The `ctorNameOpt` argument is an (optional) constructor name for the produced value
      + This is `none` for checkers/theorem schedules as they don't produce constructor applications like generators/enumerators.
    - Note: callers should supply `none` as the `ctorNameOpt` argument if `deriveSort := .Theorem`  or `.Checker` -/
def getScheduleSort (conclusion : HypothesisExpr)
  (outputVars : List Unknown)
  (ctorNameOpt : Option Name)
  (deriveSort : DeriveSort) (returnOption : Bool) : UnifyM ScheduleSort :=
  match deriveSort with
  | .Checker => return .CheckerSchedule
  | .Theorem => return (.TheoremSchedule conclusion (typeClassUsed := true))
  | _ => do
    let outputValues ← outputVars.mapM UnifyM.evaluateUnknown
    let producerSort := convertDeriveSortToProducerSort deriveSort
    let conclusion ← do
      if returnOption then
        pure outputValues
      else
        let ctorName ← Option.getDM ctorNameOpt
          (throwError "No constructor name given for Non-theorem schedule")
        pure [ConstructorExpr.Ctor ctorName outputValues]
    return .ProducerSchedule producerSort conclusion


/-- `rewriteFunctionCallsInConclusion hypotheses conclusion inductiveRelationName` does the following:
    1. Checks if the `conclusion` contains a function call where the function is *not* the same as the `inductiveRelationName`.
       (If no, we just return the pair `(hypotheses, conclusion)` as is.)
    2. If yes, we create a fresh variable & add an extra hypothesis where the fresh var is bound to the result of the function call.
    3. Additionally, checks for nonlinear variable occurrences (variables appearing multiple times) and creates fresh variables
       for all but the first occurrence, adding equality hypotheses between the fresh and original variables.
    4. We add the fresh variables to the `unknowns` set and the `constraints` map in `UnifyState`, where they map to `Undef` ranges.
    5. We then rewrite the conclusion, replacing occurrences of function calls and duplicate variables with fresh variables.
    The updated hypotheses, conclusion, a list of the names & types of the fresh variables produced, and new `LocalContext` are subsequently returned.
    - Note: it is the caller's responsibility to check that `conclusion` does indeed contain
      a non-trivial function application (e.g. by using `containsNonTrivialFuncApp`) -/
def linearizeAndFlatten
  (hypotheses : Array Expr) (conclusion : Expr) (outputIndices : List Nat) (localCtx : LocalContext) :
  UnifyM (Array Expr × Expr × List (Name × Expr) × LocalContext) := do
  -- Phase 1: flatten function calls into fresh unknowns with equality hypotheses
  let funcAppExprs ← collectUnmatchableProperSubterms conclusion
  trace[plausible.deriving.arbitrary] m!"Unmatchable exprs: {funcAppExprs} In conclusion: {conclusion}"
  withLCtx' localCtx do

  let mut freshUnknownsAndTypes := #[]

  -- Handle function calls
  for i in List.range funcAppExprs.length do
    let funcAppExpr := funcAppExprs[i]!
    let funcAppType ← inferType funcAppExpr
    let freshUnknown := localCtx.getUnusedName <| (`unk).appendAfter s!"_{i}"

    UnifyM.insertUnknown freshUnknown
    UnifyM.update freshUnknown (.Undef funcAppType)
    freshUnknownsAndTypes := freshUnknownsAndTypes.push (freshUnknown, funcAppType)

  withLocalDeclsDND freshUnknownsAndTypes (fun freshVarExprs => do
    -- Association list mapping each function call to the corresponding fresh variable
    let funcCallEqualities := List.zip funcAppExprs freshVarExprs.toList

    let mut additionalHyps := #[]

    -- Add hypotheses for function calls
    for (funcAppExpr, newVarExpr) in funcCallEqualities do
      let newHyp ← mkEq newVarExpr funcAppExpr
      additionalHyps := additionalHyps.push newHyp

    trace[plausible.deriving.arbitrary] m!"Original Conclusion: {conclusion}"
    let conclusion := replaceExprsRecursivelyOnce conclusion funcCallEqualities []
    trace[plausible.deriving.arbitrary] m!"Rewritten Conclusion after flattening: {conclusion}"

    let functionsNewTypedVars := freshUnknownsAndTypes
    let functionsNewHyps := additionalHyps

    -- Phase 2: linearize repeated variables — each extra occurrence gets a fresh unknown + equality
    let varOccurrences := collectFVarOccurrences conclusion outputIndices

    trace[plausible.deriving.arbitrary] m!"varOccurences: {repr varOccurrences.toList} \n expr: {conclusion} \n outputIndices {outputIndices}"

    let nonlinearVars := varOccurrences.toList.filter (fun (_, count) => count > 1)

    -- Handle nonlinear variables
    let mut nonlinearReplacements := []

    let mut freshUnknownsAndTypes := #[]
    for (fvarId, count) in nonlinearVars do
      let originalVar := mkFVar fvarId
      let varType ← inferType originalVar
      if varType.isSort then continue
      let varName ← fvarId.getUserName

      -- Create count-1 fresh variables (keeping first occurrence as original)
      for i in List.range (count - 1) do
        let freshName := varName.appendAfter s!"_{i + 1}"
        let freshUnknown := localCtx.getUnusedName freshName
        UnifyM.insertUnknown freshUnknown
        UnifyM.update freshUnknown (.Undef varType)
        freshUnknownsAndTypes := freshUnknownsAndTypes.push (freshUnknown, varType)
        nonlinearReplacements := (originalVar, freshUnknown) :: nonlinearReplacements

     -- We use `withLocalDecl` to add all the fresh variables produced to the local context
    withLocalDeclsDND freshUnknownsAndTypes (fun freshVarExprs => do
      -- Map nonlinear variable replacements to fresh variables
    let nonlinearVarEqualities := List.zip (nonlinearReplacements.reverse.map (·.1)) (freshVarExprs.toList)
    let mut additionalHyps := #[]
    -- Add hypotheses for nonlinear variables
    for (originalVar, freshVar) in nonlinearVarEqualities do
      let newHyp ← mkEq freshVar originalVar
      additionalHyps := additionalHyps.push newHyp

    let updatedHypotheses := hypotheses ++ additionalHyps ++ functionsNewHyps

    trace[plausible.deriving.arbitrary] m!"Flattened Conclusion: {conclusion}"
    let rewrittenConclusion := replaceExprsRecursivelyOnce conclusion nonlinearVarEqualities outputIndices
    trace[plausible.deriving.arbitrary] m!"Rewritten Conclusion after linearizing: {rewrittenConclusion}"


    -- Insert the fresh variable into the bound-variable context
    return (updatedHypotheses, rewrittenConclusion, freshUnknownsAndTypes.toList ++ functionsNewTypedVars.toList, ← getLCtx)

    )
  )


/-- Unifies each argument in the conclusion of an inductive relation with the top-level arguments to the relation
    (using the unification algorithm from Generating Good Generations),
    and subsequently computes a *naive* schedule for a generator/enumerator/checker (indicated by the `deriveSort`).

    Note: this function processes the entire type of the constructor within the same `LocalContext`
    (the one produced by `forallTelescopeReducing`).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The sort of function we are deriving (`deriveSort`) (either a generator, enumerator or a checker)
    - The names of inputs `inputNames` (arguments to the derived function)
    - An option `outputNameTypeOption` containing the name & type of the output (value to be produced)
      + This option should be `some` pair if `deriveSort = .Generator` or `.Enumerator`, and none otherwise
    - An array of unknowns (`unknownsArray`), which are provided to the unification algorithm
      + This array should be non-empty if `deriveSort = .Generator` or `.Enumerator`, and empty otherwise
      + Note: when `deriveSort == .Generator / .Enumerator`, it is the caller's responsibility to ensure that
        `unknowns == inputNames ∪ outputNames`, i.e. `unknowns` contains all args to the inductive relation
        listed in order, which coincides with `inputNames ∪ outputNames` -/
structure ScheduleResult where
  schedule : Schedule
  schedulesConsidered : Nat
  score : Score
  deriving Repr

def getScheduleForInductiveRelationConstructor
  (inductiveName : Name) (ctorName : Name) (inputNames : List Name)
  (deriveSort : DeriveSort) (outputNameTypeOption : Option (List (Name × Expr × Nat))) (unknownsArray : Array Unknown) (localCtx : LocalContext) (recFnName : Name := defaultRecFnName deriveSort)
  (depMemo : Std.HashMap SpecKey MemoEntry := {}) : UnifyM ScheduleResult := do
  trace[plausible.deriving.arbitrary] "Schedule requested for inductive {inductiveName}'s constructor, {ctorName} with inputs: {inputNames} and variables: {unknownsArray}"

  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  withLCtx' localCtx do

  -- Stay within the forallTelescope scope for all processing
  forallTelescopeReducing ctorType (cleanupAnnotations := true) (fun forAllVarsAndHyps conclusion => do
    -- Collect all the universally-quantified variables + hypotheses
    -- Universally-quantified variables `x : τ` are represented using `(some x, τ)`
    -- Hypotheses are represented using `(none, hyp)` (first component is `none` since a hypothesis doesn't have a name)
    let forAllVarsAndHypsWithTypes ← forAllVarsAndHyps.mapM (fun fvar => do
      let localCtx ← getLCtx
      let localDecl := localCtx.get! fvar.fvarId!
      let userName := localDecl.userName
      if not userName.hasMacroScopes || localDecl.binderInfo == .instImplicit then
        return (some userName, localDecl.type)
      else
        return (none, localDecl.type))

    -- Extract the universally quantified variables
    let forAllVars := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, ty) =>
      match nameOpt with
      | some name => some (name, ty)
      | none => none) |>.toList

    -- Extract hypotheses (which correspond to pairs in `forAllVarsAndHypsWithTypes` where the first component is `none`)
    let hypotheses := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, tyExpr) =>
      match nameOpt with
      | none => some tyExpr
      | some _ => none)

    let outputIndices := match outputNameTypeOption with
      | some outputs => outputs.map (fun (_, _, idx) => idx)
      | none => []

    -- For each function call in the cocnlusion, rewrite it by introducing a fresh variable
    -- equal to the result of the function call, and adding an extra hypothesis asserting equality
    -- between the function call and the variable.
    -- `freshNamesAndTypes` is a list containing the names & types of the fresh variables produced during this procedure.
    let (updatedHypotheses, updatedConclusion, freshNamesAndTypes, updatedLocalCtx) ←
      linearizeAndFlatten hypotheses conclusion outputIndices (← getLCtx)
    -- Enter the updated `LocalContext` containing the fresh variable that was created when rewriting the conclusion
    withLCtx' updatedLocalCtx (do
      let hypothesisExprs := (← monadLift (updatedHypotheses.toList.mapM (exprToHypothesisExpr ctorName))).toArray

      trace[plausible.deriving.arbitrary] m!"Hypotheses to be ordered as HypothesisExprs: {updatedHypotheses}"

      -- Creates the initial `UnifyState` needed for the unification algorithm
      let initialUnifyState ←
        match deriveSort with
        | .Generator | .Enumerator =>
           match outputNameTypeOption with
          | none => throwError "Output name & type not specified when deriving producer"
          | some outputs =>
            let outputNamesTypes := outputs.map (fun (n, ty, _) => (n, ty))
            pure $ mkProducerInitialUnifyState inputNames outputNamesTypes forAllVars hypothesisExprs.toList
        | .Checker | .Theorem => pure $ mkCheckerInitialUnifyState inputNames forAllVars hypothesisExprs.toList



      -- Extend the current state with the contents of `initialUnifyState`
      UnifyM.extendState initialUnifyState

      trace[plausible.deriving.arbitrary] m!"Initial Unify State: \n{← get}"

      -- Get the ranges corresponding to each of the unknowns
      -- For producers, we simply use the `unknownsArray` that this function receives as an argument
      -- For checkers, there is no notion of `unknowns` (all arguments to the inductive relation are inputs to the checker),
      -- so we can just use `inputNames`
      let unknowns:=
        if deriveSort.isProducer then
          unknownsArray
        else
          inputNames.toArray
      let unknownRanges ← unknowns.mapM processCorrespondingRange
      let unknownArgsAndRanges := unknowns.zip unknownRanges

      trace[plausible.deriving.arbitrary] m!"Unify State after processing unknown ranges: \n{← get}"

      -- Compute the appropriate `Range` for each argument in the constructor's conclusion
      let conclusionArgs := updatedConclusion.getAppArgs
      let conclusionRanges ← conclusionArgs.mapM convertExprToRangeInCurrentContext
      let conclusionArgsAndRanges := conclusionArgs.zip conclusionRanges

      for ((_, r1), (_, r2)) in conclusionArgsAndRanges.zip unknownArgsAndRanges do
        unify r1 r2
        trace[plausible.deriving.arbitrary] m!"Current Unify State after unifying {r1} and {r2} \n: {← get}"
        assert! (← get).equalities.isEmpty

      -- Convert the conclusion from an `Expr` to a `HypothesisExpr`
      let conclusionExpr ← exprToHypothesisExpr ctorName updatedConclusion

      let ctorNameOpt :=
        match deriveSort with
        | .Generator | .Enumerator => some ctorName
        | .Checker | .Theorem => none

      let (outputVars, recCall) ←
        match deriveSort with
        | .Generator | .Enumerator =>
          match outputNameTypeOption with
          | none => throwError "Error: output name & type not specified when deriving producer"
          | some outputs =>
          let outputNames := outputs.map (fun (n, _, _) => n)
          let outputIdxs := outputNames.map (fun n => unknowns.idxOf n)
          pure (outputNames, (inductiveName, outputIdxs))
        | .Checker | .Theorem => pure ([], (inductiveName, []))

      -- Determine the appropriate `ScheduleSort` (right now we only produce `ScheduleSort`s for `Generator`s)
      let scheduleSort ← getScheduleSort
        conclusionExpr
        (outputVars := outputVars)
        (ctorNameOpt := ctorNameOpt)
        (deriveSort := deriveSort)
        (returnOption := true)

      -- Check which universally-quantified variables have a `Fixed` range,
      -- so that we can supply them to `possibleSchedules` as the `fixedVars` arg

      let updatedForAllVars := forAllVars ++ freshNamesAndTypes
      let fixedVars ← updatedForAllVars.filterMapM (fun (v, _) => do
        if (← UnifyM.isUnknownFixed v) then
          return some v
        else
          return none)

      -- Include any fresh variables produced (when rewriting function calls in conclusions)
      -- in the list of universally-quantified variables
      let updatedForAllVars := List.map (fun (n,ty) => ⟨n,ty⟩) updatedForAllVars
      trace[plausible.deriving.arbitrary] m!"Updated ForAll Vars: {repr updatedForAllVars}"
      trace[plausible.deriving.arbitrary] m!"Fixed Vars: {repr fixedVars}"

      -- Enumerate candidate schedules and select the best by score (checks < length < unconstrained)
      let multiOutput := Lean.Option.get (← getOptions) specimen.multiOutput
      let possibleSchedules := possibleSchedules
        (vars := updatedForAllVars)
        (hypotheses := hypothesisExprs.toList)
        ctorName
        deriveSort
        recCall
        fixedVars
        recFnName
        multiOutput

      match possibleSchedules with
      | .lnil => throwError m!"Unable to compute any possible schedules"
      | .lcons fstSchdM rest =>

      let searchStart ← IO.monoNanosNow
      let (fstSchd, countSeen) ← fstSchdM

      let mut countProcessed  := 1
      let bundle ← Scoring.getActiveScorerBundle
      let scoreSchedule := fun (steps : List ScheduleStep) =>
        let key : SpecKey := { inductiveName := inductiveName, outputIndices := (Prod.snd recCall), deriveSort := deriveSort }
        let stepScores := steps.map fun step => bundle.stepScorer key depMemo step
        bundle.scheduleScorer stepScores
      let mut bestScore := scoreSchedule fstSchd
      let mut bestSchedule   := fstSchd

      trace[plausible.deriving.results] m!"First Schedule: {ppScheduleSteps bestSchedule} \nScore: {bundle.reprScore bestScore}\nSchedules Considered: {repr countSeen}\nSchedules Processed: {repr countProcessed}"
      let limit := 200000
      for schdM in rest.get do
        let (schd, countSeen) ← schdM
        let score := scoreSchedule schd
        countProcessed := countProcessed + 1
        if bundle.isBetter score bestScore then
          bestSchedule := schd
          bestScore := score
          trace[plausible.deriving.results] m!"Better Schedule: {ppScheduleSteps bestSchedule} \nScore: {bundle.reprScore bestScore}\nSchedules Considered: {repr countSeen}\nSchedules Processed: {repr countProcessed}"
        if countProcessed > limit then
          break
      let searchEnd ← IO.monoNanosNow

      trace[plausible.deriving.results] m!"Chosen Schedule: {ppScheduleSteps bestSchedule} \nScore: {bundle.reprScore bestScore}\nSchedules Considered: {repr countSeen}\nSchedules Processed: {repr countProcessed}"
      trace[plausible.deriving.results] m!"  Search time: {(searchEnd - searchStart) / 1000000}ms"

      -- Update the best schedule with the result of unification
      let unifyStart ← IO.monoNanosNow
      let updatedBestSchedule ← updateScheduleSteps bestSchedule
      let unifyEnd ← IO.monoNanosNow
      trace[plausible.deriving.results] m!"  Unify time: {(unifyEnd - unifyStart) / 1000000}ms"
      let finalState ← get

      -- Takes the `patterns` and `equalities` fields from `UnifyState` (created after
      -- the conclusion of a constructor has been unified with the top-level arguments to the inductive relation),
      -- convert them to the appropriate `ScheduleStep`s, and prepends them to the `naiveSchedule`
      let finalSchedule := addConclusionPatternsAndEqualitiesToSchedule finalState.patterns finalState.equalities (updatedBestSchedule, scheduleSort)
      pure { schedule := finalSchedule, schedulesConsidered := countProcessed, score := bestScore })
  )


/-- Unifies each argument in the conclusion of an inductive relation with the top-level arguments to the relation
    (using the unification algorithm from Generating Good Generations),
    and subsequently computes a *naive* generator schedule for a sub-generator corresponding to the constructor
    (using the schedules discussed in Testing Theorems).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The names, types, and indices of the outputs (values to be generated)
    - The names of inputs `inputNames` (arguments to the generator)
    - An array of `unknowns` (the arguments to the inductive relation)
      + Note: `unknowns == inputNames ∪ outputNames`, i.e. `unknowns` contains all args to the inductive relation
        listed in order, which coincides with `inputNames ∪ outputNames` -/
def getProducerScheduleForInductiveConstructor
  (inductiveName : Name) (ctorName : Name) (outputNamesTypesIndices : List (Name × Expr × Nat)) (inputNames : List Name)
  (unknowns : Array Unknown) (deriveSort : DeriveSort) (localCtx : LocalContext) (recFnName : Name := defaultRecFnName deriveSort)
  (depMemo : Std.HashMap SpecKey MemoEntry := {}) : UnifyM ScheduleResult :=
  getScheduleForInductiveRelationConstructor inductiveName ctorName inputNames deriveSort (some outputNamesTypesIndices) unknowns localCtx recFnName depMemo


/-- Produces an instance of a typeclass for a constrained producer (either `ArbitrarySizedSuchThat` or `EnumSizedSuchThat`).
    The arguments to this function are:

    - `outputVars` and `outputTypes` are the names & types of the values to be generated,
    - `constrainingInductive` is the inductive predicate constraining the generated values need to satisfy
    - `constrArgs` are the arguments of the inductive predicate
    - `deriveSort` is the sort of function we are deriving (either `.Generator` or `.Enumerator`) -/
def deriveConstrainedProducer
  (_args : Array Expr)
  (outputVars : Array Expr)
  (outputTypes : Array Expr)
  (constrainingInductive : Name)
  (inductiveLevels : List Level)
  (constrArgs : Array Expr)
  (deriveSort : DeriveSort) : TermElabM (TSyntax `command) := do
  -- Determine what sort of producer we're deriving (a `Generator` or an `Enumerator`)
  let producerSort := convertDeriveSortToProducerSort deriveSort

  let inductiveName := constrainingInductive

  -- Find the indices of the output variables in the inductive application.
  -- Identify which argument positions are outputs (to be generated)
  let outputFVars := outputVars.map Expr.fvarId!
  let mut outputIdxs : Array Nat := #[]
  for i in [:constrArgs.size] do
    let arg := constrArgs[i]!
    if arg.isFVar && outputFVars.contains arg.fvarId! then
      outputIdxs := outputIdxs.push i
  if outputIdxs.isEmpty then
    throwError m!"cannot find output indices, try specifying the implicit arguments"

  -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
  let inductiveVal ← getConstInfoInduct inductiveName

  -- Determine the type for each argument to the inductive
  let inductiveTypeComponents ← getComponentsOfArrowType inductiveVal.type

  -- To obtain the type of each arg to the inductive,
  -- we pop the last element (`Prop`) from `inductiveTypeComponents`
  let argTypes := inductiveTypeComponents.pop

  -- Extract the name of each argument. Output positions may not be fvars
  -- (e.g., when the output type depends on fun-bound variables), so use the
  -- output variable's name there.
  let argNames ← constrArgs.mapIdxM
    (fun i (ident : Expr) =>
      if ident.isFVar then
        ident.fvarId!.getUserName
      else if let some outIdx := outputIdxs.findIdx? (· == i) then
        outputVars[outIdx]!.fvarId!.getUserName
      else throwError m!"{ident} is expected to be a variable.")
  let argNamesTypes := argNames.zip argTypes

  -- The output type for code generation — for multiple outputs, use a right-nested product type
  -- Build the output product type (e.g., α × β for two outputs)
  let outputType ← tupleOfListM (throwError "no output types")
    (fun t rest => do
      let u ← Meta.mkFreshLevelMVar
      let v ← Meta.mkFreshLevelMVar
      pure (Lean.mkApp2 (Lean.mkConst ``Prod [u, v]) t rest)) outputTypes.toList

  -- Add the name & type of each argument of the inductive relation to the `LocalContext`
  -- Then, derive `baseProducers` & `inductiveProducers` (the code for the sub-producers
  -- that are invoked when `size = 0` and `size > 0` respectively),
  -- and obtain freshened versions of the output variables / arguments (`freshenedOutputNames`, `freshArgIdents`)
  let (baseProducers, inductiveProducers, freshenedOutputNames, freshArgIdents, localCtx) ←
  -- Freshen argument names to avoid capture, then derive schedules per constructor
    withLocalDeclsDND argNamesTypes (fun _ => do
      let mut localCtx ← getLCtx
      let mut freshUnknowns := #[]
      -- For each constructor: derive schedule → compile to MExp → emit TSyntax term

      -- For each arg to the inductive relation (as specified to the user),
      -- create a fresh name (to avoid clashing with names that may appear in constructors
      -- of the inductive relation). Note that this requires updating the `LocalContext`.
      for argName in argNames do
        let freshArgName := localCtx.getUnusedName argName
        localCtx := localCtx.renameUserName argName freshArgName
        freshUnknowns := freshUnknowns.push freshArgName

      -- Since the outputs also appear as arguments to the inductive relation,
      -- we also need to freshen their names
      let freshenedOutputNames := outputIdxs.map (fun idx => freshUnknowns[idx]!)

      -- Each argument to the inductive relation (except those at output indices)
      -- is treated as an input
      let freshenedInputNamesExcludingOutput := freshUnknowns.toList.filter
        (fun n => freshenedOutputNames.toList.all (· != n))

      -- Build the list of (outputName, outputType, outputIndex) triples
      let outputNamesTypesIndices : List (Name × Expr × Nat) :=
        (List.range outputIdxs.size).map (fun i =>
          (freshenedOutputNames[i]!, outputTypes[i]!, outputIdxs[i]!))

      let mut nonRecursiveProducers := #[]
      let mut recursiveProducers := #[]

      let freshFuelPrimeName := localCtx.getUnusedName `fuel'
      let freshSizePrimeName := localCtx.getUnusedName `size'
      let freshSize' := mkIdent freshSizePrimeName

      -- Compute the freshened recursive function name early,
      -- so it can be threaded through schedule derivation and MExp compilation.
      -- This must match the name used by `mkConstrainedProducerTypeClassInstance`.
      let freshRecFnName := localCtx.getUnusedName (match deriveSort with
        | .Generator => `aux_arb
        | .Enumerator => `aux_enum
        | _ => `aux_dec)

      let mut requiredInstances := #[]
      for ctorName in inductiveVal.ctors do
        let resultOption ← (UnifyM.runInMetaM
          (getProducerScheduleForInductiveConstructor inductiveName ctorName outputNamesTypesIndices
            freshenedInputNamesExcludingOutput freshUnknowns deriveSort localCtx freshRecFnName)
            emptyUnifyState)
        match resultOption with
        | some result =>
          let schedule := result.schedule
          -- Obtain a sub-producer for this constructor, along with an array of all typeclass instances that need to be defined beforehand.
          -- (Under the hood, we compile the schedule to an `MExp`, then compile the `MExp` to a Lean term containing the code for the sub-producer.
          -- This is all done in a state monad: when we detect that a new instance is required, we append it to an array of `TSyntax term`s
          -- (where each term represents a typeclass instance)
          let (subProducer, instances) ← StateT.run (s := #[]) (do
            let mexp ← MExp.scheduleToMExp schedule (.MId `size) (.MId `initSize) outputType (fuelPrimeName := freshFuelPrimeName) (sizePrimeName := freshSizePrimeName)
            MExp.mexpToTSyntax mexp deriveSort)

          requiredInstances := requiredInstances ++ instances

          -- Determine whether the constructor is recursive
          -- (i.e. if the constructor has a hypothesis that refers to the inductive relation we are targeting)
          let isRecursive ← isConstructorRecursive inductiveName ctorName

          if isRecursive then
            -- Following the QuickChick convention,
            -- recursive sub-generators have a weight of `.succ size'`
            -- and sub-enumerators don't have any weight associated with them
            let subProducerTerm ←
              match producerSort with
              | .Generator => `( ($(mkIdent ``Nat.succ) $freshSize', $subProducer) )
              | .Enumerator => pure subProducer
            recursiveProducers := recursiveProducers.push subProducerTerm
          else
            -- Following the QuickChick convention,
            -- non-recursive sub-generators have a weight of 1
            -- (sub-enumerators don't have any weight associated with them)
            let subGeneratorTerm ←
              match producerSort with
              | .Generator => `( (1, $subProducer) )
              | .Enumerator => pure subProducer
            nonRecursiveProducers := nonRecursiveProducers.push subGeneratorTerm

        | none => throwError m!"Unable to derive producer schedule for constructor {ctorName}"

      if (not requiredInstances.isEmpty) then
        let deduplicatedInstances := List.eraseDups requiredInstances.toList
        trace[plausible.deriving.arbitrary]  m!"Required typeclass instances (please derive these first if they aren't already defined):\n{deduplicatedInstances}"

      if nonRecursiveProducers.isEmpty && recursiveProducers.isEmpty then
        throwError "Cannot derive constrained producer for '{inductiveName}': no constructor schedules were generated"
      if nonRecursiveProducers.isEmpty then
        throwError "Cannot derive constrained producer for '{inductiveName}': all constructors are recursive (no finite base case)"

      -- Collect all the base / inductive producers into two Lean list terms
      -- Base producers are invoked when `size = 0`, inductive producers are invoked when `size > 0`
      let baseProducers ← `([$nonRecursiveProducers,*])
      let inductiveProducers ← `([$nonRecursiveProducers,*, $recursiveProducers,*])

      return (baseProducers, inductiveProducers, freshenedOutputNames, Lean.mkIdent <$> freshUnknowns, localCtx))

  -- Create an instance of the appropriate producer typeclass
  mkConstrainedProducerTypeClassInstance baseProducers inductiveProducers
    constrainingInductive inductiveLevels freshArgIdents freshenedOutputNames.toList
    outputTypes.toList producerSort localCtx

/-- Compiles an InductiveSchedule from the memo into (def, instance) commands.
    Uses the pre-derived schedules directly (no re-derivation).
    `siblings` is the list of specs in the same mutual block (for rewriting to Source.MutRec). -/
def compileInductiveSchedule (indSched : InductiveSchedule)
    (globalName : Name) (siblings : List (Name × List Nat × Name × DeriveSort))
    : TermElabM (TSyntax `command × TSyntax `command) := do
  let key := indSched.key
  let indInfo ← getConstInfoInduct key.inductiveName
  let indLevels := indInfo.levelParams.map (Level.param ·)
  -- Get arg types using getCorrectTypes (handles dependent types like Eq's α correctly)
  let numArgs := (← getComponentsOfArrowType indInfo.type).size - 1
  let argNames := (List.range numArgs).map (fun i => indSched.argNames.getD i (Name.mkSimple s!"arg_{i}"))
  let argNameTypes : Array (Name × Expr) := Id.run do
    let mut r := #[]
    for i in [:numArgs] do
      r := r.push (argNames.getD i `x, mkSort .zero)  -- placeholder types
    r
  -- Create fvars with placeholder types, then fix with getCorrectTypes
  withLocalDeclsDND argNameTypes fun allFVars => do
  let argTypesLive ← getCorrectTypes allFVars key.inductiveName indLevels
  do
    -- Filter out Sort-typed positions from outputs (those are type params, handled by instance binders)
    let outputIndicesNonSort := key.outputIndices.filter (fun i =>
      match argTypesLive[i]? with | some ty => !ty.isSort | none => true)
    let outputTypes := outputIndicesNonSort.filterMap (fun i => argTypesLive[i]?)
    -- Compile each constructor schedule to a sub-producer term
    let outputType ← if key.deriveSort == .Checker then
        pure (Lean.mkConst ``Bool)
      else
        tupleOfListM (throwError "no output types")
          (fun t rest => do
            let u ← Meta.mkFreshLevelMVar
            let v ← Meta.mkFreshLevelMVar
            pure (Lean.mkApp2 (Lean.mkConst ``Prod [u, v]) t rest)) outputTypes
    let producerSort := convertDeriveSortToProducerSort key.deriveSort
    let freshFuelPrimeName := `fuel'
    let freshSizePrimeName := `size'
    let mut nonRecursiveProducers : Array (TSyntax `term) := #[]
    let mut recursiveProducers : Array (TSyntax `term) := #[]
    let freshSize' := Lean.mkIdent freshSizePrimeName
    -- Helper: rewrite Source.Rec to use globalName + rewrite sibling calls
    let rewriteSchedule := fun (steps : List ScheduleStep) =>
      let mutRewritten := rewriteMutualCalls steps siblings
      -- Also rewrite Source.Rec (self-recursive) to use globalName
      mutRewritten.map fun step =>
        match step with
        | .Unconstrained v (.Rec _ args) ps => .Unconstrained v (.Rec globalName args) ps
        | .SuchThat vs (.Rec _ args) ps => .SuchThat vs (.Rec globalName args) ps
        | .Check (.Rec _ args) pol => .Check (.Rec globalName args) pol
        | other => other
    for (_, schedule) in indSched.baseSchedules do
      let (steps, sort) := schedule
      let rewrittenSteps := rewriteSchedule steps
      let rewrittenSchedule := (rewrittenSteps, sort)
      let (subProducer, _) ← StateT.run (s := #[]) (do
        let mexp ← MExp.scheduleToMExp rewrittenSchedule (.MId `size) (.MId `initSize) outputType
          (fuelPrimeName := freshFuelPrimeName) (sizePrimeName := freshSizePrimeName)
        MExp.mexpToTSyntax mexp key.deriveSort)
      if scheduleUsesMutualCall rewrittenSteps then
        let term ← match key.deriveSort with
          | .Generator => `( ($(Lean.mkIdent ``Nat.succ) $freshSize', $subProducer) )
          | .Enumerator => pure subProducer
          | .Checker | .Theorem => `(fun (_ : Unit) => $subProducer)
        recursiveProducers := recursiveProducers.push term
      else
        let term ← match key.deriveSort with
          | .Generator => `( (1, $subProducer) )
          | .Enumerator => pure subProducer
          | .Checker | .Theorem => `(fun (_ : Unit) => $subProducer)
        nonRecursiveProducers := nonRecursiveProducers.push term
    for (_, schedule) in indSched.recSchedules do
      let (steps, sort) := schedule
      let rewrittenSchedule := (rewriteSchedule steps, sort)
      let (subProducer, _) ← StateT.run (s := #[]) (do
        let mexp ← MExp.scheduleToMExp rewrittenSchedule (.MId `size) (.MId `initSize) outputType
          (fuelPrimeName := freshFuelPrimeName) (sizePrimeName := freshSizePrimeName)
        MExp.mexpToTSyntax mexp key.deriveSort)
      let term ← match key.deriveSort with
        | .Generator => `( ($(Lean.mkIdent ``Nat.succ) $freshSize', $subProducer) )
        | .Enumerator => pure subProducer
        | .Checker | .Theorem => `(fun (_ : Unit) => $subProducer)
      recursiveProducers := recursiveProducers.push term
    -- For checkers with recursive constructors, add a failsafe to the base case:
    -- if no base constructor matches, return "unknown" (error) rather than "false",
    -- since a recursive constructor might succeed at a larger size.
    let baseProducersWithFailsafe ← do
      if (key.deriveSort == .Checker || key.deriveSort == .Theorem) && !recursiveProducers.isEmpty then
        let failsafe ← `((fun (_ : Unit) => $failFn $genericFailure))
        pure (nonRecursiveProducers.push failsafe)
      else
        pure nonRecursiveProducers
    let baseProducers ← `([$baseProducersWithFailsafe,*])
    let allProducers := nonRecursiveProducers ++ recursiveProducers
    let inductiveProducers ← `([$allProducers,*])
    let argNames := (List.range allFVars.size).map (fun i => indSched.argNames.getD i (Name.mkSimple s!"arg_{i}"))
    let freshArgIdents : TSyntaxArray `term := argNames.toArray.map (fun n => Lean.mkIdent n)
    let freshenedOutputNames := outputIndicesNonSort.filterMap (fun i => argNames[i]?)
    -- Compute paramInfo using the live fvars (handles dependent types correctly)
    let liveTypes ← getCorrectTypes allFVars key.inductiveName indLevels
    let liveTypesSyntax ← liveTypes.mapM (fun ty => PrettyPrinter.delab ty)
    let mut paramInfo : Array (Name × Expr × TSyntax `term) := #[]
    for i in [:liveTypes.size] do
      paramInfo := paramInfo.push (argNames.getD i `x, liveTypes[i]!, liveTypesSyntax[i]!)
    mkConstrainedProducerMutualPieces baseProducers inductiveProducers
      key.inductiveName indLevels freshArgIdents freshenedOutputNames
      outputTypes producerSort (← getLCtx) globalName key.deriveSort paramInfo

/-- Recursively derives the best schedule for a SpecKey, populating the memo with
    all transitive dependencies. Returns the score for this spec.

    Follows QuickChick's `inductive_best_valid_schedule` pattern:
    1. Check memo (return cached if found, or optimistic score if inProgress/cycle)
    2. Check if instance already exists (return totalScore)
    3. Insert inProgress placeholder
    4. Derive schedules for each constructor
    5. Collect NonRec deps from chosen schedules → recursively derive
    6. Store result in memo -/
partial def deriveBestInductiveSchedule (key : SpecKey)
    (memo : IO.Ref (Std.HashMap SpecKey MemoEntry))
    (scheduleRewriter : List ScheduleStep → List ScheduleStep := id) : TermElabM Score := do
  -- 1. Check memo
  let current ← memo.get
  match current[key]? with
  | some .inProgress => return default  -- cycle: optimistic (mutual call = cheap)
  | some (.done indSched) => return indSched.score
  | some (.failed _) => return default  -- user must provide; assume partial quality
  | none => pure ()

  -- 2. Non-inductive heads (e.g. LE.le, Not) — try to find an existing instance
  unless (← isInductive key.inductiveName) do
    -- For non-inductives, check if a Decidable instance exists (gives DecOpt via [Decidable P] : DecOpt P)
    let hasInstance ← try
      Meta.withNewMCtxDepth do
        -- Build a proposition with metavar args and check Decidable
        let info ← getConstInfo key.inductiveName
        let mut t := .const key.inductiveName (info.levelParams.map fun _ => .zero)
        let arity := (← getComponentsOfArrowType info.type).size - 1
        for _ in List.range arity do
          let argTy := (← inferType t).bindingDomain!
          let mv ← Meta.mkFreshExprMVar (some argTy)
          t := .app t mv
        let result ← Meta.synthInstance? (← mkAppM ``Decidable #[t])
        pure result.isSome
    catch _ => pure false
    if hasInstance then
      let trivialSched : InductiveSchedule := { key, argNames := [], recFnName := `_, baseSchedules := [], recSchedules := [], score := default, alreadyExists := true }
      memo.modify (·.insert key (.done trivialSched))
      let bundle ← Scoring.getActiveScorerBundle
      return bundle.emptyScore
    else
      memo.modify (·.insert key (.failed s!"{key.inductiveName} is not inductive and has no Decidable instance"))
      let bundle ← Scoring.getActiveScorerBundle
      return bundle.penaltyScore

  -- Check if instance already exists — skip derivation if so
  let indInfo ← getConstInfoInduct key.inductiveName
  let indTypeComponents ← getComponentsOfArrowType indInfo.type
  let argTypes := indTypeComponents.pop
  let nonSortOutputIndices := key.outputIndices.filter (fun i =>
    match argTypes[i]? with | some ty => !ty.isSort | none => true)
  let instanceExists ← Meta.withNewMCtxDepth do
    try
      if nonSortOutputIndices.isEmpty && key.outputIndices.length > 0 then pure true
      else if key.deriveSort == .Checker then
        -- For checkers: synthesize DecOpt (@ind args*) with all args as metavars
        let indLevelsForCheck ← indInfo.levelParams.mapM (fun _ => do
          let lv ← Meta.mkFreshLevelMVar
          pure (.succ lv))
        let numArgs := argTypes.size
        let rec buildAndCheckChecker (idx : Nat) (t : Expr) (fvars : Array Expr) (instIdx : Nat) : TermElabM Bool :=
          if idx >= numArgs then do
            let body := mkAppN (.const key.inductiveName indLevelsForCheck) fvars
            let ty ← mkAppM ``DecOpt #[body]
            let result ← Meta.synthInstance? ty
            pure result.isSome
          else do
            let argTy := (← inferType t).bindingDomain!
            let name := Name.mkSimple s!"arg_{idx}"
            let bi := if argTy.isSort then BinderInfo.implicit else .default
            withLocalDecl name bi argTy fun fv => do
              if argTy.isSort then
                let enumTy ← mkAppM ``Enum #[fv]
                let decEqTy ← mkAppM ``DecidableEq #[fv]
                withLocalDecl (Name.mkSimple s!"inst_enum_{instIdx}") .instImplicit enumTy fun _ =>
                withLocalDecl (Name.mkSimple s!"inst_deceq_{instIdx}") .instImplicit decEqTy fun _ =>
                  buildAndCheckChecker (idx + 1) (.app t fv) (fvars.push fv) (instIdx + 1)
              else
                buildAndCheckChecker (idx + 1) (.app t fv) (fvars.push fv) instIdx
        buildAndCheckChecker 0 (.const key.inductiveName indLevelsForCheck) #[] 0
      else if nonSortOutputIndices.isEmpty then pure false
      else
        -- Build properly-typed fvars by applying the inductive one arg at a time
        -- Then nest withLocalDecl for each + instImplicit for Sort-typed params
        -- Use Level.succ (fresh mvar) for each universe param — ensures Type level (not Prop)
        let indLevelsForCheck ← indInfo.levelParams.mapM (fun _ => do
          let lv ← Meta.mkFreshLevelMVar
          pure (.succ lv))
        let numArgs := argTypes.size
        let rec buildAndCheck (idx : Nat) (t : Expr) (fvars : Array Expr) (instIdx : Nat) : TermElabM Bool :=
          if idx >= numArgs then do
            -- All fvars created — now build predicate and try synthesis
            let outputFVars := nonSortOutputIndices.filterMap (fun i => fvars[i]?)
            let outputTypes ← outputFVars.mapM (fun e => inferType e)
            let outType ← tupleOfListM (throwError "empty")
              (fun t' rest => do
                let u ← Meta.mkFreshLevelMVar
                let v ← Meta.mkFreshLevelMVar
                pure (Lean.mkApp2 (Lean.mkConst ``Prod [u, v]) t' rest)) outputTypes
            withLocalDecl `x .default outType fun xFvar => do
              let mut projections : Array Expr := #[]
              let mut currentExpr := xFvar
              for i in [:outputFVars.length] do
                if outputFVars.length == 1 then projections := projections.push currentExpr
                else if i < outputFVars.length - 1 then
                  projections := projections.push (← mkAppM ``Prod.fst #[currentExpr])
                  currentExpr ← mkAppM ``Prod.snd #[currentExpr]
                else projections := projections.push currentExpr
              let mut appArgs : Array Expr := #[]
              let mut outIdx := 0
              for i in [:fvars.size] do
                if i ∈ nonSortOutputIndices then
                  appArgs := appArgs.push projections[outIdx]!
                  outIdx := outIdx + 1
                else
                  appArgs := appArgs.push fvars[i]!
              let body := mkAppN (.const key.inductiveName indLevelsForCheck) appArgs
              let pred ← mkLambdaFVars #[xFvar] body
              let tcName ← match key.deriveSort with
                | .Generator => pure ``ArbitrarySizedSuchThat
                | .Enumerator => pure ``EnumSizedSuchThat
                | .Checker | .Theorem => throwError "synthInstance check: checker case should be handled above"
              let ty ← mkAppM tcName #[outType, pred]
              let result ← Meta.synthInstance? ty
              pure result.isSome
          else do
            -- Get the type of the next arg from the partially-applied inductive
            let argTy := (← inferType t).bindingDomain!
            let name := Name.mkSimple s!"arg_{idx}"
            let bi := if argTy.isSort then BinderInfo.implicit else .default
            withLocalDecl name bi argTy fun fv => do
              -- If Sort-typed, add Arbitrary + DecidableEq instance fvars
              if argTy.isSort then
                let arbTy ← mkAppM ``Plausible.Arbitrary #[fv]
                let decEqTy ← mkAppM ``DecidableEq #[fv]
                withLocalDecl (Name.mkSimple s!"inst_arb_{instIdx}") .instImplicit arbTy fun _ =>
                withLocalDecl (Name.mkSimple s!"inst_deceq_{instIdx}") .instImplicit decEqTy fun _ =>
                  buildAndCheck (idx + 1) (.app t fv) (fvars.push fv) (instIdx + 1)
              else
                buildAndCheck (idx + 1) (.app t fv) (fvars.push fv) instIdx
        buildAndCheck 0 (.const key.inductiveName indLevelsForCheck) #[] 0
    catch _ => pure false
  if instanceExists then
    let trivialSched : InductiveSchedule := { key, argNames := [], recFnName := `_, baseSchedules := [], recSchedules := [], score := default, alreadyExists := true }
    memo.modify (·.insert key (.done trivialSched))
    let bundle ← Scoring.getActiveScorerBundle
    return bundle.emptyScore

  -- 3. Insert inProgress placeholder (cycle detection)
  memo.modify (·.insert key .inProgress)
  let startTime ← IO.monoNanosNow

  -- 4. Derive schedules for each constructor
  let indInfo ← getConstInfoInduct key.inductiveName
  let indTypeComponents ← getComponentsOfArrowType indInfo.type
  let argTypes := indTypeComponents.pop
  let varPool := #["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"]
  let argNames := (List.range argTypes.size).map (fun i => Name.mkSimple (varPool.getD i s!"v{i}"))
  let argNamesTypes := argNames.toArray.zip argTypes


  let mut baseSchedules : List (Name × Schedule) := []
  let mut recSchedules : List (Name × Schedule) := []
  let mut allDeps : Array ScheduleDep := #[]

  try
    let results ← withLocalDeclsDND argNamesTypes fun _ => do
      let mut localCtx ← getLCtx
      let mut freshUnknowns := #[]
      for argName in argNames do
        let freshArgName := localCtx.getUnusedName argName
        localCtx := localCtx.renameUserName argName freshArgName
        freshUnknowns := freshUnknowns.push freshArgName

      let freshenedInputNames := freshUnknowns.toList.filter
        (fun n => key.outputIndices.all (fun idx => freshUnknowns.getD idx `_ != n))
      let freshenedOutputNamesTypesIndices : List (Name × Expr × Nat) :=
        key.outputIndices.map (fun idx => (freshUnknowns.getD idx `x, argTypes.getD idx (mkSort .zero), idx))
      let freshRecFnName := localCtx.getUnusedName `aux_arb

      let mut base : List (Name × Schedule) := []
      let mut rec_ : List (Name × Schedule) := []
      let mut deps : Array ScheduleDep := #[]
      let mut ctorStats : List (Name × Nat × Nat × Score) := []

      for ctorName in indInfo.ctors do
        try
          let ctorStart ← IO.monoNanosNow
          let currentMemo ← memo.get
          let resultOption ← (UnifyM.runInMetaM
            (getProducerScheduleForInductiveConstructor key.inductiveName ctorName
              freshenedOutputNamesTypesIndices freshenedInputNames freshUnknowns
              key.deriveSort localCtx freshRecFnName currentMemo)
              emptyUnifyState)
          let ctorEnd ← IO.monoNanosNow
          let ctorElapsed := (ctorEnd - ctorStart) / 1000
          match resultOption with
          | some result =>
            let (scheduleSteps, scheduleSort) := result.schedule
            ctorStats := ctorStats ++ [(ctorName, ctorElapsed, result.schedulesConsidered, result.score)]
            let rewrittenSteps := scheduleRewriter scheduleSteps
            let schedule := (rewrittenSteps, scheduleSort)
            let ctorDeps := collectNonRecDeps rewrittenSteps
            for dep in ctorDeps do
              if !deps.contains dep then
                deps := deps.push dep
            let isRec ← isConstructorRecursive key.inductiveName ctorName
            if isRec || scheduleUsesMutualCall rewrittenSteps then
              rec_ := rec_ ++ [(ctorName, schedule)]
            else
              base := base ++ [(ctorName, schedule)]
          | none => pure ()
        catch _ => pure ()
      return (base, rec_, deps, freshUnknowns.toList, freshRecFnName, ctorStats)

    let (base, rec_, deps, fNames, (rFnName, ctorStats)) := results
    baseSchedules := base
    recSchedules := rec_
    allDeps := deps
    -- 5. Recursively derive deps
    for dep in deps do
      if dep.kind == .relation || dep.kind == .checker then
        let depKey : SpecKey := { inductiveName := dep.inductiveName, outputIndices := dep.outputIndices, deriveSort := dep.deriveSort }
        let _ ← deriveBestInductiveSchedule depKey memo scheduleRewriter
    -- 6. Store result
    let endTime ← IO.monoNanosNow
    let elapsed := (endTime - startTime) / 1000
    let ctorScoreList := ctorStats.map fun (name, _, _, s) => (name, s)
    let score ← PatternCoverage.computeInductiveScore key.inductiveName key.outputIndices ctorScoreList
    let indSched : InductiveSchedule := {
      key := key
      argNames := fNames
      recFnName := rFnName
      baseSchedules := base
      recSchedules := rec_
      score := score
      derivationTimeUs := elapsed
      ctorStats := ctorStats
    }
    memo.modify (·.insert key (.done indSched))
    return score
  catch e =>
    let msg ← e.toMessageData.toString
    memo.modify (·.insert key (.failed s!"Failed to derive schedules for {key.inductiveName}: {msg}"))
    let bundle ← Scoring.getActiveScorerBundle
    return bundle.penaltyScore

/-- Derives schedules for a spec and returns the dependencies (Source.NonRec calls)
    without compiling to code. Used by auto-derive to discover what instances are needed. -/
def collectSpecDependencies
  (_args : Array Expr) (outputVars : Array Expr) (outputTypes : Array Expr)
  (constrainingInductive : Name) (_inductiveLevels : List Level)
  (constrArgs : Array Expr) (deriveSort : DeriveSort)
  (scheduleRewriter : List ScheduleStep → List ScheduleStep := id)
  (recFnNameOverride : Option Name := none) :
  TermElabM (Array ScheduleDep) := do
  let inductiveName := constrainingInductive
  let outputFVars := outputVars.map Expr.fvarId!
  let mut outputIdxs : Array Nat := #[]
  for i in [:constrArgs.size] do
    let arg := constrArgs[i]!
    if arg.isFVar && outputFVars.contains arg.fvarId! then
      outputIdxs := outputIdxs.push i
  if outputIdxs.isEmpty then
    throwError m!"cannot find output indices"
  let inductiveVal ← getConstInfoInduct inductiveName
  let inductiveTypeComponents ← getComponentsOfArrowType inductiveVal.type
  let argTypes := inductiveTypeComponents.pop
  let argNames ← constrArgs.mapIdxM
    (fun i (ident : Expr) =>
      if ident.isFVar then ident.fvarId!.getUserName
      else if let some outIdx := outputIdxs.findIdx? (· == i) then
        outputVars[outIdx]!.fvarId!.getUserName
      else throwError m!"{ident} is expected to be a variable.")
  let argNamesTypes := argNames.zip argTypes
  withLocalDeclsDND argNamesTypes (fun _ => do
    let mut localCtx ← getLCtx
    let mut freshUnknowns := #[]
    for argName in argNames do
      let freshArgName := localCtx.getUnusedName argName
      localCtx := localCtx.renameUserName argName freshArgName
      freshUnknowns := freshUnknowns.push freshArgName
    let freshenedOutputNames := outputIdxs.map (fun idx => freshUnknowns[idx]!)
    let freshenedInputNamesExcludingOutput := freshUnknowns.toList.filter
      (fun n => freshenedOutputNames.toList.all (· != n))
    let outputNamesTypesIndices : List (Name × Expr × Nat) :=
      (List.range outputIdxs.size).map (fun i =>
        (freshenedOutputNames[i]!, outputTypes[i]!, outputIdxs[i]!))
    let freshRecFnName := recFnNameOverride.getD (localCtx.getUnusedName `aux_arb)
    let mut allDeps : Array ScheduleDep := #[]
    for ctorName in inductiveVal.ctors do
      let resultOption ← (UnifyM.runInMetaM
        (getProducerScheduleForInductiveConstructor inductiveName ctorName outputNamesTypesIndices
          freshenedInputNamesExcludingOutput freshUnknowns deriveSort localCtx freshRecFnName)
          emptyUnifyState)
      match resultOption with
      | some result =>
        let (scheduleSteps, _) := result.schedule
        let rewrittenSteps := scheduleRewriter scheduleSteps
        let deps := collectNonRecDeps rewrittenSteps
        for dep in deps do
          if !allDeps.contains dep then
            allDeps := allDeps.push dep
      | none => pure ()
    return allDeps)

/-- Like `deriveConstrainedProducer` but returns the components needed for assembly
    into either a standalone instance or a mutual def block.
    Returns: (baseProducers, inductiveProducers, freshenedOutputNames, freshArgIdents, outputTypes, localCtx, inductiveName, inductiveLevels, producerSort) -/
def deriveConstrainedProducerParts
  (_args : Array Expr) (outputVars : Array Expr) (outputTypes : Array Expr)
  (constrainingInductive : Name) (inductiveLevels : List Level)
  (constrArgs : Array Expr) (deriveSort : DeriveSort)
  (scheduleRewriter : List ScheduleStep → List ScheduleStep := id)
  (recFnNameOverride : Option Name := none) :
  TermElabM (TSyntax `term × TSyntax `term × Array Name × TSyntaxArray `term × Array Expr × LocalContext × Name × List Level × ProducerSort) := do
  let producerSort := convertDeriveSortToProducerSort deriveSort
  -- Identify which argument positions are outputs (to be generated)
  let inductiveName := constrainingInductive
  let outputFVars := outputVars.map Expr.fvarId!
  let mut outputIdxs : Array Nat := #[]
  for i in [:constrArgs.size] do
    let arg := constrArgs[i]!
    if arg.isFVar && outputFVars.contains arg.fvarId! then
      outputIdxs := outputIdxs.push i
  if outputIdxs.isEmpty then
    throwError m!"cannot find output indices, try specifying the implicit arguments"
  -- Extract argument names and types from the inductive's type signature
  let inductiveVal ← getConstInfoInduct inductiveName
  let inductiveTypeComponents ← getComponentsOfArrowType inductiveVal.type
  let argTypes := inductiveTypeComponents.pop
  let argNames ← constrArgs.mapIdxM
    (fun i (ident : Expr) =>
      if ident.isFVar then ident.fvarId!.getUserName
      else if let some outIdx := outputIdxs.findIdx? (· == i) then
        outputVars[outIdx]!.fvarId!.getUserName
      else throwError m!"{ident} is expected to be a variable.")
  let argNamesTypes := argNames.zip argTypes
  -- Build the output product type (e.g., α × β for two outputs)
  let _outputType ← tupleOfListM (throwError "no output types")
    (fun t rest => do
      let u ← Meta.mkFreshLevelMVar
      let v ← Meta.mkFreshLevelMVar
      pure (Lean.mkApp2 (Lean.mkConst ``Prod [u, v]) t rest)) outputTypes.toList
  let (baseProducers, inductiveProducers, freshenedOutputNames, freshArgIdents, localCtx) ←
  -- Freshen argument names to avoid capture, then derive schedules per constructor
    withLocalDeclsDND argNamesTypes (fun _ => do
      let mut localCtx ← getLCtx
      let mut freshUnknowns := #[]
      for argName in argNames do
        let freshArgName := localCtx.getUnusedName argName
        localCtx := localCtx.renameUserName argName freshArgName
        freshUnknowns := freshUnknowns.push freshArgName
      let freshenedOutputNames := outputIdxs.map (fun idx => freshUnknowns[idx]!)
      let freshenedInputNamesExcludingOutput := freshUnknowns.toList.filter
        (fun n => freshenedOutputNames.toList.all (· != n))
      let outputNamesTypesIndices : List (Name × Expr × Nat) :=
        (List.range outputIdxs.size).map (fun i =>
          (freshenedOutputNames[i]!, outputTypes[i]!, outputIdxs[i]!))
      let mut nonRecursiveProducers := #[]
      let mut recursiveProducers := #[]
      let freshFuelPrimeName := localCtx.getUnusedName `fuel'
      let freshSizePrimeName := localCtx.getUnusedName `size'
      let freshSize' := mkIdent freshSizePrimeName
      let freshRecFnName := recFnNameOverride.getD (localCtx.getUnusedName (match deriveSort with
        | .Generator => `aux_arb | .Enumerator => `aux_enum | _ => `aux_dec))
      -- For each constructor: derive a schedule, compile to syntax
      for ctorName in inductiveVal.ctors do
        let resultOption ← (UnifyM.runInMetaM
          (getProducerScheduleForInductiveConstructor inductiveName ctorName outputNamesTypesIndices
            freshenedInputNamesExcludingOutput freshUnknowns deriveSort localCtx freshRecFnName)
            emptyUnifyState)
        match resultOption with
        | some result =>
          let (scheduleSteps, scheduleSort) := result.schedule
          let rewrittenSteps := scheduleRewriter scheduleSteps
          let schedule := (rewrittenSteps, scheduleSort)
          let (subProducer, requiredInsts) ← StateT.run (s := #[]) (do
            let mexp ← MExp.scheduleToMExp schedule (.MId `size) (.MId `initSize) _outputType (fuelPrimeName := freshFuelPrimeName) (sizePrimeName := freshSizePrimeName)
            MExp.mexpToTSyntax mexp deriveSort)
          if !requiredInsts.isEmpty then
            let outputIdxsStr := outputNamesTypesIndices.map (fun (n, _, i) => s!"{n}@{i}")
            trace[plausible.deriving.arbitrary] m!"[{repr deriveSort}] {inductiveName} (outputs: {outputIdxsStr}) constructor {ctorName} requires: {requiredInsts}"
          let isRecursive ← (isConstructorRecursive inductiveName ctorName) <||> pure (scheduleUsesMutualCall rewrittenSteps)
          if isRecursive then
            let subProducerTerm ← match producerSort with
              | .Generator => `( ($(mkIdent ``Nat.succ) $freshSize', $subProducer) )
              | .Enumerator => pure subProducer
            recursiveProducers := recursiveProducers.push subProducerTerm
          else
            let subGeneratorTerm ← match producerSort with
              | .Generator => `( (1, $subProducer) )
              | .Enumerator => pure subProducer
            nonRecursiveProducers := nonRecursiveProducers.push subGeneratorTerm
        | none => throwError m!"Unable to derive producer schedule for constructor {ctorName}"
      if nonRecursiveProducers.isEmpty && recursiveProducers.isEmpty then
        throwError "Cannot derive constrained producer for '{inductiveName}': no constructor schedules were generated"
      if nonRecursiveProducers.isEmpty then
        throwError "Cannot derive constrained producer for '{inductiveName}': all constructors are recursive (no finite base case)"
      let baseProducers ← `([$nonRecursiveProducers,*])
      let inductiveProducers ← `([$nonRecursiveProducers,*, $recursiveProducers,*])
      return (baseProducers, inductiveProducers, freshenedOutputNames, Lean.mkIdent <$> freshUnknowns, localCtx))
  return (baseProducers, inductiveProducers, freshenedOutputNames, freshArgIdents, outputTypes, localCtx, inductiveName, inductiveLevels, producerSort)


private def deriveArbitrarySuchThatInstance'
  (args : Array Expr)
  (outVars : Array Expr)
  (outTypes : Array Expr)
  (constrainingInductive : Name)
  (inductiveLevels : List Level)
  (constrArgs : Array Expr) :
  TermElabM (TSyntax `command) := do
  deriveConstrainedProducer args outVars outTypes constrainingInductive inductiveLevels constrArgs (deriveSort := .Generator)

/-- Peels nested existentials from `∃ x₁, ∃ x₂, ..., P x₁ x₂ ...`, calling `action` inside
    the nested lambdaTelescope scopes so that fvars remain in scope. -/
private partial def peelExistentialsAux (body : Expr) (outVars : Array Expr) (outTypes : Array Expr)
    (action : Expr → Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  match body.app2? ``Exists with
  | .some (outTy, innerBody) =>
    let innerBody ← whnf innerBody
    lambdaTelescope innerBody fun binders innerBody' => do
      if h : binders.size > 0 then
        peelExistentialsAux innerBody' (outVars.push binders[0]) (outTypes.push outTy) action
      else
        action body outVars outTypes
  | .none => action body outVars outTypes

/-- Parses the user-supplied derivation constraint, extracting the input args, output vars, output types,
    constraining inductive name, its levels, and its arguments. Supports multiple existential outputs. -/
private def withParsedDerivingArgs (input : Expr)
  (action :
    (args : Array Expr) → (outVars : Array Expr) → (outTypes : Array Expr) →
    (constrInd : Name) → (constrLevels : List Level) → (constrArgs : Array Expr) → TermElabM α) : TermElabM α :=
  lambdaTelescope input <|
  fun args body => do
  peelExistentialsAux body #[] #[] fun innerBody outVars outTypes => do
  if outVars.isEmpty then
    throwError m!"Error in parsing constraint: {body} is not of the form ∃ x, P."
  innerBody.withApp <|
  fun ind indArgs => do
  if !ind.isConst then throwError m!"Error in parsing constraint: {ind} is expected to be a constant."
  let indName := ind.constName!
  let indLevels := ind.constLevels!
  action args outVars outTypes indName indLevels indArgs

/-- Derives an instance of the `ArbitrarySuchThat` typeclass,
    where `outputVar` and `outputTypeSyntax` are the name & type of the value to be generated,
    and `constrainingProp` is a proposition which generated values need to satisfy -/
def deriveArbitrarySuchThatInstance (tm : Term) : TermElabM Command := do
  let e ← elabTerm tm .none
  withParsedDerivingArgs e deriveArbitrarySuchThatInstance'

def deriveEnumSuchThatInstance' (args : Array Expr) (outVars : Array Expr) (outTypes : Array Expr)
  (constrainingProp : Name) (inductiveLevels : List Level) (constrArgs : Array Expr) : TermElabM (TSyntax `command) :=
  deriveConstrainedProducer args outVars outTypes constrainingProp inductiveLevels constrArgs (deriveSort := .Enumerator)

/-- Derives an instance of the `EnumSuchThat` typeclass,
    where `outputVar` and `outputTypeSyntax` are the name & type of the value to be generated,
    and `constrainingProp` is a proposition which generated values need to satisfy -/
def deriveEnumSuchThatInstance (tm : Term) : TermElabM Command := do
  let e ← elabTerm tm .none
  withParsedDerivingArgs e deriveEnumSuchThatInstance'

/-- Command for deriving a constrained generator for an inductive relation -/
syntax (name := generator_deriver) "derive_generator" term : command

/-- Elaborator for the `derive_generator` command which derives a constrained generator
    using generator schedules from Testing Theorems & the unification algorithm from Generating Good Generators -/
@[command_elab generator_deriver]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(derive_generator $descr:term) => do
    -- Derive an instance of the `ArbitrarySuchThat` typeclass
    let typeClassInstance ← liftTermElabM <| deriveArbitrarySuchThatInstance descr

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this generator: ")

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax

/-- Command for deriving a constrained generator with multi-output hypothesis steps -/
syntax (name := generator_multi_deriver) "derive_generator_multi" term : command

/-- Elaborator for `derive_generator_multi` — same as `derive_generator` but allows each
    hypothesis to produce maximally many outputs at once (requires multi-output instances). -/
@[command_elab generator_multi_deriver]
def elabDeriveGeneratorMulti : CommandElab := fun stx => do
  match stx with
  | `(derive_generator_multi $descr:term) => do
    withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
      let typeClassInstance ← liftTermElabM <| deriveArbitrarySuchThatInstance descr
      let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)
      liftTermElabM $ Tactic.TryThis.addSuggestion stx
        (Format.pretty genFormat) (header := "Try this generator: ")
      elabCommand typeClassInstance
  | _ => throwUnsupportedSyntax

/-- Command for deriving a constrained enumerator for an inductive relation -/
syntax (name := enumerator_deriver) "derive_enumerator" term : command

/-- Elaborator for the `derive_generator` command which derives a constrained generator
    using generator schedules from Testing Theorems & the unification algorithm from Generating Good Generators -/
@[command_elab enumerator_deriver]
def elabDeriveScheduledEnumerator : CommandElab := fun stx => do
  match stx with
  | `(derive_enumerator $descr:term) => do
    -- Derive an instance of the `Enumerate` typeclass
    let typeClassInstance ← liftTermElabM <| deriveEnumSuchThatInstance descr

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

    -- Display the code for the derived enumerator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this enumerator: ")

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax

/-! ## Mutual derivation command

`derive_mutual` derives multiple constrained producers/checkers/enumerators simultaneously,
allowing them to call each other for recursive/mutual-recursive relations.

### Syntax:
```
derive_mutual
  generator (fun τ => ∃ (Γ : List type) (e : term), typing Γ e τ),
  generator_multi (∃ (Γ : List type) (e : term) (τ : type), typing Γ e τ),
  checker (fun Γ e τ => typing Γ e τ)
```

Each entry is either `generator`, `generator_multi`, `enumerator`, or `checker` followed by
a term describing the constraint. Entries in the same SCC are compiled into a shared
`mutual` block with cross-calls rewritten to `Source.MutRec`.
-/

/-- Command for deriving multiple constrained generators in sequence,
    each with multi-output hypothesis steps enabled.
    Later entries can use instances derived by earlier ones.
    Each entry can optionally be prefixed with a sort keyword (default: generator). -/
syntax mutualEntry := ("generator" <|> "enumerator" <|> "checker")? term
syntax (name := mutual_deriver) "derive_mutual" mutualEntry,+ : command

/-- Derives a constrained producer instance directly from a ScheduleDep,
    without going through syntax parsing. Returns the instance command. -/
def deriveFromScheduleDep (dep : ScheduleDep) (scheduleRewriter : List ScheduleStep → List ScheduleStep := id)
    (recFnNameOverride : Option Name := none) : TermElabM (TSyntax `command) := do
  let indInfo ← getConstInfoInduct dep.inductiveName
  let indLevels := indInfo.levelParams.map (Level.param ·)
  let indTypeComponents ← getComponentsOfArrowType indInfo.type
  let argTypes := indTypeComponents.pop
  -- Create fvars for all args
  let argNameTypes : Array (Name × Expr) := Id.run do
    let mut result := #[]
    let mut inpIdx := 0
    let mut outIdx := 0
    for i in [:argTypes.size] do
      if i ∈ dep.outputIndices then
        let name := Name.mkSimple s!"out_{outIdx}"
        result := result.push (name, argTypes[i]!)
        outIdx := outIdx + 1
      else
        let name := Name.mkSimple s!"inp_{inpIdx}"
        result := result.push (name, argTypes[i]!)
        inpIdx := inpIdx + 1
    result
  withLocalDeclsDND argNameTypes fun allFVars => do
    let inputFVars := Id.run do
      let mut result := #[]
      for i in [:argTypes.size] do
        if i ∉ dep.outputIndices then
          result := result.push allFVars[i]!
      result
    let outputFVars := Id.run do
      let mut result := #[]
      for i in [:argTypes.size] do
        if i ∈ dep.outputIndices then
          result := result.push allFVars[i]!
      result
    let outputTypes := dep.outputIndices.filterMap (fun i => argTypes[i]?)
    let deriveSort := dep.deriveSort
    let parts ← deriveConstrainedProducerParts inputFVars outputFVars outputTypes.toArray
      dep.inductiveName indLevels allFVars deriveSort scheduleRewriter recFnNameOverride
    let (baseProducers, inductiveProducers, freshenedOutputNames, freshArgIdents, outTypes, localCtx, _, _, producerSort) := parts
    mkConstrainedProducerTypeClassInstance baseProducers inductiveProducers
      dep.inductiveName indLevels freshArgIdents freshenedOutputNames.toList
      outTypes.toList producerSort localCtx

@[command_elab mutual_deriver]
def elabDeriveMutual : CommandElab := fun stx => do
  match stx with
  | `(derive_mutual $entries,*) => do
    withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
      let specEntries := entries.getElems

      -- Step 1: Parse all specs to get (inductiveName, outputIdxs, deriveSort) and assign global def names
      let mut specMeta : Array (Name × List Nat × Name × DeriveSort) := #[]
      for i in [:specEntries.size] do
        let entry := specEntries[i]!
        -- Parse the optional sort keyword from the mutualEntry syntax
        let (deriveSort, termStx) : DeriveSort × (TSyntax `term) := Id.run do
          let children := entry.raw.getArgs
          -- mutualEntry = ("generator" | "enumerator" | "checker")? term
          -- If keyword present: children[0] is the keyword, children[1] is the term
          -- If no keyword: children[0] is empty, children[1] is the term (or just the term)
          if children.size >= 2 then
            let kw := children[0]!
            let tm := children[1]!
            if kw.isOfKind `null && kw.getArgs.isEmpty then
              (.Generator, ⟨tm⟩)
            else
              let sort := if kw.getArgs.any (fun a => a.getKind == `token.checker) then .Checker
                else if kw.getArgs.any (fun a => a.getKind == `token.enumerator) then .Enumerator
                else .Generator
              (sort, ⟨tm⟩)
          else
            (.Generator, ⟨entry.raw⟩)
        let (indName, outIdxs) ← liftTermElabM do
          let e ← elabTerm termStx .none
          lambdaTelescope e fun _args body => do
            peelExistentialsAux body #[] #[] fun innerBody outVars _outTypes => do
              innerBody.withApp fun ind indArgs => do
                if !ind.isConst then throwError "Expected constant in derive_mutual spec"
                let indName := ind.constName!
                let outputFVars := outVars.map Expr.fvarId!
                let mut idxs : Array Nat := #[]
                for j in [:indArgs.size] do
                  if indArgs[j]!.isFVar && outputFVars.contains indArgs[j]!.fvarId! then
                    idxs := idxs.push j
                return (indName, idxs.toList)
        let uid ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_mutual)
        let globalName := Name.mkSimple s!"{uid}_{indName.toString.replace "." "_"}_{i}"
        specMeta := specMeta.push (indName, outIdxs, globalName, deriveSort)

      -- Auto-derive: recursively discover and derive all transitive dependencies
      -- Step 2: Derive schedules (auto-derive discovers transitive deps, or manual mode)
      let autoDerive := Lean.Option.get (← getOptions) specimen.autoDeriveDeps
      if autoDerive then
        let memo ← IO.mkRef ({} : Std.HashMap SpecKey MemoEntry)
        -- Recursively derive schedules for all user specs (populates memo with all deps)
        for (indName, outIdxs, _, ds) in specMeta do
          let key : SpecKey := { inductiveName := indName, outputIndices := outIdxs, deriveSort := ds }
          let _ ← liftTermElabM <| deriveBestInductiveSchedule key memo
        -- DFS from roots to find actually-used deps
        let finalMemo ← memo.get
        let mut usedKeys : Std.HashSet SpecKey := {}
        for (indName, outIdxs, _, ds) in specMeta do
          let key : SpecKey := { inductiveName := indName, outputIndices := outIdxs, deriveSort := ds }
          usedKeys := collectUsedDeps key finalMemo usedKeys
        -- Add all used deps to specMeta (so they're included in the mutual block)
        for key in usedKeys.toList do
          let inBlock := specMeta.any fun (sIndName, sOutIdxs, _, sDs) =>
            sIndName == key.inductiveName && sOutIdxs == key.outputIndices && sDs == key.deriveSort
          if !inBlock then
            let uid ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_mutual)
            let globalName := Name.mkSimple s!"{uid}_{key.inductiveName.toString.replace "." "_"}_auto"
            specMeta := specMeta.push (key.inductiveName, key.outputIndices, globalName, key.deriveSort)
        -- Use SCC-based compilation from memo
        -- Step 3: SCC decomposition and compilation
        let components := computeSpecSCC usedKeys.toList finalMemo
        -- Print dependency graph + emission order as rich HTML
        let getNumArgs (k : SpecKey) : CommandElabM Nat := liftTermElabM do
          try pure ((← getComponentsOfArrowType (← getConstInfoInduct k.inductiveName).type).size - 1)
          catch _ => pure k.outputIndices.length
        let mut totalEdges : Nat := 0
        for k in usedKeys.toList do
          match finalMemo[k]? with
          | some (.done indSched) =>
            let allScheds := indSched.baseSchedules ++ indSched.recSchedules
            let deps := allScheds.flatMap (fun (_, (steps, _)) => collectNonRecDeps steps)
            let relDeps := deps.filter (fun d => d.kind == .relation || d.kind == .checker)
            let depKeys := relDeps.map (fun d => SpecKey.mk d.inductiveName d.outputIndices d.deriveSort)
              |>.filter (usedKeys.contains ·) |>.eraseDups
            totalEdges := totalEdges + depKeys.length
          | _ => pure ()
        -- Build HTML output using ProofWidgets (controlled by specimen.richOutput)
        let richOutput := Lean.Option.get (← getOptions) specimen.richOutput
        let mkSpan (style : Json) (text : String) : Html :=
          .element "span" #[("style", style)] #[.text text]
        let headerStyle := json% {"fontWeight": "bold", "fontSize": "1.2em", "color": "#4fc1ff"}
        let srcStyle := json% {"color": "#dcdcaa", "fontWeight": "bold"}
        let dstStyle := json% {"color": "#9cdcfe"}
        let reqStyle := json% {"color": "#c586c0", "fontStyle": "italic"}
        let schedStyle := json% {"color": "#ce9178", "fontSize": "0.9em", "whiteSpace": "pre", "fontFamily": "var(--vscode-editor-font-family, monospace)"}
        let singletonStyle := json% {"color": "#b5cea8"}
        let mutualStyle := json% {"color": "#ce9178", "fontWeight": "bold"}
        let scoreStyle := json% {"color": "#808080", "fontSize": "0.9em"}
        let mut htmlChildren : Array Html := #[]
        -- Title
        htmlChildren := htmlChildren.push (.element "div" #[("style", json% {"marginBottom": "12px"})] #[
          mkSpan headerStyle s!"⚙ derive_mutual — {usedKeys.size} specs, {components.length} components"
        ])
        -- Merged emission order + constructor schedules (topological)
        let bundle ← liftTermElabM Scoring.getActiveScorerBundle
        -- Score color: green (good) → red (bad) via bundle.scoreBadness ∈ [0,1]
        let scoreToColor (score : Score) : String :=
          let b := bundle.scoreBadness score
          let hue := (1.0 - b) * 120.0
          s!"hsl({Float.toString hue}, 70%, 60%)"
        -- Aggregate spec-level color from the inductive-level score
        let specColor (indSched : InductiveSchedule) : String :=
          scoreToColor indSched.score
        let mkCtorItems (indSched : InductiveSchedule) : Array Html := Id.run do
          let allScheds := indSched.baseSchedules ++ indSched.recSchedules
          let mut items : Array Html := #[]
          for (ctorName, schedule@(steps, _)) in allScheds do
            let isBase := indSched.baseSchedules.any (fun (n, _) => n == ctorName)
            let tag := if isBase then "base" else "rec"
            let tagColor := if isBase then json% {"color": "#4ec9b0"} else json% {"color": "#d7ba7d"}
            let (ctorInfoStr, ctorColor) := match indSched.ctorStats.find? (fun (n, _, _, _) => n == ctorName) with
              | some (_, us, count, score) =>
                let timeStr := if us >= 1000 then s!"{us / 1000}ms" else if us > 0 then s!"{us}μs" else ""
                let countStr := if count > 1 then s!"{count} considered" else ""
                let scoreStr := bundle.reprScore score
                let parts := [timeStr, countStr, scoreStr].filter (· != "")
                (s!" ({String.intercalate ", " parts})", scoreToColor score)
              | none => ("", scoreToColor bundle.emptyScore)
            let ctorNameStyle := json% {"color": $(ctorColor), "fontWeight": "bold"}
            items := items.push (Html.element "details" #[] #[
              .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                mkSpan ctorNameStyle ctorName.getString!,
                .text " ",
                mkSpan tagColor s!"[{tag}]",
                mkSpan scoreStyle ctorInfoStr
              ],
              .element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "6px", "padding": "4px 8px", "background": "#1a1a2e", "borderRadius": "4px", "border": "1px solid #2a2a4a", "whiteSpace": "pre", "fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "0.9em", "lineHeight": "1.5"})]
                (let stepHtmls := steps.toArray.map fun step =>
                  let stepStr := ppStep step
                  let color := match step with
                    | .Check _ false => "hsl(0, 70%, 60%)"
                    | .Check (.NonRec (name, _)) true =>
                      let depKey := SpecKey.mk name [] .Checker
                      match finalMemo[depKey]? with
                      | some (.done depSched) => specColor depSched
                      | _ => "hsl(30, 70%, 60%)"
                    | .Check _ true => "hsl(30, 70%, 60%)"
                    | .Unconstrained _ (.NonRec (name, _)) _ =>
                      let depKey := SpecKey.mk name [] .Generator
                      match finalMemo[depKey]? with
                      | some (.done depSched) => specColor depSched
                      | _ => "hsl(60, 70%, 60%)"
                    | .Unconstrained _ _ _ => "hsl(60, 70%, 60%)"
                    | .SuchThat vs (.NonRec (name, args)) ps =>
                      let outNames := vs.map Prod.fst
                      let outIdxs := computeOutputIndices args outNames
                      let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
                      let depKey := SpecKey.mk name outIdxs ds
                      match finalMemo[depKey]? with
                      | some (.done depSched) => specColor depSched
                      | _ => "hsl(90, 70%, 60%)"
                    | .SuchThat _ (.Rec ..) _ => "hsl(200, 50%, 60%)"
                    | .SuchThat _ (.MutRec ..) _ => "hsl(200, 50%, 60%)"
                    | .Match .. => "hsl(120, 40%, 60%)"
                  Html.element "div" #[] #[mkSpan (json% {"color": $(color)}) stepStr]
                let (_, sort) := schedule
                let conclusionStr := match sort with
                  | .ProducerSchedule _ conclusion =>
                    let outputStr := match conclusion with
                      | [e] => ppConstructorExpr e
                      | es => s!"({String.intercalate ", " (es.map ppConstructorExpr)})"
                    s!"return {outputStr}"
                  | .CheckerSchedule => "return ok"
                  | .TheoremSchedule hyp _ => s!"check_conclusion {ppHypothesisExpr hyp}"
                let conclusionHtml := Html.element "div" #[] #[mkSpan (json% {"color": "hsl(120, 70%, 70%)"}) conclusionStr]
                stepHtmls.push conclusionHtml)
            ])
          items
        let mut orderItems : Array Html := #[]
        for comp in components do
          if comp.length > 1 then
            let mut mutualItems : Array Html := #[]
            for k in comp do
              let numArgs ← getNumArgs k
              match finalMemo[k]? with
              | some (.done indSched) =>
                let timeStr := if indSched.derivationTimeUs >= 1000 then s!" {indSched.derivationTimeUs / 1000}ms"
                  else if indSched.derivationTimeUs > 0 then s!" {indSched.derivationTimeUs}μs" else ""
                let nCtors := indSched.baseSchedules.length + indSched.recSchedules.length
                let ctorItems := mkCtorItems indSched
                let specNameStyle := json% {"color": $(specColor indSched), "fontWeight": "bold"}
                let indScoreStr := bundle.reprScore indSched.score
                mutualItems := mutualItems.push (Html.element "details" #[] #[
                  .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                    mkSpan specNameStyle (k.prettyPrint numArgs),
                    mkSpan scoreStyle s!" ({nCtors} ctors{timeStr}) score: {indScoreStr}"
                  ],
                  .element "div" #[("style", json% {"marginLeft": "12px"})] ctorItems
                ])
              | _ => pure ()
            orderItems := orderItems.push (.element "div" #[("style", json% {"marginBottom": "6px", "paddingLeft": "4px", "borderLeft": "3px solid #ce9178"})] (#[
              mkSpan mutualStyle s!"◆ mutual ({comp.length}):",
              .element "br" #[] #[]
            ] ++ mutualItems))
          else
            let k := comp.head!
            let numArgs ← getNumArgs k
            match finalMemo[k]? with
            | some (.done indSched) =>
              if indSched.alreadyExists then
                orderItems := orderItems.push (.element "div" #[("style", json% {"marginBottom": "2px"})] #[
                  .text "● ", mkSpan singletonStyle (k.prettyPrint numArgs),
                  mkSpan scoreStyle " (pre-existing)"
                ])
              else
                let timeStr := if indSched.derivationTimeUs >= 1000 then s!" {indSched.derivationTimeUs / 1000}ms"
                  else if indSched.derivationTimeUs > 0 then s!" {indSched.derivationTimeUs}μs" else ""
                let nCtors := indSched.baseSchedules.length + indSched.recSchedules.length
                let ctorItems := mkCtorItems indSched
                let specNameStyle := json% {"color": $(specColor indSched), "fontWeight": "bold"}
                let indScoreStr := bundle.reprScore indSched.score
                orderItems := orderItems.push (Html.element "details" #[] #[
                  .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                    .text "● ",
                    mkSpan specNameStyle (k.prettyPrint numArgs),
                    mkSpan scoreStyle s!" ({nCtors} ctors{timeStr}) score: {indScoreStr}"
                  ],
                  .element "div" #[("style", json% {"marginLeft": "12px"})] ctorItems
                ])
            | _ => pure ()
        htmlChildren := htmlChildren.push (Html.element "details" #[("open", json% true)] #[
          .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginBottom": "6px"})] #[
            .text "📋 Derived Specs (topological order)"
          ],
          .element "div" #[("style", json% {"marginLeft": "8px"})] orderItems
        ])
        -- Dependency graph with clickable constructors showing schedules
        if totalEdges > 0 then
          let getCtorSchedule (specKey : SpecKey) (ctorName : String) : String :=
            match finalMemo[specKey]? with
            | some (.done indSched) =>
              let allScheds := indSched.baseSchedules ++ indSched.recSchedules
              match allScheds.find? (fun (n, _) => n.getString! == ctorName) with
              | some (_, schedule) => ppSchedule schedule
              | none => "(schedule not found)"
            | _ => "(not derived)"
          -- Build graph section
          let mut graphItems : Array Html := #[]
          for k in usedKeys.toList do
            let nArgs ← getNumArgs k
            let label := k.prettyPrint nArgs
            match finalMemo[k]? with
            | some (.done indSched) =>
              let allScheds := indSched.baseSchedules ++ indSched.recSchedules
              let mut depCtors : Std.HashMap SpecKey (List Name) := {}
              for (ctorName, (steps, _)) in allScheds do
                let deps := collectNonRecDeps steps
                let relDeps := deps.filter (fun d => d.kind == .relation || d.kind == .checker)
                for d in relDeps do
                  let dk := SpecKey.mk d.inductiveName d.outputIndices d.deriveSort
                  if usedKeys.contains dk then
                    let existing := depCtors.getD dk []
                    if ctorName ∉ existing then
                      depCtors := depCtors.insert dk (existing ++ [ctorName])
              if !depCtors.isEmpty then
                let mut dstItems : Array Html := #[]
                for (dk, ctors) in depCtors.toList do
                  let dkArgs ← getNumArgs dk
                  -- Each constructor is a clickable details showing its schedule
                  let ctorElements ← ctors.toArray.mapM fun ctorName => do
                    let schedText := getCtorSchedule k ctorName.getString!
                    pure (Html.element "details" #[("style", json% {"display": "inline"})] #[
                      .element "summary" #[("style", json% {"cursor": "pointer", "display": "inline", "color": "#4ec9b0"})] #[
                        .text ctorName.getString!
                      ],
                      .element "div" #[("style", json% {"marginLeft": "24px", "marginBottom": "4px", "padding": "4px 8px", "background": "#1e1e1e", "borderRadius": "4px", "border": "1px solid #3c3c3c"})] #[
                        mkSpan schedStyle schedText
                      ]
                    ])
                  let ctorSep := ctorElements.foldl (init := (#[] : Array Html)) fun acc el =>
                    if acc.isEmpty then #[el] else acc ++ #[.text ", ", el]
                  dstItems := dstItems.push (.element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "3px"})] #[
                    mkSpan reqStyle "requires ",
                    mkSpan dstStyle (dk.prettyPrint dkArgs),
                    .text "  via ",
                    .element "span" #[] ctorSep
                  ])
                graphItems := graphItems.push (.element "details" #[] #[
                  .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                    mkSpan srcStyle label,
                    mkSpan (json% {"color": "#808080"}) s!" ({depCtors.size} deps)"
                  ],
                  .element "div" #[] dstItems
                ])
            | _ => pure ()
          htmlChildren := htmlChildren.push (Html.element "details" #[] #[
            .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginTop": "12px", "marginBottom": "6px"})] #[
              .text s!"📊 Dependency Graph ({totalEdges} edges)"
            ],
            .element "div" #[("style", json% {"marginLeft": "8px", "borderLeft": "2px solid #3c3c3c", "paddingLeft": "12px"})] graphItems
          ])
        -- Pattern coverage trie leaves (collapsible per inductive)
        let mut trieItems : Array Html := #[]
        for k in usedKeys.toList do
          match finalMemo[k]? with
          | some (.done indSched) =>
            if indSched.alreadyExists then pure ()
            else
              let nArgs ← getNumArgs k
              let leaves ← liftTermElabM do
                let indInfo ← getConstInfoInduct k.inductiveName
                let mut patterns : List (Name × PatternCoverage.CovPattern) := []
                for ctorName in indInfo.ctors do
                  let ctorInfo ← getConstInfoCtor ctorName
                  let pat ← forallTelescopeReducing ctorInfo.type fun _ conclusion => do
                    PatternCoverage.conclusionToCovPattern k.inductiveName conclusion k.outputIndices indInfo.numParams
                  patterns := patterns ++ [(ctorName, pat)]
                let numAllArgs := indInfo.numParams + indInfo.numIndices
                let initChildren := (List.range numAllArgs).map fun i =>
                  if i ∈ k.outputIndices then PatternCoverage.CovPattern.output else .wild
                let initPat := PatternCoverage.CovPattern.ctr k.inductiveName initChildren
                let tree ← PatternCoverage.coverPatterns patterns initPat
                return PatternCoverage.collectLeaves tree
              let ctorScores : List (Name × Score) := indSched.ctorStats.map fun (name, _, _, score) => (name, score)
              let mut leafHtmls : Array Html := #[]
              for (pat, rules) in leaves do
                let covering : List (Name × Score) := rules.filterMap fun r =>
                  ctorScores.find? (fun x => x.1 == r)
                let leafScore := bundle.leafAggregator covering
                let patStr := PatternCoverage.ppCovPattern pat
                let leafColor := scoreToColor leafScore
                if covering.isEmpty then
                  leafHtmls := leafHtmls.push (.element "div" #[("style", json% {"marginLeft": "8px", "marginBottom": "4px"})] #[
                    mkSpan (json% {"color": "hsl(0, 70%, 60%)"}) s!"{patStr}",
                    .element "br" #[] #[],
                    mkSpan (json% {"color": "hsl(0, 50%, 50%)", "marginLeft": "16px"}) "UNCOVERED"
                  ])
                else
                  let ctorItems : Array Html := covering.toArray.map fun (r, s) =>
                    let shortName := (r.componentsRev.head?.getD r).toString
                    let ctorColor := scoreToColor s
                    Html.element "div" #[("style", json% {"marginLeft": "16px"})] #[
                      mkSpan (json% {"color": $(ctorColor)}) s!"{shortName}: {bundle.reprScore s}"
                    ]
                  let aggregateHtml := Html.element "div" #[("style", json% {"marginLeft": "16px", "fontStyle": "italic"})] #[
                    mkSpan (json% {"color": $(leafColor)}) s!"aggregates to: {bundle.reprScore leafScore}"
                  ]
                  leafHtmls := leafHtmls.push (.element "div" #[("style", json% {"marginLeft": "8px", "marginBottom": "6px"})] (
                    #[mkSpan (json% {"color": $(leafColor), "fontWeight": "bold"}) patStr] ++
                    ctorItems ++
                    #[aggregateHtml]
                  ))
              let indScoreStr := bundle.reprScore indSched.score
              trieItems := trieItems.push (Html.element "details" #[] #[
                .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                  mkSpan (json% {"color": $(specColor indSched), "fontWeight": "bold"}) (k.prettyPrint nArgs),
                  mkSpan scoreStyle s!" ({leaves.length} leaves, score: {indScoreStr})"
                ],
                .element "div" #[("style", json% {"marginLeft": "12px", "padding": "4px 0", "fontSize": "0.9em", "fontFamily": "var(--vscode-editor-font-family, monospace)"})] leafHtmls
              ])
          | _ => pure ()
        if !trieItems.isEmpty then
          htmlChildren := htmlChildren.push (Html.element "details" #[] #[
            .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginTop": "12px", "marginBottom": "6px"})] #[
              .text s!"🌲 Pattern Coverage ({trieItems.size} inductives)"
            ],
            .element "div" #[("style", json% {"marginLeft": "8px", "borderLeft": "2px solid #3c3c3c", "paddingLeft": "12px"})] trieItems
          ])
        -- Emit the full HTML (if richOutput enabled)
        if richOutput then
          let fullHtml := Html.element "div" #[("style", json% {"fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "13px", "lineHeight": "1.6", "padding": "8px"})] htmlChildren
          let graphMsg ← liftCoreM <| Lean.MessageData.ofHtml fullHtml
            s!"derive_mutual: {usedKeys.size} specs in {components.length} components"
          logInfo graphMsg
        -- Plain-text output (accessible to LLMs and non-IDE tooling)
        -- Levels: 0=off, 1=names+quality, 2=full schedules for poor-quality, 3=everything
        let textLevel := Lean.Option.get (← getOptions) specimen.textOutput
        if textLevel > 0 then
          let specQuality (indSched : InductiveSchedule) : String :=
            let b := bundle.scoreBadness indSched.score
            if b ≤ 0.2 then "★★★"
            else if b ≤ 0.5 then "★★☆"
            else if b ≤ 0.8 then "★☆☆"
            else "☆☆☆"
          let showSchedules (indSched : InductiveSchedule) : Bool :=
            textLevel ≥ 3 || (textLevel ≥ 2 && bundle.scoreBadness indSched.score > 0.5)
          let mut lines : Array String := #[]
          lines := lines.push s!"⚙ derive_mutual — {usedKeys.size} specs, {components.length} components"
          lines := lines.push ""
          lines := lines.push "── Derived Specs (topological order) ──"
          for comp in components do
            if comp.length > 1 then
              lines := lines.push s!"  ◆ mutual ({comp.length}):"
              for k in comp do
                let numArgs ← getNumArgs k
                match finalMemo[k]? with
                | some (.done indSched) =>
                  let nCtors := indSched.baseSchedules.length + indSched.recSchedules.length
                  lines := lines.push s!"    {specQuality indSched} {k.prettyPrint numArgs} ({nCtors} ctors) [{bundle.reprScore indSched.score}]"
                  if showSchedules indSched then
                    let allScheds := indSched.baseSchedules ++ indSched.recSchedules
                    for (ctorName, schedule) in allScheds do
                      let isBase := indSched.baseSchedules.any (fun (n, _) => n == ctorName)
                      let tag := if isBase then "base" else "rec"
                      let ctorScore := match indSched.ctorStats.find? (fun (n, _, _, _) => n == ctorName) with
                        | some (_, _, _, s) => bundle.reprScore s
                        | none => "?"
                      lines := lines.push s!"      {ctorName.getString!} [{tag}] {ctorScore}"
                      lines := lines.push s!"        {ppSchedule schedule}"
                | _ => pure ()
            else
              let k := comp.head!
              let numArgs ← getNumArgs k
              match finalMemo[k]? with
              | some (.done indSched) =>
                if indSched.alreadyExists then
                  lines := lines.push s!"  ● {k.prettyPrint numArgs} (pre-existing)"
                else
                  let nCtors := indSched.baseSchedules.length + indSched.recSchedules.length
                  lines := lines.push s!"  ● {specQuality indSched} {k.prettyPrint numArgs} ({nCtors} ctors) [{bundle.reprScore indSched.score}]"
                  if showSchedules indSched then
                    let allScheds := indSched.baseSchedules ++ indSched.recSchedules
                    for (ctorName, schedule) in allScheds do
                      let isBase := indSched.baseSchedules.any (fun (n, _) => n == ctorName)
                      let tag := if isBase then "base" else "rec"
                      let ctorScore := match indSched.ctorStats.find? (fun (n, _, _, _) => n == ctorName) with
                        | some (_, _, _, s) => bundle.reprScore s
                        | none => "?"
                      lines := lines.push s!"      {ctorName.getString!} [{tag}] {ctorScore}"
                      lines := lines.push s!"        {ppSchedule schedule}"
              | _ => pure ()
          if textLevel ≥ 2 && totalEdges > 0 then
            lines := lines.push ""
            lines := lines.push s!"── Dependency Graph ({totalEdges} edges) ──"
            for k in usedKeys.toList do
              let nArgs ← getNumArgs k
              let label := k.prettyPrint nArgs
              match finalMemo[k]? with
              | some (.done indSched) =>
                let allScheds := indSched.baseSchedules ++ indSched.recSchedules
                let mut depCtors : Std.HashMap SpecKey (List Name) := {}
                for (ctorName, (steps, _)) in allScheds do
                  let deps := collectNonRecDeps steps
                  let relDeps := deps.filter (fun d => d.kind == .relation || d.kind == .checker)
                  for d in relDeps do
                    let dk := SpecKey.mk d.inductiveName d.outputIndices d.deriveSort
                    if usedKeys.contains dk then
                      let existing := depCtors.getD dk []
                      if ctorName ∉ existing then
                        depCtors := depCtors.insert dk (existing ++ [ctorName])
                if !depCtors.isEmpty then
                  lines := lines.push s!"  {label} ({depCtors.size} deps)"
                  for (dk, ctors) in depCtors.toList do
                    let dkArgs ← getNumArgs dk
                    let ctorStrs := ctors.map (fun n => n.getString!)
                    lines := lines.push s!"    requires {dk.prettyPrint dkArgs}  via {String.intercalate ", " ctorStrs}"
              | _ => pure ()
          logInfo m!"{String.intercalate "\n" lines.toList}"
        -- For each component: assign names, compile, emit
        for comp in components do
          -- Assign global names for this component
          let mut compMeta : Array (SpecKey × Name) := #[]
          for key in comp do
            let uid ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_mutual)
            let globalName := Name.mkSimple s!"{uid}_{key.inductiveName.toString.replace "." "_"}"
            compMeta := compMeta.push (key, globalName)
          -- Build siblings list for this component (for MutRec rewriting)
          let compSiblings : List (Name × List Nat × Name × DeriveSort) :=
            compMeta.toList.map (fun (k, gn) => (k.inductiveName, k.outputIndices, gn, k.deriveSort))
          -- Compile each spec in the component
          let mut defCmds : Array (TSyntax `command) := #[]
          let mut instCmds : Array (TSyntax `command) := #[]
          for (key, globalName) in compMeta do
            match finalMemo[key]? with
            | some (.done indSched) =>
              if indSched.alreadyExists then continue
              try
                let (defCmd, instCmd) ← liftTermElabM <|
                  compileInductiveSchedule indSched globalName compSiblings
                defCmds := defCmds.push defCmd
                instCmds := instCmds.push instCmd
              catch e =>
                logWarning m!"Failed to compile {key.inductiveName}{key.outputIndices}{repr key.deriveSort}: {e.toMessageData}"
            | _ => logWarning m!"No schedule found for {key.inductiveName}{key.outputIndices}"
          let getNumArgs (k : SpecKey) : CommandElabM Nat := liftTermElabM do
            try pure ((← getComponentsOfArrowType (← getConstInfoInduct k.inductiveName).type).size - 1)
            catch _ => pure k.outputIndices.length
          -- Emit: mutual block for multi-element, standalone for singletons
          let specDescs ← compMeta.toList.mapM fun (k, _) => do
            let numArgs ← getNumArgs k
            let scoreStr := match finalMemo[k]? with
              | some (.done indSched) =>
                if indSched.alreadyExists then "(pre-existing)"
                else s!"({indSched.baseSchedules.length} base, {indSched.recSchedules.length} rec)"
              | _ => ""
            pure s!"{k.prettyPrint numArgs} {scoreStr}"
          if defCmds.size > 1 then
            logInfo m!"  ◆ mutual ({defCmds.size}):\n    {String.intercalate "\n    " specDescs}"
            let mutualCmd ← `(command| mutual $defCmds* end)
            elabCommand mutualCmd
          else if defCmds.size == 1 then
            logInfo m!"  ● {specDescs.head!}"
            elabCommand defCmds[0]!
          for instCmd in instCmds do
            elabCommand instCmd
      else
        -- Fallback: no auto-derive, use old per-entry compilation
        let siblings := specMeta.toList
        let mut defCmds : Array (TSyntax `command) := #[]
        let mut instCmds : Array (TSyntax `command) := #[]
        for i in [:specEntries.size] do
          let rawEntry := specEntries[i]!
          -- Extract term from mutualEntry syntax (skip optional keyword)
          let termStx : TSyntax `term := Id.run do
            let children := rawEntry.raw.getArgs
            if children.size >= 2 then ⟨children[1]!⟩ else ⟨rawEntry.raw⟩
          let (_, _, globalName, _) := specMeta[i]!
          let rewriter := fun steps => rewriteMutualCalls steps siblings
          let (defCmd, instCmd) ← liftTermElabM do
            let e ← elabTerm termStx .none
            withParsedDerivingArgs e fun args outVars outTypes indName indLevels indArgs => do
              let parts ← deriveConstrainedProducerParts args outVars outTypes indName indLevels indArgs .Generator rewriter (some globalName)
              let (baseProducers, inductiveProducers, freshenedOutputNames, freshArgIdents, outputTypes, localCtx, _, inductiveLevels, producerSort) := parts
              mkConstrainedProducerMutualPieces baseProducers inductiveProducers
                indName inductiveLevels freshArgIdents freshenedOutputNames.toList
                outputTypes.toList producerSort localCtx globalName .Generator
          defCmds := defCmds.push defCmd
          instCmds := instCmds.push instCmd
        let mutualCmd ← `(command| mutual $defCmds* end)
        elabCommand mutualCmd
        for instCmd in instCmds do
          elabCommand instCmd
  | _ => throwUnsupportedSyntax
