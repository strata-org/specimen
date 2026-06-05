import Lean

import Specimen.MakeConstrainedProducerInstance
import Specimen.DeriveConstrainedProducer
import Specimen.Idents
import Specimen.DecOpt
import Specimen.UnificationMonad

open Lean Std Elab Command Meta Term Parser
open Idents Schedules



/-- Unifies each argument in the conclusion of an inductive relation with the top-level arguments to the relation
    (using the unification algorithm from Generating Good Generations),
    and subsequently computes a *naive* checker schedule for a sub-checker corresponding to the constructor
    (using the schedules discussed in Testing Theorems).

    Note: this function processes the entire type of the constructor within the same `LocalContext`
    (the one produced by `forallTelescopeReducing`).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The names of inputs `inputNames` (arguments to the checker, i.e. all arguments to the inductive relation) -/
def getCheckerScheduleForInductiveConstructor (inductiveName : Name) (ctorName : Name) (inputNames : List Name) (localCtx : LocalContext) (recFnName : Name := `aux_dec) : UnifyM Schedule :=
  getScheduleForInductiveRelationConstructor inductiveName ctorName inputNames (deriveSort := .Checker) none #[] localCtx recFnName


/-- Produces an instance of the `DecOpt` typeclass containing the definition for the top-level derived checker.
    The arguments to this function are:
    - a list of `baseCheckers` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveCheckers`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation

    - Note: this function is identical to `mkTopLevelChecker`, except it doesn't take in a `NameMap` argument
    - TODO: refactor to avoid code duplication -/
def mkDecOptInstance (baseCheckers : TSyntax `term) (inductiveCheckers : TSyntax `term)
  (inductiveName : Name) (inductiveLevels : List Level) (args : TSyntaxArray `term) (topLevelLocalCtx : LocalContext) : TermElabM (TSyntax `command) := do

  -- Produce fresh names for function parameters
  let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
  let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'
  let freshFuel' := mkFreshAccessibleIdent topLevelLocalCtx `fuel'
  let auxDecIdent := mkFreshAccessibleIdent topLevelLocalCtx `aux_dec
  let checkerType ← `($exceptTypeConstructor $genErrorType $boolIdent)

  -- Create the inner match on size
  let mut sizeCaseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $checkerBacktrackFn $baseCheckers)
  sizeCaseExprs := sizeCaseExprs.push zeroCase
  let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $checkerBacktrackFn $inductiveCheckers)
  sizeCaseExprs := sizeCaseExprs.push succCase
  let sizeMatchExpr ← mkMatchExpr sizeIdent sizeCaseExprs

  -- Wrap with outer fuel match
  let mut fuelCaseExprs := #[]
  let fuelZeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $failFn $outOfFuelError)
  fuelCaseExprs := fuelCaseExprs.push fuelZeroCase
  let fuelSuccCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshFuel' => $sizeMatchExpr)
  fuelCaseExprs := fuelCaseExprs.push fuelSuccCase
  let matchExpr ← mkMatchExpr fuelIdent fuelCaseExprs

  -- Create function arguments for the checker's `fuel`, `initSize` & `size` parameters
  let fuelParam ← `(Term.letIdBinder| ($fuelIdent : $natIdent))
  let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))

  -- Add parameters for each argument to the inductive relation
  let paramInfo ← analyzeInductiveArgs inductiveName inductiveLevels args

  -- Inner params are for the inner `aux_dec` function
  let mut innerParams := #[]
  innerParams := innerParams.push fuelParam
  innerParams := innerParams.push initSizeParam
  innerParams := innerParams.push sizeParam

  -- Outer params are for the top-level lambda function which invokes `aux_dec`
  let mut outerParams := #[]
  let mut typeParams := #[]
  for (paramName, paramType, paramTypeSyntax) in paramInfo do
    let outerParamIdent := mkIdent paramName
    outerParams := outerParams.push outerParamIdent

    if paramType.isSort then typeParams := typeParams.push paramName

    -- Inner parameters are for the inner `aux_arb` function
    let innerParam ←
    if paramType.isSort then
     `(Term.letIdBinder| ($(mkIdent paramName) : _))
    else
     `(Term.letIdBinder| ($(mkIdent paramName) : $paramTypeSyntax))
    innerParams := innerParams.push innerParam

  let arbitraryTypeParamInstances ← mkTypeClassInstanceBinders typeParams #[``Enum, ``DecidableEq]

  -- Produces an instance of the `DecOpt` typeclass containing the definition for the derived generator
  let fuelVal := Lean.Option.get (← getOptions) specimen.fuel
  let fuelLit := Syntax.mkNumLit (toString fuelVal)
  `(instance $arbitraryTypeParamInstances:bracketedBinder* : $decOptTypeclass (@$(mkIdent inductiveName) $args*) where
      $unqualifiedDecOptFn:ident :=
        let rec $auxDecIdent:ident $innerParams* $arbitraryTypeParamInstances:bracketedBinder* : $checkerType :=
          $matchExpr
        fun $freshSizeIdent => $auxDecIdent $fuelLit $freshSizeIdent $freshSizeIdent $outerParams*)


def deriveScheduledChecker' (_args : Array Expr)
    (constrInd : Name)
    (constrLevels : List Level)
    (constrArgs : Array Expr) : TermElabM (TSyntax `command) := do
  -- Parse `inductiveProp` for an application of the inductive relation

  let inductiveName := constrInd

  -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
  let inductiveVal ← getConstInfoInduct inductiveName

  -- Determine the type for each argument to the inductive
  let inductiveTypeComponents ← getComponentsOfArrowType inductiveVal.type

  -- To obtain the type of each arg to the inductive,
  -- we pop the last element (`Prop`) from `inductiveTypeComponents`
  let argTypes := inductiveTypeComponents.pop
  -- For now we fail if any argument is not a variable
  let argNames ← constrArgs.mapM
    (fun ident : Expr =>
      if ident.isFVar then
        ident.fvarId!.getUserName
      else throwError m!"{ident} is expected to be a variable.")
  let argNamesTypes := argNames.zip argTypes

  -- Add the name & type of each argument to the inductive relation to the `LocalContext`
  -- Then, derive `baseProducers` & `inductiveProducers` (the code for the sub-producers
  -- that are invoked when `size = 0` and `size > 0` respectively),
  -- and obtain freshened versions of the output variable / arguments (`freshenedOutputName`, `freshArgIdents`)
  let (baseCheckers, inductiveCheckers, freshArgIdents, localCtx) ←
    withLocalDeclsDND argNamesTypes (fun _ => do
      let mut localCtx ← getLCtx
      let mut freshUnknowns := #[]

      -- For each arg to the inductive relation (as specified to the user),
      -- create a fresh name (to avoid clashing with names that may appear in constructors
      -- of the inductive relation). Note that this requires updating the `LocalContext`.
      for argName in argNames do
        let freshArgName := localCtx.getUnusedName argName
        localCtx := localCtx.renameUserName argName freshArgName
        freshUnknowns := freshUnknowns.push freshArgName

      let mut nonRecursiveCheckers := #[]
      let mut recursiveCheckers := #[]
      let mut requiredInstances := #[]

      -- Compute the freshened names for `aux_dec` and `size'` early,
      -- so they can be threaded through schedule derivation and MExp compilation.
      -- These must match the names used by `mkDecOptInstance`.
      let freshAuxDecName := localCtx.getUnusedName `aux_dec
      let freshFuelPrimeName := localCtx.getUnusedName `fuel'
      let freshSizePrimeName := localCtx.getUnusedName `size'

      for ctorName in inductiveVal.ctors do
        let scheduleOption ← (UnifyM.runUnifyM
          (getCheckerScheduleForInductiveConstructor inductiveName ctorName freshUnknowns.toList localCtx freshAuxDecName)
            emptyUnifyState)
        match scheduleOption with
        | some (schedule, unifyState) =>
          -- Obtain a sub-checker for this constructor, along with an array of all typeclass instances that need to be defined beforehand.
          -- (Under the hood, we compile the schedule to an `MExp`, then compile the `MExp` to a Lean term containing the code for the sub-producer.
          -- This is all done in a state monad: when we detect that a new instance is required, we append it to an array of `TSyntax term`s
          -- (where each term represents a typeclass instance)
          let (subChecker, instances) ← StateT.run (s := #[]) (do
            let recType := unifyState.outputTypes.headD (mkConst ``Bool)
            let mexp ← MExp.scheduleToMExp schedule (.MId `size) (.MId `initSize) recType (fuelPrimeName := freshFuelPrimeName) (sizePrimeName := freshSizePrimeName)
            MExp.mexpToTSyntax mexp (deriveSort := .Checker))

          requiredInstances := requiredInstances ++ instances

          -- Determine whether the constructor is recursive
          -- (i.e. if the constructor has a hypothesis that refers to the inductive relation we are targeting)
          let isRecursive ← isConstructorRecursive inductiveName ctorName

          let unitIdent := Lean.mkIdent ``Unit
          -- Sub-checkers need to be thunked, since we don't want the `checkerBacktrack` combinator
          -- (which expects a list of sub-checkers as inputs) to evaluate all the sub-checkers eagerly
          let thunkedSubChecker ← `(fun (_ : $unitIdent) => $subChecker)

          if isRecursive then
            recursiveCheckers := recursiveCheckers.push thunkedSubChecker
          else
            nonRecursiveCheckers := nonRecursiveCheckers.push thunkedSubChecker

        | none => throwError m!"Unable to derive producer schedule for constructor {ctorName}"

      if (not requiredInstances.isEmpty) then
        let deduplicatedInstances := List.eraseDups requiredInstances.toList
        trace[plausible.deriving.arbitrary] m!"Required typeclass instances (please derive these first if they aren't already defined):\n{deduplicatedInstances}"

      -- Collect all the base / inductive checkers into two Lean list terms
      -- Base checkers are invoked when `size = 0`, inductive checkers are invoked when `size > 0`
      let baseCheckers ← `([$nonRecursiveCheckers,*])
      let inductiveCheckers ← `([$nonRecursiveCheckers,*, $recursiveCheckers,*])

      return (baseCheckers, inductiveCheckers, Lean.mkIdent <$> freshUnknowns, localCtx))

  -- Create an instance of the `DecOpt` typeclass
  mkDecOptInstance
    baseCheckers
    inductiveCheckers
    constrInd
    constrLevels
    freshArgIdents
    localCtx

private def withParsedDerivingArgs (input : Expr)
  (action :
    (args : Array Expr) →
    (constrInd : Name) → (constrLevels : List Level) → (constrArgs : Array Expr) → TermElabM α) : TermElabM α :=
  lambdaTelescope input <|
  fun args body => do
  let body ← whnf body
  body.withApp <|
  fun ind indArgs => do
  if !ind.isConst then throwError m!"Error in parsing constraint: {ind} is expected to be a constant."
  let indName := ind.constName!
  let indLevels := ind.constLevels!
  action args indName indLevels indArgs

/-- Derives a checker which checks the `inductiveProp` (an inductive relation, represented as a `TSyntax term`)
    using the unification algorithm from Generating Good Generators and the schedules discuseed in Testing Theorems -/
def deriveScheduledChecker (inductiveProp : TSyntax `term) : TermElabM (TSyntax `command) := do
  let elabTm ← elabTerm inductiveProp .none
  withParsedDerivingArgs elabTm deriveScheduledChecker'

----------------------------------------------------------------------
-- NEW Command elaborator driver
-----------------------------------------------------------------------

/-- Command which derives a checker using the new schedule and unification-based algorithm -/
syntax (name := checker_deriver) "derive_checker" term : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab checker_deriver]
def elabDeriveScheduledChecker : CommandElab := fun stx => do
  match stx with
  | `(derive_checker $indProp:term) => do

    -- Produce an instance of the `DecOpt` typeclass corresponding to the inductive proposition `indProp`
    let typeclassInstance ← liftTermElabM <| deriveScheduledChecker indProp

    -- Pretty-print the derived checker
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived checker to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this checker: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
