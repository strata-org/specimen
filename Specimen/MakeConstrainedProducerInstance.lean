import Lean
import Std
import Plausible.Gen
import Specimen.Enumerators
import Specimen.GeneratorCombinators
import Specimen.TSyntaxCombinators
import Specimen.Idents
import Specimen.Utils
import Specimen.Schedules
import Specimen.Debug

open Lean Elab Command Meta Term Parser Std
open Idents Schedules


/-- The class a derived producer's unconstrained values, and its type parameters, are drawn through:
    under Basalt `Basalt.ArbitrarySized` for a generator and an enumerator alike, finite at a size;
    otherwise Plausible's `Arbitrary` and Specimen's `Enum`. -/
def basaltUnconstrainedClass (useBasalt : Bool) : ProducerSort → Name
  | .Generator => if useBasalt then Name.mkStr2 "Basalt" "ArbitrarySized" else ``Plausible.Arbitrary
  | .Enumerator => if useBasalt then Name.mkStr2 "Basalt" "ArbitrarySized" else ``Enum

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) :
  TermElabM (TSyntax `ident × TSyntaxArray `ident) := do
  match body with
  | `($indRel:ident $args:ident*) => do
    return (indRel, args)
  | `($indRel:ident) => do
    return (indRel, #[])
  | _ => throwErrorAt body "Expected inductive type application"

/-- Instantiates a known-to-be well-typed call to inductive with array of arguments `es` one
    at a time and infers each arguments type, so renamings and dependent types are supported.
    Returns the array of types for each argument in `es`. -/
def getCorrectTypes (es : Array Expr) (ind : Name) (inductiveLevels : List Level) : TermElabM (Array Expr) := do
  trace[plausible.deriving.arbitrary] m!"Levels for inductive {ind}: {inductiveLevels}"
  let mut t : Expr := .const ind inductiveLevels
  let mut tys : Array Expr := #[]
  for e in es do
    tys := tys.push (← inferType t).bindingDomain!
    t := .app t e
  let resolvedExpr ← instantiateMVars t
  trace[plausible.deriving.arbitrary] m!"Resolved mvar type: {t} {resolvedExpr}"
  return tys

/-- Analyzes the type of the inductive relation and matches each
    argument with its expected type, returning an array of
    (parameter name, type expression) pairs -/
def analyzeInductiveArgs (inductiveName : Name) (inductiveLevels : List Level) (args : Array Term) :
  TermElabM (Array (Name × Expr × TSyntax `term)) := do
  let argNames ← monadLift <| args.mapM extractParamName
  let types ← getCorrectTypes (argNames.map (mkFVar ⟨·⟩)) inductiveName inductiveLevels
  let typesSyntax ← monadLift <| types.mapM PrettyPrinter.delab
  trace[plausible.deriving.arbitrary] m!"Types for inductive args: {typesSyntax}"
  return argNames.zip (types.zip typesSyntax)

def mkTypeClassInstanceBinders (typeParams : Array Name) (typeClasses : Array Name) : TermElabM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  let instances ← typeParams.flatMapM fun param =>
    typeClasses.mapM fun tc =>
      `(Lean.Elab.Deriving.instBinderF| [$(mkIdent tc) $(mkIdent param)])
  return TSyntaxArray.mk instances

/-- Finds the index of the argument in the inductive application for the value we wish to generate
    (i.e. finds `i` s.t. `args[i] == targetVar`) -/
def findTargetVarIndex (targetVar : FVarId) (args : Array Expr) : (Option Nat) := do
  for i in [:args.size] do
    let arg := args[i]!
    if arg.isFVar then
      let varName := arg.fvarId!
      if varName == targetVar then
        return i
  none


/-- Under `specimen.emitBasalt` the emitted code names Basalt's classes, which resolve only in a file
    that imports `Specimen.Basalt` (the deriver itself does not import Basalt). Checked before emitting
    anything, so a missing import is reported as such rather than as an unknown identifier somewhere
    inside the generated code. -/
def requireBasaltImport : CoreM Unit := do
  unless ((← getEnv).getModuleIdx? `Specimen.BasaltBridge).isSome do
    throwError "`specimen.emitBasalt` requires `import Specimen.Basalt` in this file: derived \
      generators are emitted against Basalt's `Gen`, `Fail`, `FailWith` and `Backtrack`"

/-- Whether `stx` contains the identifier `x`, ignoring macro scopes. -/
private def mentionsIdent (x : Name) (stx : Syntax) : Bool :=
  (stx.find? fun s => s.isIdent && s.getId.eraseMacroScopes == x.eraseMacroScopes).isSome

/-- Produces an instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass containing the definition for a constrained generator.
    The arguments to this function are:
    - a list of `baseGenerators` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveGenerators`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveName`)
    - the arguments (`args`) to the inductive relation
    - the names and types for the values we wish to generate (`targetVars`, `targetTypes`)
      + For multiple outputs, the instance is created for the product type
    - the `producerSort`, which determines what typeclass is to be produced
      + If `producerSort = .Generator`, an `ArbitrarySizedSuchThat` instance is produced
      + If `producerSort = .Enumerator`, an `EnumSizedSuchThat` instance is produced
    - The `LocalContext` associated with the top-level inductive relation (`topLevelLocalCtx`) -/
def mkConstrainedProducerTypeClassInstance
  (baseGenerators : TSyntax `term)
  (inductiveGenerators : TSyntax `term)
  (inductiveName : Name)
  (inductiveLevels : List Level)
  (args : TSyntaxArray `term) (targetVars : List Name)
  (targetTypes : List Expr)
  (producerSort : ProducerSort)
  (topLevelLocalCtx : LocalContext) : TermElabM (TSyntax `command) := do
    -- Produce fresh names for function parameters
    let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
    let freshLeafSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `leafSize
    let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'
    let freshFuel' := mkFreshAccessibleIdent topLevelLocalCtx `fuel'

    -- Whether to target Basalt's generator algebra (generators only; see `specimen.emitBasalt`).
    let emitBasalt := Lean.Option.get (← getOptions) specimen.emitBasalt
    let useBasalt := emitBasalt && (producerSort matches .Generator || producerSort matches .Enumerator)
    if useBasalt then requireBasaltImport

    -- The (backtracking) combinator to be invoked
    let combinatorFn :=
      if useBasalt then basaltBacktrackFn
      else match producerSort with
      | .Generator => genBacktrackFn
      | .Enumerator => enumerateFn

    -- Create the inner match on size (base vs recursive constructors)
    let mut sizeCaseExprs := #[]
    let zeroCase ← `(Term.matchAltExpr|
      | $(mkIdent ``Nat.zero) => $combinatorFn $baseGenerators)
    sizeCaseExprs := sizeCaseExprs.push zeroCase

    let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $combinatorFn $inductiveGenerators)
    sizeCaseExprs := sizeCaseExprs.push succCase

    let sizeMatchExpr ← mkMatchExpr sizeIdent sizeCaseExprs

    -- Wrap with outer fuel match for termination
    let mut fuelCaseExprs := #[]
    -- Running out of the termination counter is *inconclusive*, not a refutation: nothing was
    -- determined. Under Basalt that is a distinct constructor rather than an error message that a
    -- downstream string-matching predicate has to recognise.
    let fuelZeroCase ←
      if useBasalt then `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $backtrackGenExhaustFn)
      else `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $failFn $outOfFuelError)
    fuelCaseExprs := fuelCaseExprs.push fuelZeroCase
    let fuelSuccCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshFuel' => $sizeMatchExpr)
    fuelCaseExprs := fuelCaseExprs.push fuelSuccCase
    let matchExpr ← mkMatchExpr fuelIdent fuelCaseExprs

    -- Create function arguments for the producer's `fuel`, `initSize` & `size` parameters
    let fuelParam ← `(Term.letIdBinder| ($fuelIdent : $natIdent))
    let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
    let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))

    -- Add parameters for each argument to the inductive relation
    -- (except the target variables, which we'll filter out later)
    let paramInfo ← analyzeInductiveArgs inductiveName inductiveLevels args

    let targetVarsList := targetVars

    -- Inner params are for the inner `aux_arb` / `aux_enum` function
    let mut innerParams := #[]
    innerParams := innerParams.push fuelParam
    innerParams := innerParams.push initSizeParam
    innerParams := innerParams.push sizeParam

    -- Outer params are for the top-level lambda function which invokes `aux_arb` / `aux_enum`
    let mut outerParams := #[]
    let mut outputTypeSyntaxes : Array (TSyntax `term) := #[]
    let mut typeParams := #[]
    for (paramName, paramType, paramTypeSyntax) in paramInfo do
      -- Only add a function parameter if the argument to the inductive relation is not a target variable
      -- (We skip the target variables since those are the values we wish to generate)
      if paramType.isSort then
        typeParams := typeParams.push paramName
      if paramName ∉ targetVarsList then
        let outerParamIdent := mkIdent paramName
        outerParams := outerParams.push outerParamIdent

        let innerParamIdent := mkIdent paramName

        let innerParam ← if paramType.isSort then
          `(Term.letIdBinder| ($innerParamIdent : Sort _))
          else
          `(Term.letIdBinder| ($innerParamIdent : $paramTypeSyntax))

        innerParams := innerParams.push innerParam
      else
        outputTypeSyntaxes := outputTypeSyntaxes.push paramTypeSyntax

    -- Build the target type syntax — for multiple outputs, use a right-nested product type
    let targetTypeSyntax ← do
      let syns ← if outputTypeSyntaxes.isEmpty then
        targetTypes.mapM (fun ty => PrettyPrinter.delab ty)
      else pure outputTypeSyntaxes.toList
      tupleOfListM (throwError "no output types found")
        (fun t rest => `($t × $rest)) syns
    -- Build the lambda pattern for the typeclass predicate
    -- For a single output: `fun x => @P args*`
    -- For multiple outputs: `fun (x₁, (x₂, x₃)) => @P args*` (right-nested)
    let targetVarPattern : TSyntax `term ← do
      let rec mkProdPat : List Name → TermElabM (TSyntax `term)
        | [] => throwError "no output variables"
        | [v] => `($(Lean.mkIdent v))
        | v :: vs => do let rest ← mkProdPat vs; `(($(Lean.mkIdent v), $rest))
      mkProdPat targetVars

    -- Figure out which typeclass should be derived
    -- (`ArbitrarySizedSuchThat` for generators, `EnumSizedSuchThat` for enumerators)
    let producerTypeClass :=
      match producerSort with
      | .Generator => arbitrarySizedSuchThatTypeclass
      | .Enumerator => enumSizedSuchThatTypeclass

    -- Similarly, figure out the name of the function corresponding to the typeclass above
    let producerTypeClassFunction :=
      match producerSort with
      | .Generator => unqualifiedArbitrarySizedSTFn
      | .Enumerator => unqualifiedEnumSizedSTFn

    -- Generators use `aux_arb` as the inner function, enumerators use `aux_enum`
    let innerFunctionIdent :=
      match producerSort with
      | .Generator => mkFreshAccessibleIdent topLevelLocalCtx `aux_arb
      | .Enumerator => mkFreshAccessibleIdent topLevelLocalCtx `aux_enum

    -- Determine the appropriate type of the final producer
    -- (`G α` under Basalt, else `Plausible.Gen α` or `ExceptT GenError Enum α`)
    let optionTProducerType ←
      if useBasalt then
        `($basaltGenVar $targetTypeSyntax)
      else match producerSort with
      | .Generator => `($genTypeConstructor $targetTypeSyntax)
      | .Enumerator => `($exceptTTypeConstructor $genErrorType $enumTypeConstructor $targetTypeSyntax)

    let producerUnconstrainedClass := basaltUnconstrainedClass useBasalt producerSort

    let arbitraryTypeParamInstances ← mkTypeClassInstanceBinders typeParams #[producerUnconstrainedClass, ``DecidableEq]

    let fuelVal := Lean.Option.get (← getOptions) specimen.fuel
    let fuelLit := Syntax.mkNumLit (toString fuelVal)

    -- Produce an instance of the appropriate typeclass containing the definition for the derived producer
    if useBasalt then
      -- The generator monad is bound on the *inner function*, not on an enclosing lambda: `let rec`
      -- is lifted to a top-level declaration and so cannot capture an implicit binder from its
      -- surrounding scope — doing that leaves `G` as an unassigned metavariable and the lifted
      -- `aux_arb` fails the kernel with "declaration has metavariables".
      --
      -- `BacktrackGenFor.gen` is itself `∀ {G} [Gen G] [Fail G] [FailWith _ G] [Backtrack G]
      -- [MonoBacktrack G], Nat → G α`,
      -- so the field's own binders unify with the inner function's at the call below.
      let basaltBinders ← liftMacroM basaltInstBinders
      let (basaltClass, basaltField) := match producerSort with
        | .Generator => (backtrackGenForTypeclass, unqualifiedBacktrackGenForFn)
        | .Enumerator => (enumForTypeclass, unqualifiedEnumForFn)
      `(instance $arbitraryTypeParamInstances:bracketedBinder* : $basaltClass $targetTypeSyntax (fun $targetVarPattern => @$(mkIdent inductiveName) $args*) where
          $basaltField:ident :=
            let rec $innerFunctionIdent:ident {$basaltGenVar : Type → Type} $basaltBinders:bracketedBinder* $innerParams* $arbitraryTypeParamInstances:bracketedBinder* : $optionTProducerType :=
              $matchExpr
            fun $freshSizeIdent $freshLeafSizeIdent => $innerFunctionIdent $fuelLit $freshLeafSizeIdent $freshSizeIdent $outerParams*)
    else
    `(instance $arbitraryTypeParamInstances:bracketedBinder* : $producerTypeClass $targetTypeSyntax (fun $targetVarPattern => @$(mkIdent inductiveName) $args*) where
        $producerTypeClassFunction:ident :=
          let rec $innerFunctionIdent:ident $innerParams* $arbitraryTypeParamInstances:bracketedBinder* : $optionTProducerType :=
            $matchExpr
          fun $freshSizeIdent => $innerFunctionIdent $fuelLit $freshSizeIdent $freshSizeIdent $outerParams*)

/-- Like `mkConstrainedProducerTypeClassInstance` but returns the function body and metadata
    separately, for use in `mutual def` blocks.
    Returns: (matchExpr, innerParams, returnType, outerParams, instanceMetadata) -/
def mkConstrainedProducerMutualPieces
  (baseGenerators : TSyntax `term) (inductiveGenerators : TSyntax `term)
  (inductiveName : Name) (inductiveLevels : List Level)
  (args : TSyntaxArray `term) (targetVars : List Name)
  (targetTypes : List Expr) (producerSort : ProducerSort)
  (topLevelLocalCtx : LocalContext) (globalDefName : Name)
  (deriveSort : DeriveSort)
  (precomputedParamInfo : Option (Array (Name × Expr × TSyntax `term)) := none)
  (requiredTypeClasses : Option (Array Name) := none) :
  TermElabM (TSyntax `command × TSyntax `command) := do
    -- Reuse the same computation as mkConstrainedProducerTypeClassInstance
    let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
    let freshLeafSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `leafSize
    let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'
    let freshFuel' := mkFreshAccessibleIdent topLevelLocalCtx `fuel'

    -- Whether to target Basalt's generator algebra (generators only; see `specimen.emitBasalt`).
    let emitBasalt := Lean.Option.get (← getOptions) specimen.emitBasalt
    let useBasalt := emitBasalt && (deriveSort matches .Generator || deriveSort matches .Enumerator)
    if useBasalt then requireBasaltImport

    let combinatorFn :=
      if useBasalt then basaltBacktrackFn
      else match deriveSort with
      | .Generator => genBacktrackFn
      | .Enumerator => enumerateFn
      | .Checker | .Theorem => checkerBacktrackFn

    let mut sizeCaseExprs := #[]
    sizeCaseExprs := sizeCaseExprs.push (← `(Term.matchAltExpr|
      | $(mkIdent ``Nat.zero) => $combinatorFn $baseGenerators))
    sizeCaseExprs := sizeCaseExprs.push (← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $combinatorFn $inductiveGenerators))
    let sizeMatchExpr ← mkMatchExpr sizeIdent sizeCaseExprs

    let mut fuelCaseExprs := #[]
    -- Exhausting the termination counter is inconclusive, not a refutation.
    fuelCaseExprs := fuelCaseExprs.push (←
      if useBasalt then `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $backtrackGenExhaustFn)
      else `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $failFn $outOfFuelError))
    fuelCaseExprs := fuelCaseExprs.push (← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshFuel' => $sizeMatchExpr))
    let matchExpr ← mkMatchExpr fuelIdent fuelCaseExprs

    let paramInfo ← match precomputedParamInfo with
      | some info => pure info
      | none => analyzeInductiveArgs inductiveName inductiveLevels args
    let targetVarsList := targetVars

    -- Build the function type: Nat → Nat → Nat → param types → Gen α
    let mut paramTypes : Array (TSyntax `term) := #[natIdent, natIdent, natIdent]
    let mut outerParams : Array (TSyntax `term) := #[]
    let mut outputTypeSyntaxes : Array (TSyntax `term) := #[]
    let mut typeParams := #[]
    -- Build inner params for the lambda
    let mut innerParamBinders : Array (TSyntax `term) := #[]
    innerParamBinders := innerParamBinders.push (← `(($fuelIdent : $natIdent)))
    innerParamBinders := innerParamBinders.push (← `(($initSizeIdent : $natIdent)))
    innerParamBinders := innerParamBinders.push (← `(($sizeIdent : $natIdent)))

    for (paramName, paramType, paramTypeSyntax) in paramInfo do
      if paramType.isSort then
        typeParams := typeParams.push paramName
      if paramName ∉ targetVarsList then
        outerParams := outerParams.push (mkIdent paramName)
        paramTypes := paramTypes.push paramTypeSyntax
        if paramType.isSort then
          innerParamBinders := innerParamBinders.push (← `(($(mkIdent paramName) : Sort _)))
        else
          innerParamBinders := innerParamBinders.push (← `(($(mkIdent paramName) : $paramTypeSyntax)))
      else
        outputTypeSyntaxes := outputTypeSyntaxes.push paramTypeSyntax

    let targetTypeSyntax ← do
      if deriveSort == .Checker || deriveSort == .Theorem then
        `(Bool)
      else
        let syns ← if outputTypeSyntaxes.isEmpty then
          targetTypes.mapM (fun ty => PrettyPrinter.delab ty)
        else pure outputTypeSyntaxes.toList
        tupleOfListM (throwError "no output types found")
          (fun t rest => `($t × $rest)) syns
    let targetVarPattern : TSyntax `term ← do
      if deriveSort == .Checker || deriveSort == .Theorem then
        `(Unit.unit)
      else
        let rec mkProdPat : List Name → TermElabM (TSyntax `term)
          | [] => throwError "no output variables"
          | [v] => `($(Lean.mkIdent v))
          | v :: vs => do let rest ← mkProdPat vs; `(($(Lean.mkIdent v), $rest))
        mkProdPat targetVars

    let optionTProducerType ←
      if useBasalt then `($basaltGenVar $targetTypeSyntax)
      else match deriveSort with
      | .Generator => `($genTypeConstructor $targetTypeSyntax)
      | .Enumerator => `($exceptTTypeConstructor $genErrorType $enumTypeConstructor $targetTypeSyntax)
      | .Checker | .Theorem => `($exceptTypeConstructor $genErrorType $boolIdent)

    -- Build full function type with named Pi binders (handles dependent types)
    let mut allParamNamesAndTypes : Array (TSyntax `ident × TSyntax `term) := #[]
    allParamNamesAndTypes := allParamNamesAndTypes.push (fuelIdent, natIdent)
    allParamNamesAndTypes := allParamNamesAndTypes.push (initSizeIdent, natIdent)
    allParamNamesAndTypes := allParamNamesAndTypes.push (sizeIdent, natIdent)
    for (paramName, paramType, paramTypeSyntax) in paramInfo do
      if paramName ∉ targetVarsList then
        if paramType.isSort then
          allParamNamesAndTypes := allParamNamesAndTypes.push (mkIdent paramName, ← `(Sort _))
        else
          allParamNamesAndTypes := allParamNamesAndTypes.push (mkIdent paramName, paramTypeSyntax)
    let mut fullType ← pure optionTProducerType
    for (name, ty) in allParamNamesAndTypes.reverse do
      fullType ← `(($name : $ty) → $fullType)

    -- Add instance binders for type params
    let typeClasses := match requiredTypeClasses with
      | some tcs => tcs
      | none =>
        -- Under Basalt a type parameter needs a `G`-polymorphic unconstrained generator, and the
        -- *fueled* class specifically: a derived datatype only ever gets `Basalt.ArbitrarySized`, and
        -- Basalt's blanket `Arbitrary → ArbitrarySized` instance means the fueled binder still accepts a
        -- hand-written unfueled instance, so it is the weaker requirement.
        let producerUnconstrainedClass := basaltUnconstrainedClass useBasalt producerSort
        #[producerUnconstrainedClass, ``DecidableEq]
    let defTypeParamInstances ← mkTypeClassInstanceBinders typeParams typeClasses

    -- Emit the def with ∀ type (supports instance binders inline)
    -- One ident for declaration and reference. `globalDefName` is a *simple* name with the declaring
    -- namespace mangled in (see `specimenWorkerName`), so it is declared in the ambient namespace and an
    -- unqualified reference cannot be captured by an imported copy — that copy has a different name.
    let defIdent := mkIdent globalDefName
    -- Build ∀ type with instance binders interleaved after Sort-typed params
    let mut defType ← pure optionTProducerType
    -- Add non-Sort value params (from right)
    let insertIdx := 3 + typeParams.size
    for (name, ty) in allParamNamesAndTypes[insertIdx:].toArray.reverse do
      defType ← `(($name : $ty) → $defType)
    -- Add instance binders (referencing the Sort-typed params)
    for instBinder in defTypeParamInstances.reverse do
      defType ← `(∀ $instBinder:bracketedBinder, $defType)
    -- Add Sort-typed params + fuel/initSize/size (from right)
    for (name, ty) in allParamNamesAndTypes[:insertIdx].toArray.reverse do
      defType ← `(($name : $ty) → $defType)
    -- Under Basalt the definition is polymorphic in the generator monad. These binders go
    -- *outermost*, since the return type `G α` mentions `G`. Mutually recursive
    -- definitions in the block each carry their own `{G}`, which unify at the call sites, so the
    -- whole SCC ends up at one interpretation without needing a shared section variable.
    if useBasalt then
      defType ← liftMacroM (basaltForall defType)
    -- Lambda includes instance binders at the same position
    let instParams : Array (TSyntax `term) := defTypeParamInstances.map (fun b => ⟨b.raw⟩)
    let allInnerParams := innerParamBinders[:insertIdx].toArray ++ instParams ++ innerParamBinders[insertIdx:].toArray
    let innerLambda ← `(fun $allInnerParams* => $matchExpr)
    -- Bind the generator monad in an outer lambda rather than splicing binders into the parameter
    -- array: `fun {G} [Gen G] … => fun params => body` is the same term as one combined lambda, and
    -- avoids having to name the implicit-binder parser category.
    let lambdaBody ←
      if useBasalt then
        liftMacroM (basaltFun innerLambda)
      else pure innerLambda
    -- Name the recursive argument. Left to infer it, Lean's structural search over a large mutual block
    -- with three `Nat` parameters per definition gives up and falls back to well-founded recursion, whose
    -- eagerly proved unfolding lemma can exhaust the kernel's memory. Only a definition that passes
    -- `fuel'` on (see `recCall`) recurses; the clause on any other draws an "unused" warning.
    let recurses := [baseGenerators, inductiveGenerators].any (mentionsIdent freshFuel'.getId ·)
    let defCmd ←
      if !recurses then `(command| def $defIdent : $defType := $lambdaBody)
      -- `termination_by` binds every parameter after the colon, so the seven holes skip `{G}` and its
      -- six instances.
      else if useBasalt then `(command| def $defIdent : $defType := $lambdaBody
        termination_by structural _ _ _ _ _ _ _ $fuelIdent:ident => $fuelIdent)
      else `(command| def $defIdent : $defType := $lambdaBody
        termination_by structural $fuelIdent:ident => $fuelIdent)

    -- Emit the instance (differs by deriveSort)
    let fuelVal := Lean.Option.get (← getOptions) specimen.fuel
    let fuelLit := Syntax.mkNumLit (toString fuelVal)
    let callArgs : TSyntaxArray `term := #[(⟨fuelLit⟩ : TSyntax `term), (freshSizeIdent : TSyntax `term), (freshSizeIdent : TSyntax `term)] ++ (TSyntaxArray.mk outerParams)
    let callExpr ← `($defIdent $callArgs*)
    let instTypeClasses := match requiredTypeClasses with
      | some tcs => tcs
      | none => match deriveSort with
        | .Checker | .Theorem => #[``Enum, ``DecidableEq]
        | _ => match producerSort with
          -- Must agree with `defTypeParamInstances` above: under Basalt a type parameter needs a
          -- `G`-polymorphic unconstrained generator, so the binder is `Basalt.ArbitrarySized`. Emitting
          -- `Plausible.Arbitrary` here while the body calls `Basalt.ArbitrarySized.arbitrarySized`
          -- leaves the parameter's generator unsatisfiable — and the error names the *body's* class, so
          -- it reads as a missing user instance rather than a mismatched binder.
          | .Generator => #[basaltUnconstrainedClass useBasalt .Generator, ``DecidableEq]
          | .Enumerator => #[basaltUnconstrainedClass useBasalt .Enumerator, ``DecidableEq]
    let instCmd ← match deriveSort with
      | .Checker | .Theorem => do
        let arbitraryTypeParamInstances ← mkTypeClassInstanceBinders typeParams instTypeClasses
        `(command|
          instance $arbitraryTypeParamInstances:bracketedBinder* : $decOptTypeclass (@$(mkIdent inductiveName) $args*) where
            $unqualifiedDecOptFn:ident := fun $freshSizeIdent => $callExpr)
      | _ => do
        let producerTypeClass :=
          match useBasalt, producerSort with
          | true, .Generator => backtrackGenForTypeclass
          | true, .Enumerator => enumForTypeclass
          | false, .Generator => arbitrarySizedSuchThatTypeclass
          | false, .Enumerator => enumSizedSuchThatTypeclass
        let producerTypeClassFunction :=
          match useBasalt, producerSort with
          | true, .Generator => unqualifiedBacktrackGenForFn
          | true, .Enumerator => unqualifiedEnumForFn
          | false, .Generator => unqualifiedArbitrarySizedSTFn
          | false, .Enumerator => unqualifiedEnumSizedSTFn
        let arbitraryTypeParamInstances ← mkTypeClassInstanceBinders typeParams instTypeClasses
        if useBasalt then
          -- The leaf size is the worker's `initSize`; the search's size is its `size`.
          let leafCallArgs : TSyntaxArray `term := #[(⟨fuelLit⟩ : TSyntax `term),
            (freshLeafSizeIdent : TSyntax `term), (freshSizeIdent : TSyntax `term)] ++
            (TSyntaxArray.mk outerParams)
          `(command|
            instance $arbitraryTypeParamInstances:bracketedBinder* : $producerTypeClass $targetTypeSyntax (fun $targetVarPattern => @$(mkIdent inductiveName) $args*) where
              $producerTypeClassFunction:ident := fun $freshSizeIdent $freshLeafSizeIdent => $defIdent $leafCallArgs*)
        else
        `(command|
          instance $arbitraryTypeParamInstances:bracketedBinder* : $producerTypeClass $targetTypeSyntax (fun $targetVarPattern => @$(mkIdent inductiveName) $args*) where
            $producerTypeClassFunction:ident := fun $freshSizeIdent => $callExpr)

    return (defCmd, instCmd)

