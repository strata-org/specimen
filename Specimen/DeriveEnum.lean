import Lean

import Specimen.Debug
import Specimen.Idents
import Specimen.TSyntaxCombinators
import Specimen.Enumerators
import Specimen.Utils
import Plausible.DeriveArbitrary

open Lean Elab Command Meta Term Parser
open Elab.Deriving

open Idents

-- Note: the following functions closely follow the implementation of the deriving handler
-- for `Arbitrary` in Plausible/DeriveArbitrary.lean.

/-- Takes the name of a constructor for an algebraic data type and returns an array
    containing `(argument_name, argument_type)` pairs.

    If the algebraic data type is defined using anonymous constructor argument syntax, i.e.
    ```
    inductive T where
      C1 : τ1 → … → τn
      …
    ```
    Lean produces macro scopes when we try to access the names for the constructor args.
    In this case, we remove the macro scopes so that the name is user-accessible.
    (This will result in constructor argument names being non-unique in the array
    that is returned -- it is the caller's responsibility to produce fresh names,
    e.g. using `Idents.genFreshNames`.)
-/
def getArgsAndTypesFromCtorName (ctorName : Name) (numParams : Nat := 0) : MetaM (Array (Name × Expr)) := do
  let ctorInfo ← getConstInfoCtor ctorName

  forallTelescopeReducing ctorInfo.type fun args _ => do
    let mut argNamesAndTypes := #[]
    for h : i in [:args.size] do
      if i < numParams then continue
      let arg := args[i]
      let localDecl ← arg.fvarId!.getDecl
      let mut argName := localDecl.userName
      if argName.hasMacroScopes then
        argName := Name.eraseMacroScopes argName
      argNamesAndTypes := Array.push argNamesAndTypes (argName, localDecl.type)

    return argNamesAndTypes

open TSyntax.Compat in
/-- Recursively expand a structure-typed expression into `[Enum proj]` binders
    for each leaf field of type `Type u`. Nested structures are expanded recursively.
    Non-Type, non-structure fields cause an error. -/
private partial def expandStructEnumBinders (indName : Name) (argName : Name)
    (expr : Expr) (syn : TSyntax `term) : TermElabM (Array Syntax) := do
  let ty ← inferType expr
  if ty.isSort then
    try
      let c ← mkAppM ``Enum #[expr]
      if (← isTypeCorrect c) then
        return #[← `(instBinderF| [$(mkCIdent ``Enum):ident $syn])]
    catch _ => pure ()
    return #[]
  else
    let env ← getEnv
    let some sName := ty.constName? |
      throwError m!"Cannot derive Enum for '{indName}': structure parameter \
        '{mkIdent argName}' has a field of type '{ty}', which is not a Type or \
        structure of Types. This makes the type effectively indexed."
    let some sInfo := getStructureInfo? env sName |
      throwError m!"Cannot derive Enum for '{indName}': structure parameter \
        '{mkIdent argName}' has a field of type '{ty}', which is not a Type or \
        structure of Types. This makes the type effectively indexed."
    let mut result : Array Syntax := #[]
    for field in sInfo.fieldNames do
      let projName := sName ++ field
      let projExpr := mkApp (mkConst projName) expr
      let projSyn ← `($(mkIdent projName) $syn)
      result := result ++ (← expandStructEnumBinders indName argName projExpr projSyn)
    return result

def mkEnumInstBinders (indVal : InductiveVal) (argNames : Array Name) :
    TermElabM (Array Syntax) := do
  forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let mut binders : Array Syntax := #[]
    for h : i in [:params.size] do
      let param := params[i]
      let argName := argNames[i]!
      let normalOk ← try
        let c ← mkAppM ``Enum #[param]
        isTypeCorrect c
      catch _ => pure false
      if normalOk then
        binders := binders.push
          (← `(instBinderF| [$(mkCIdent ``Enum):ident $(mkIdent argName):ident]))
      else
        binders := binders ++ (← expandStructEnumBinders indVal.name argName param (mkIdent argName))
    return binders

open TSyntax.Compat in
/-- Creates a `Header` for the `Enum` typeclass (mirrors `mkArbitraryHeader` from DeriveArbitrary) -/
def mkEnumHeader (indVal : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let targetType ← mkInductiveApp indVal argNames
  let binders := binders ++ (← mkEnumInstBinders indVal argNames)
  return { binders, argNames, targetNames := #[], targetType }

/-- Creates the *body* of the enumerator that appears in the `EnumSized` instance -/
def mkEnumBody (inductiveVal : InductiveVal) (enumeratorType : TSyntax `term) : TermElabM Term := do
  let targetTypeName := inductiveVal.name

  -- Fetch the ambient local context, which we need to produce user-accessible fresh names
  let localCtx ← getLCtx

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the enumerator function, as well as the `aux_enum` inner helper function
  let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
  let freshSize' := mkFreshAccessibleIdent localCtx `size'

  let mut nonRecursiveEnumerators := #[]
  let mut recursiveEnumerators := #[]
  for ctorName in inductiveVal.ctors do
    let ctorIdent := mkIdent ctorName
    let ctorArgNamesTypes ← getArgsAndTypesFromCtorName ctorName inductiveVal.numParams

    if ctorArgNamesTypes.isEmpty then
      -- Constructor is nullary, we can just use an enumerator of the form `pure ...`
      let pureGen ← `($pureFn $ctorIdent)
      nonRecursiveEnumerators := nonRecursiveEnumerators.push pureGen
    else
      -- Produce a fresh name for each of the args to the constructor
      let ctorArgNames := Prod.fst <$> ctorArgNamesTypes
      let freshArgIdents := Lean.mkIdent <$> genFreshNames (existingNames := ctorArgNames) (namePrefixes := ctorArgNames)

      let mut doElems := #[]
      -- Determine whether the constructor has any recursive arguments
      let ctorIsRecursive ← isConstructorRecursive targetTypeName ctorName
      if !ctorIsRecursive then
        -- Call `enum` to enumerate a value for each of the arguments
        for freshIdent in freshArgIdents do
          let bindExpr ← mkLetBind freshIdent #[enumFn]
          doElems := doElems.push bindExpr
      else
        -- For recursive constructors, we need to examine each argument to see which of them require
        -- recursive calls to the enumerator
        let freshArgIdentsTypes := Array.zip freshArgIdents (Prod.snd <$> ctorArgNamesTypes)
        for (freshIdent, argType) in freshArgIdentsTypes do
          -- If the argument's type is the same as the target type,
          -- produce a recursive call to the enumerator using `aux_enum`,
          -- otherwise enumerate a value using `enum`
          let bindExpr ←
            if argType.getAppFn.constName == targetTypeName then
              mkLetBind freshIdent #[auxEnumFn, freshSize']
            else
              mkLetBind freshIdent #[enumFn]
          doElems := doElems.push bindExpr

      -- Create an expression `return C x1 ... xn` at the end of the enumerator, where
      -- `C` is the constructor name and the `xi` are the enumerated values for the args
      let pureExpr ← `(doElem| return $ctorIdent $freshArgIdents*)
      doElems := doElems.push pureExpr

      -- Put the body of the enumerator together
      let enumeratorBody ← mkDoBlock doElems
      if !ctorIsRecursive then
        nonRecursiveEnumerators := nonRecursiveEnumerators.push enumeratorBody
      else
        recursiveEnumerators := recursiveEnumerators.push enumeratorBody

  -- Just use the first non-recursive enumerator as the default enumerator
  let defaultGenerator ← Option.getDM (nonRecursiveEnumerators[0]?)
    (throwError m!"derive Enum failed, {targetTypeName} has no non-recursive constructors")

  -- Create the cases for the pattern-match on the size argument
  -- If `size = 0`, pick one of the non-recursive enumerators
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $zeroIdent => $oneOfWithDefaultEnumCombinatorFn $defaultGenerator [$nonRecursiveEnumerators,*])
  caseExprs := caseExprs.push zeroCase

  -- If `size = .succ size'`, pick an enumerator (it can be non-recursive or recursive)
  let allEnumerators ← `([$nonRecursiveEnumerators,*, $recursiveEnumerators,*])
  let succCase ← `(Term.matchAltExpr| | $succIdent $freshSize' => $oneOfWithDefaultEnumCombinatorFn $defaultGenerator $allEnumerators)
  caseExprs := caseExprs.push succCase

  -- Create function argument for the enumerator size
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← mkMatchExpr sizeIdent caseExprs

  `(let rec $auxEnumFn:ident $sizeParam : $enumeratorType :=
      $matchExpr
    fun $freshSizeIdent => $auxEnumFn $freshSizeIdent)

/-- Creates the function definition for the derived enumerator.
    Mirrors `Plausible.mkAuxFunction` from `DeriveArbitrary.lean`. -/
def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← mkEnumHeader indVal
  let binders := header.binders

  -- Determine the type of the enumerator
  -- (the `Enumerator` type constructor applied to the name of the `inductive` type, plus any type parameters)
  let targetType ← mkInductiveApp ctx.typeInfos[i]! header.argNames
  let enumeratorType ← `($enumTypeConstructor $targetType)

  let mut body ← mkEnumBody indVal enumeratorType

  -- When `usePartial` is true (nested or mutual recursion), create local
  -- `let`-definitions containing the relevant `EnumSized` instances so that
  -- `Enum TargetType` is available (via the `EnumSized → Enum` bridge) for
  -- resolving instances like `EnumSized (List TargetType)`.
  -- This mirrors how `DeriveArbitrary` emits local `ArbitraryFueled` instances.
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``EnumSized header.argNames
    body ← mkLet letDecls body

  if ctx.usePartial then
    `(partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent ``Nat) → $enumeratorType := $body:term)
  else
    `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent ``Nat) → $enumeratorType := $body:term)

/-- Creates a `mutual ... end` block containing the definitions of the derived enumerators -/
def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in 0...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

open TSyntax.Compat in
/-- Variant of `Deriving.Util.mkInstanceCmds` specialized to creating `EnumSized` instances
    that have `Enum` inst-implicit binders (mirroring `mkArbitraryFueledInstanceCmds`). -/
def mkEnumSizedInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in 0...ctx.typeInfos.size do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkEnumInstBinders indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `($(mkCIdent ``EnumSized) $indType)
      let val ← `(⟨$(mkIdent auxFunName)⟩)
      let instCmd ← `(instance $binders:implicitBinder* : $type := $val)
      instances := instances.push instCmd
  return instances

/-- Creates the commands for deriving `EnumSized` for a single type -/
def mkEnumSizedInstanceCmd (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Enum "enumSized" declName
  return #[← mkMutualBlock ctx] ++ (← mkEnumSizedInstanceCmds ctx #[declName])

syntax (name := enum_deriver) "derive_enum" term : command

/-- Command elaborator which derives an instance of the `EnumSized` typeclass -/
@[command_elab enum_deriver]
def elabDeriveEnum : CommandElab := fun stx => do
  match stx with
  | `(derive_enum $targetTypeTerm:term) => do

    -- TODO: figure out how to support parameterized types
    let targetTypeIdent ←
      match targetTypeTerm with
      | `($tyIdent:ident) => pure tyIdent
      | _ => throwErrorAt targetTypeTerm "Parameterized types not supported"
    let targetTypeName := targetTypeIdent.getId

    let isInductiveType ← isInductive targetTypeName
    if isInductiveType then
      let cmds ← liftTermElabM $ mkEnumSizedInstanceCmd targetTypeName

      -- Pretty-print the derived enumerator
      -- & display the code for the derived typeclass instance to the user
      -- in the VS Code side panel
      let instCmd : TSyntax `command := ⟨cmds.back!⟩
      let enumFormat ← liftCoreM (PrettyPrinter.ppCommand instCmd)
      -- Suppressed under `set_option specimen.silent true`.
      unless (← inSilentMode) do
        liftTermElabM $ Tactic.TryThis.addSuggestion stx
          (Format.pretty enumFormat) (header := "Try this enumerator: ")

      -- Elaborate the typeclass instance and add it to the local context
      for cmd in cmds do elabCommand cmd
    else
      throwError "Cannot derive Enum instance for non-inductive types"

  | _ => throwUnsupportedSyntax

/-- Deriving handler which produces an instance of the `EnumSized` typeclass for
    each type specified in `declNames` -/
def deriveEnumInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      let cmds ← liftTermElabM $ mkEnumSizedInstanceCmd declName
      for cmd in cmds do elabCommand cmd
    return true
  else
    throwError "Cannot derive instance of Enum typeclass for non-inductive types"
    return false

initialize
  registerDerivingHandler ``Enum deriveEnumInstanceHandler
