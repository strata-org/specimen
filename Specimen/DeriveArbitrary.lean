/-
  Override of Plausible's `DeriveArbitrary` with support for structure-parameterized types.

  This re-registers the `Arbitrary` deriving handler. The only semantic change from
  Plausible's version is `mkArbitraryInstBinders` (replacing `mkInstImplicitBinders`),
  which expands structure parameters into per-field `[Arbitrary T.Field]` binders.

  Once this fix is upstreamed to Plausible, this file can be removed.
-/
import Plausible.DeriveArbitrary

open Lean Elab Meta Parser Term
open Elab.Deriving
open Elab.Command

namespace Plausible.Override

open Plausible Arbitrary

open TSyntax.Compat in
/-- Recursively expand a structure-typed expression into `[Arbitrary proj]` binders
    for each leaf field of type `Type u`. Nested structures are expanded recursively.
    Non-Type, non-structure fields cause an error. -/
private partial def expandStructBinders (className : Name) (indName : Name) (argName : Name)
    (expr : Expr) (syn : TSyntax `term) : TermElabM (Array Syntax) := do
  let ty ← inferType expr
  if ty.isSort then
    try
      let c ← mkAppM className #[expr]
      if (← isTypeCorrect c) then
        return #[← `(instBinderF| [$(mkCIdent className):ident $syn])]
    catch _ => pure ()
    return #[]
  else
    let env ← getEnv
    let some sName := ty.constName? |
      throwError m!"Cannot derive {className} for '{indName}': structure parameter \
        '{mkIdent argName}' has a field of type '{ty}', which is not a Type or \
        structure of Types. This makes the type effectively indexed."
    let some sInfo := getStructureInfo? env sName |
      throwError m!"Cannot derive {className} for '{indName}': structure parameter \
        '{mkIdent argName}' has a field of type '{ty}', which is not a Type or \
        structure of Types. This makes the type effectively indexed."
    let mut result : Array Syntax := #[]
    for field in sInfo.fieldNames do
      let projName := sName ++ field
      let projExpr := mkApp (mkConst projName) expr
      let projSyn ← `($(mkIdent projName) $syn)
      result := result ++ (← expandStructBinders className indName argName projExpr projSyn)
    return result

def mkArbitraryInstBinders (className : Name) (indVal : InductiveVal) (argNames : Array Name) :
    TermElabM (Array Syntax) := do
  forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let mut binders : Array Syntax := #[]
    for h : i in [:params.size] do
      let param := params[i]
      let argName := argNames[i]!
      let normalOk ← try
        let c ← mkAppM className #[param]
        isTypeCorrect c
      catch _ => pure false
      if normalOk then
        binders := binders.push
          (← `(instBinderF| [$(mkCIdent className):ident $(mkIdent argName):ident]))
      else
        binders := binders ++ (← expandStructBinders className indVal.name argName param (mkIdent argName))
    return binders

open TSyntax.Compat in
def mkArbitraryHeader (indVal : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let targetType ← mkInductiveApp indVal argNames
  let binders := binders ++ (← mkArbitraryInstBinders ``Arbitrary indVal argNames)
  return { binders, argNames, targetNames := #[], targetType }

/-- Constructor arg names and types, skipping type parameters. -/
def getCtorArgs (indVal : InductiveVal) (ctorName : Name) : MetaM (Array (Name × Expr)) := do
  let ctorInfo ← getConstInfoCtor ctorName
  forallTelescopeReducing ctorInfo.type fun args _ => do
    let mut result := #[]
    for h : i in [:args.size] do
      if i < indVal.numParams then continue
      let arg := args[i]
      let argType ← arg.fvarId!.getType
      let argName ← Core.mkFreshUserName `a
      result := result.push (argName, argType)
    return result

/-- Creates the body of the generator (duplicated from Plausible since `mkBody` is module-private). -/
def mkBody (_header : Header) (inductiveVal : InductiveVal) (generatorType : TSyntax `term) : TermElabM Term := do
  let targetTypeName := inductiveVal.name
  let freshFuel := Lean.mkIdent (← Core.mkFreshUserName `fuel)
  let freshFuel' := Lean.mkIdent (← Core.mkFreshUserName `fuel')
  let auxArb := mkIdent `aux_arb

  let mut weightedNonRecursiveGenerators := #[]
  let mut weightedRecursiveGenerators := #[]
  let mut nonRecursiveGeneratorsNoWeights := #[]

  for ctorName in inductiveVal.ctors do
    let ctorIdent := mkIdent ctorName
    let ctorArgNamesTypes ← getCtorArgs inductiveVal ctorName
    let (ctorArgNames, ctorArgTypes) := Array.unzip ctorArgNamesTypes
    let ctorArgIdents := Lean.mkIdent <$> ctorArgNames
    let ctorArgIdentsTypes := Array.zip ctorArgIdents ctorArgTypes

    if ctorArgNamesTypes.isEmpty then
      let pureGen ← `(($(Lean.mkIdent `pure) $ctorIdent))
      weightedNonRecursiveGenerators := weightedNonRecursiveGenerators.push (← `((1, $pureGen)))
      nonRecursiveGeneratorsNoWeights := nonRecursiveGeneratorsNoWeights.push pureGen
    else
      let (generatorBody, ctorIsRecursive) ←
        withLocalDeclsDND ctorArgNamesTypes (fun _ => do
          let mut doElems := #[]
          let mut ctorIsRecursive := false
          for (freshIdent, argType) in ctorArgIdentsTypes do
            let bindExpr ←
              if argType.isAppOf targetTypeName then
                ctorIsRecursive := true
                `(doElem| let $freshIdent ← $(mkIdent `aux_arb):term $(freshFuel'):term)
              else
                `(doElem| let $freshIdent ← $(mkIdent ``Arbitrary.arbitrary):term)
            doElems := doElems.push bindExpr
          let pureExpr ← `(doElem| return $ctorIdent $ctorArgIdents*)
          doElems := doElems.push pureExpr
          let generatorBody ← `((do $[$doElems:doElem]*))
          pure (generatorBody, ctorIsRecursive))

      if !ctorIsRecursive then
        weightedNonRecursiveGenerators := weightedNonRecursiveGenerators.push (← `((1, $generatorBody)))
        nonRecursiveGeneratorsNoWeights := nonRecursiveGeneratorsNoWeights.push generatorBody
      else
        weightedRecursiveGenerators := weightedRecursiveGenerators.push (← ``(($freshFuel' + 1, $generatorBody)))

  let defaultGenerator ← Option.getDM (nonRecursiveGeneratorsNoWeights[0]?)
    (throwError m!"derive Arbitrary failed, {targetTypeName} has no non-recursive constructors")

  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $(mkIdent ``Gen.oneOfWithDefault) $defaultGenerator [$nonRecursiveGeneratorsNoWeights,*])
  caseExprs := caseExprs.push zeroCase

  let allWeightedGenerators ← `([$weightedNonRecursiveGenerators,*, $weightedRecursiveGenerators,*])
  let succCase ← `(Term.matchAltExpr| | $freshFuel' + 1 => $(mkIdent ``Gen.frequency) $defaultGenerator $allWeightedGenerators)
  caseExprs := caseExprs.push succCase

  let fuelParam ← `(Term.letIdBinder| ($freshFuel : $(mkIdent `Nat)))
  let matchExpr ← `(match $freshFuel:ident with $caseExprs:matchAlt*)

  `(let rec $auxArb:ident $fuelParam : $generatorType :=
      $matchExpr
    fun $freshFuel => $auxArb $freshFuel)

def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← mkArbitraryHeader indVal
  let binders := header.binders

  let targetType ← mkInductiveApp ctx.typeInfos[i]! header.argNames
  let generatorType ← `($(mkIdent ``Plausible.Gen) $targetType)

  let mut body ← mkBody header indVal generatorType

  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``ArbitraryFueled header.argNames
    body ← mkLet letDecls body

  if ctx.usePartial then
    `(partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent ``Nat) → $generatorType := $body:term)
  else
    `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent ``Nat) → $generatorType := $body:term)

def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in 0...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

open TSyntax.Compat in
def mkArbitraryFueledInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name)
    (useAnonCtor := true) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in 0...ctx.typeInfos.size do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkArbitraryInstBinders ``Arbitrary indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `($(mkCIdent ``ArbitraryFueled) $indType)
      let mut val := mkIdent auxFunName
      if useAnonCtor then val ← `(⟨$val⟩)
      let instCmd ← `(instance $binders:implicitBinder* : $type := $val)
      instances := instances.push instCmd
  return instances

def mkArbitraryFueledInstanceCmd (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Arbitrary "arbitrary" declName
  let cmds := #[← mkMutualBlock ctx] ++ (← mkArbitraryFueledInstanceCmds ctx #[declName])
  trace[plausible.deriving.arbitrary] "\n{cmds}"
  return cmds

def mkArbitraryInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if !(← declNames.allM isInductive) then
    throwError "Cannot derive instance of Arbitrary typeclass for non-inductive types"
  for declName in declNames do
    let indVal ← liftTermElabM $ getConstInfoInduct declName
    if indVal.numIndices > 0 then
      throwError "Cannot derive instance of Arbitrary typeclass for indexed inductive type '{declName}'"
  for declName in declNames do
    let cmds ← liftTermElabM $ mkArbitraryFueledInstanceCmd declName
    cmds.forM elabCommand
  return true

initialize
  registerDerivingHandler ``Arbitrary mkArbitraryInstanceHandler

end Plausible.Override
