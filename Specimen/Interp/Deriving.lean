import Specimen.Interp.Bridge

/-!
# Deriving `ToVal` and `OfVal`

Both directions of the bridge are purely structural: `ToVal` reflects a constructor's name and converts
its fields; `OfVal` matches `Val.ctor name args` back. Written by hand that is boilerplate proportional
to the number of constructors, and it has to be redone for every project whose relations the interpreter
is pointed at — Cedar alone needs `CedarType`, `Name`, `EntityUID`, `Prim`, `Qualified`, `BoolType`,
`ExtType` and `Attr` before a single one of its schedules can run.

So derive it:

```
deriving instance ToVal, OfVal for CedarType
```

## What the encoding has to agree with

`Val.mkCtor` and the fully qualified constructor name, because that is what the interpreter's `Match`
steps pattern-match against (`Specimen.Interp.matchPattern`) and what the hand-written instances in
`Bridge` already produce. `mkCtor` rather than `Val.ctor` so `Nat.zero`/`Nat.succ` normalise to literals,
keeping a derived instance agreeing with `instToValNat` on a type that happens to contain a `Nat`.

## Recursion, including through containers

`CedarType.record` holds a `Map Attr (Qualified CedarType)`: the recursion runs through two container
types before coming back. So the generated function cannot just call itself on same-typed fields — it has
to make `ToVal CedarType` *available as an instance* while it is being defined, so that
`ToVal (Map Attr (Qualified CedarType))` can be resolved from `ToVal (Qualified CedarType)` from
`ToVal CedarType`.

`Lean.Elab.Deriving.mkLocalInstanceLetDecls` does exactly that — it binds the class at every type in the
mutual family to the corresponding auxiliary function — so emitting those let-declarations is what makes
nested recursion work, and every field can then simply use `toVal`/`ofVal` and let instance resolution
sort it out. The functions are `partial` for the same reason: the recursion is not structural once it
passes through a container.
-/

open Lean Elab Command Term Meta Lean.Parser.Term
open Lean.Elab.Deriving

namespace Specimen.Interp

/-! ## `ToVal` -/

/-- One match arm per constructor: bind the fields, convert each, reflect the name. -/
private def mkToValAlts (indVal : InductiveVal) : TermElabM (Array (TSyntax ``matchAlt)) := do
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt ← forallTelescopeReducing ctorInfo.type fun _ _ => do
      -- Parameters are inaccessible in a pattern; fields become fresh binders.
      let mut ctorArgs := #[]
      for _ in [0:indVal.numParams] do
        ctorArgs := ctorArgs.push (← `(_))
      let mut fields := #[]
      for _ in [0:ctorInfo.numFields] do
        let a := mkIdent (← mkFreshUserName `a)
        ctorArgs := ctorArgs.push a
        fields := fields.push a
      let pattern ← `(@$(mkIdent ctorName):ident $ctorArgs:term*)
      let args ← fields.mapM fun a => `($(mkCIdent ``toVal) $a)
      let rhs ← `($(mkCIdent ``Val.mkCtor) $(quote ctorName) [$args,*])
      `(matchAltExpr| | $pattern:term => $rhs:term)
    alts := alts.push alt
  return alts

private def mkToValAux (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← mkHeader ``ToVal 1 indVal
  let target := mkIdent header.targetNames[0]!
  let alts ← mkToValAlts indVal
  let mut body ← `(match $target:term with $alts:matchAlt*)
  -- The family's own instances, so recursion through a container resolves. See the module docstring.
  body ← mkLet (← mkLocalInstanceLetDecls ctx ``ToVal header.argNames) body
  `(partial def $(mkIdent auxFunName):ident $header.binders:bracketedBinder* :
      $(mkCIdent ``Val) := $body:term)

/-! ## `OfVal` -/

/-- One match arm per constructor, on `Val.ctor <name> [fields]`. The arity is part of the pattern, so a
    `Val` carrying the right name with the wrong number of arguments falls through to the catch-all and
    is reported rather than silently mismatched. -/
private def mkOfValAlts (indVal : InductiveVal) : TermElabM (Array (TSyntax ``matchAlt)) := do
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt ← forallTelescopeReducing ctorInfo.type fun _ _ => do
      let mut fields := #[]
      for _ in [0:ctorInfo.numFields] do
        fields := fields.push (mkIdent (← mkFreshUserName `a))
      let pattern ← `($(mkCIdent ``Val.ctor) $(quote ctorName) [$fields,*])
      -- Parameters are implicit here: we are building the value, so they are inferred from the
      -- expected type rather than recovered from the `Val`, which does not carry them.
      -- Build the call first: v4.34's parser takes no application directly after `← $(…)`.
      let args ← fields.mapM fun a => do
        let call ← `($(mkCIdent ``ofVal) $a)
        `((← $call:term))
      let rhs ← `(do return $(mkIdent ctorName):ident $args*)
      `(matchAltExpr| | $pattern:term => $rhs:term)
    alts := alts.push alt
  return alts

private def mkOfValAux (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  -- Arity 0: the explicit argument is a `Val`, not a value of the inductive, so it is added here
  -- rather than by `mkHeader`.
  let header ← mkHeader ``OfVal 0 indVal
  let v := mkIdent (← mkFreshUserName `v)
  let alts ← mkOfValAlts indVal
  let indType ← mkInductiveApp indVal header.argNames
  let mut body ← `(match $v:term with
      $alts:matchAlt*
      | bad => Except.error s!"expected `{$(quote indVal.name)}`, got `{bad}`")
  body ← mkLet (← mkLocalInstanceLetDecls ctx ``OfVal header.argNames) body
  `(partial def $(mkIdent auxFunName):ident $header.binders:bracketedBinder*
      ($v : $(mkCIdent ``Val)) : Except String $indType := $body:term)

/-! ## Handlers -/

private def mkCmds (className : Name) (fnPrefix : String)
    (mkAux : Deriving.Context → Nat → TermElabM Command) (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext className fnPrefix declName
  -- Always `partial`: recursion through a container is not structural, and every derived function here
  -- is a total-by-construction traversal whose termination Lean cannot see.
  let ctx := { ctx with usePartial := true }
  let mut auxDefs := #[]
  for i in [0:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAux ctx i)
  let block ← `(mutual $auxDefs:command* end)
  return #[block] ++ (← mkInstanceCmds ctx className #[declName])

private def handlerFor (className : Name) (fnPrefix : String)
    (mkAux : Deriving.Context → Nat → TermElabM Command) (declNames : Array Name) :
    CommandElabM Bool := do
  if !(← declNames.allM isInductive) then
    return false
  for declName in declNames do
    let indVal ← liftTermElabM <| getConstInfoInduct declName
    -- An index is not recoverable from a `Val`, which carries constructor names and arguments only.
    if indVal.numIndices > 0 then
      throwError "cannot derive {className} for the indexed inductive type '{declName}': a `Val` \
        records a constructor and its arguments, not the indices the type is family-indexed by"
  for declName in declNames do
    let cmds ← liftTermElabM <| mkCmds className fnPrefix mkAux declName
    cmds.forM elabCommand
  return true

initialize
  registerDerivingHandler ``ToVal (handlerFor ``ToVal "toVal" mkToValAux)
  registerDerivingHandler ``OfVal (handlerFor ``OfVal "ofVal" mkOfValAux)

end Specimen.Interp
