import Specimen.Interp.Preschedule

/-!
# Extracting a `RelSpec` from a real inductive

`Specimen.Interp.Preschedule` schedules from a `RelSpec` — a relation's binders, premises and
conclusion as data. Writing one by hand is fine for `BST`; it is not fine for Cedar. This module
reads the inductive declaration and produces the `RelSpec` for you.

Two commands, both self-contained:

```lean
#specimen_relspec BST              -- log a pasteable `RelSpec` literal
derive_relspec BST                 -- define `def bstRelSpec : RelSpec := …`
derive_relspec BST as myBstSpec    -- …under a name you choose
```

The extraction is **read-only and separate from the derivation pipeline**: nothing here is imported by
`derive_mutual`, no schedule search runs, no instance is synthesised, and no environment extension is
touched. It reads `getConstInfoInduct`/`getConstInfoCtor` and reuses the pipeline's own reifiers
(`Schedules.exprToConstructorExpr`, `Schedules.exprToHypothesisExpr`) so that the `ConstructorExpr`s
come out spelled exactly as the compile-time scheduler would spell them. That matters: the runtime
scheduler's decisions are structural, so a differently-spelled premise would schedule differently.

## What is reproduced, and what is not

* **Binder classification** follows the pipeline's rule (`DeriveConstrainedProducer.lean:447-466`): a
  binder is a *variable* when it has a user-visible name or is instance-implicit, and a *premise*
  otherwise — an anonymous binder is what `∀ n m, n ≤ m → …` produces for the `n ≤ m`.
* **Conclusion flattening** is reproduced at the data level by `CtorSpec.linearize`, the counterpart
  of the pipeline's `linearizeAndFlatten` phase 1: a function application in the conclusion cannot be
  matched against, so it becomes a fresh variable plus an equality premise. Without this the extracted
  spec would be rejected by `reschedule` with `conclusionNotLinearized`.
* **`delegable` is left empty.** Deciding it requires synthesising an `ArbitrarySizedSuchThat`
  instance per equality premise, which is exactly the compile-time machinery this module stays out of.
  Fill it in by hand if a premise has a producer you want used.
* **`argNames` are invented** — `a_1`, `b_1`, … freshened against every binder name in the relation.
  They are internal to a schedule, so any collision-free choice does.
-/

open Lean Meta Elab Command Schedules

namespace Specimen.Interp

/-! ## Flattening a conclusion, at the data level -/

/-- Whether an expression tree contains a function application anywhere. Such a subterm cannot be
    turned into a pattern, so a conclusion holding one cannot be matched against an input. -/
partial def hasFuncApp : ConstructorExpr → Bool
  | .FuncApp .. => true
  | .Ctor _ args | .TyCtor _ args => args.any hasFuncApp
  | _ => false

/-- Replaces each maximal function-application subterm of `e` with a fresh variable, returning the
    rewritten expression and the `(freshVar, replacedSubterm)` pairs. `next` supplies fresh names. -/
partial def flattenFuncApps (next : Nat → Name) (start : Nat) (e : ConstructorExpr) :
    ConstructorExpr × List (Name × ConstructorExpr) × Nat :=
  match e with
  | .FuncApp .. =>
    let v := next start
    (.Unknown v, [(v, e)], start + 1)
  | .Ctor c args =>
    let (args', subs, n) := flattenList next start args
    (.Ctor c args', subs, n)
  | .TyCtor c args =>
    let (args', subs, n) := flattenList next start args
    (.TyCtor c args', subs, n)
  | other => (other, [], start)
where
  /-- `flattenFuncApps` over a list, threading the fresh-name counter. -/
  flattenList (next : Nat → Name) (start : Nat) :
      List ConstructorExpr → List ConstructorExpr × List (Name × ConstructorExpr) × Nat
    | [] => ([], [], start)
    | a :: as =>
      let (a', subs, n) := flattenFuncApps next start a
      let (as', subs', n') := flattenList next n as
      (a' :: as', subs ++ subs', n')

/-- The data-level counterpart of the pipeline's `linearizeAndFlatten` phase 1.

    A function application in the conclusion is *unmatchable*: the schedule cannot destructure
    `f x` to recover `x`, and it cannot pattern-match an input against it. The pipeline therefore
    lifts each such subterm into a fresh variable `unk_i` plus a premise `unk_i = f x`, which the
    scheduler can then either check (when everything is bound) or solve for (via the built-in equality
    producer). This does the same to a `CtorSpec`.

    Idempotent, and a no-op on a conclusion that has no function application — which is the common
    case, and why an extracted `BST` spec is unaffected. -/
def CtorSpec.linearize (c : CtorSpec) : CtorSpec :=
  if !c.conclusionArgs.any hasFuncApp then c
  else
    let used := c.vars.map VarSpec.name
    let next := fun (i : Nat) => freshen used (Name.mkSimple s!"unk_{i}")
    let (args', subs, _) := c.conclusionArgs.foldl (fun (acc, subs, n) a =>
      let (a', s, n') := flattenFuncApps next n a
      (acc ++ [a'], subs ++ s, n')) ([], [], 0)
    { c with
      conclusionArgs := args'
      -- The equality premise mirrors `mkEq newVar funcApp`: the fresh variable on the left, the
      -- replaced subterm on the right, with the type argument as a droppable hole.
      hypotheses := c.hypotheses ++ subs.map (fun (v, e) => (``Eq, [.Hole, .Unknown v, e]))
      vars := c.vars ++ subs.map (fun (v, _) => ({ name := v } : VarSpec)) }

/-! ## Reading the declaration -/

/-- A relation's last name component, lowered to identifier case: `BST` → `bst`, `HasTypeA` →
    `hasTypeA`. `decapitalize` alone would give `bST`, which reads badly in a generated artifact. -/
def shortIdent (indName : Name) : String :=
  let short := (indName.componentsRev.head?.getD indName).getString!
  if short.all (fun ch => !ch.isLower) then short.toLower else short.decapitalize

/-- Names for a relation's arguments: `a_1`, `b_1`, … past `l_1`, `v12_1`, freshened against `used`
    so they cannot collide with a constructor's own binders. -/
def mkArgNames (used : List Name) (n : Nat) : List Name :=
  let pool := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"]
  (List.range n).map (fun i =>
    freshen used (Name.mkSimple ((pool[i]?).getD s!"v{i}" ++ "_1")))

/-- The argument positions of an inductive that carry no runtime value: `Sort`-typed ones and
    typeclass instances. `RelSchedule.typeArgIndices` skips these when matching a caller's `Val`s to
    argument positions. -/
def extractTypeArgIndices (indName : Name) : MetaM (List Nat) := do
  let info ← getConstInfoInduct indName
  forallTelescopeReducing info.type fun args _ => do
    let mut idxs := []
    for (a, i) in args.toList.zipIdx do
      let ty ← inferType a
      if ty.isSort || (← isClass? ty).isSome then
        idxs := idxs ++ [i]
    return idxs

/-- The reified type of each of a relation's argument positions, for typing the fresh variables
    `CtorSpec.linearize` introduces. A position whose type is not reifiable (a sort, a function type)
    gets a placeholder; nothing generates a value for those anyway. -/
def extractArgTypes (indName : Name) : MetaM (List HypothesisExpr) := do
  let info ← getConstInfoInduct indName
  forallTelescopeReducing info.type fun args _ =>
    args.toList.mapM fun a => do
      let ty ← inferType a
      if ty.isSort then pure (`Sort, [])
      else
        try pure (← exprToHypothesisExpr indName ty)
        catch _ => pure (`_unreifiableType, [])

-- `isTypeValuedConst` / `retypeTypeApps` live in `Schedules`, next to `exprToHypothesisExpr`, which
-- now applies them itself: the compile-time deriver needs the same classification (see there).

/-- `retypeTypeApps` over a hypothesis's arguments. -/
def retypeHyp (h : HypothesisExpr) : MetaM HypothesisExpr := do
  return (h.1, ← h.2.mapM retypeTypeApps)

/-- The function whose application `CtorSpec.linearize` replaced with the fresh variable `v`.

    Recovered from the equality premise linearization emits — `v = f x` — which is the only record that
    the substitution happened. -/
def CtorSpec.freshVarSource? (c : CtorSpec) (v : Name) : Option Name :=
  c.hypotheses.findSome? fun (rel, args) =>
    if rel != ``Eq then none
    else
      match args with
      | [_, .Unknown v', .FuncApp f _] => if v' == v then some f else none
      -- Linearization puts the fresh variable on the left, but a hand-written `CtorSpec` need not.
      | [_, .FuncApp f _, .Unknown v'] => if v' == v then some f else none
      | _ => none

/-- A function's result type, reified, for typing a fresh variable that stands in for an application
    of it.

    `none` when the result type mentions the arguments, because then there is no single type to record:
    the fresh variable's type would depend on values the schedule has not chosen yet. Also `none` when
    the result type is not reifiable, which is the same situation `extractArgTypes` handles. -/
def funcResultType (indName : Name) (fname : Name) : MetaM (Option HypothesisExpr) := do
  let some info := (← getEnv).find? fname | return none
  forallTelescopeReducing info.type fun xs result => do
    if xs.any (fun x => result.containsFVar x.fvarId!) then return none
    if result.isSort then return none
    try return some (← exprToHypothesisExpr indName result)
    catch _ => return none

/-- Gives the fresh variables `CtorSpec.linearize` introduced a type.

    Linearization works on `ConstructorExpr`s, which carry no types, so it can only leave the fresh
    variable untyped — and an untyped variable is unusable: an `Unconstrained` step for it cannot find a
    generator, so *every plan that pre-generates it is unrunnable*. On Cedar that was the whole story for
    `Lub.record`, whose four independent premises give the largest plan space in the family and of which
    only one plan could be measured.

    Two sources, in order:

    1. A fresh variable standing in for a **whole conclusion argument** takes that argument's type.
    2. One standing in for a **nested subterm** takes the result type of the function whose application
       it replaced, read off the `v = f x` premise linearization left behind.

    A variable neither of those reaches stays untyped — a dependent result type, say — and
    `InterpEnv.check` names it if a plan ever tries to generate it. -/
def CtorSpec.typeFreshVars (argTypes : List HypothesisExpr)
    (funcResults : List (Name × HypothesisExpr)) (c : CtorSpec) : CtorSpec :=
  { c with vars := c.vars.map fun v =>
      if v.ty != (`_unknownType, []) then v
      else
        match c.conclusionArgs.zipIdx.find? (fun (a, _) => a == ConstructorExpr.Unknown v.name) with
        | some (_, j) => { v with ty := (argTypes[j]?).getD v.ty }
        | none =>
          match c.freshVarSource? v.name with
          | none => v
          | some fname =>
            match funcResults.find? (fun p => p.1 == fname) with
            | some (_, ty) => { v with ty := ty }
            | none => v }

/-- Reifies one constructor.

    Binders split into variables and premises by the pipeline's rule: a user-visible name (or an
    instance-implicit binder) makes a variable, an anonymous binder makes a premise. `∀ n m, n ≤ m → …`
    therefore yields variables `n`, `m` and the premise `n ≤ m`. -/
def extractCtorSpec (argTypes : List HypothesisExpr) (ctorName : Name) : MetaM CtorSpec := do
  let info ← getConstInfoCtor ctorName
  forallTelescopeReducing info.type (cleanupAnnotations := true) fun binders conclusion => do
    let mut vars : List VarSpec := []
    let mut hyps : List HypothesisExpr := []
    for b in binders do
      let decl ← b.fvarId!.getDecl
      if !decl.userName.hasMacroScopes || decl.binderInfo == .instImplicit then
        let ty := decl.type
        -- A **dictionary** binder carries no runtime value, exactly like a `Sort` binder, so it is
        -- recorded the same way. `MapNotContainsKey {α β} [DecidableEq α]` is the case that bites: left
        -- as an ordinary variable, a mode that happens to put its position among the outputs tries to
        -- *produce a dictionary*, and the schedule fails with "arity mismatch binding sub-producer
        -- results: 2 variable(s) [inst._@…, vrest] but 1 value(s)". Flagging it keeps it out of
        -- `producibleVars`, out of the non-linearity check, and holed out of the outputs.
        if ty.isSort || decl.binderInfo == .instImplicit then
          vars := vars ++ [{ name := decl.userName, ty := (`Sort, []), isSort := true }]
        else
          -- A binder type need not be a relation, so reification can legitimately fail (a function
          -- type, say). Record the variable anyway: only an `Unconstrained` step reads `ty`, and
          -- `InterpEnv.check` will name it if one does.
          let tyExpr ←
            try pure (← exprToHypothesisExpr ctorName ty)
            catch _ => pure (`_unreifiableType, [])
          vars := vars ++ [{ name := decl.userName, ty := tyExpr }]
      else
        hyps := hyps ++ [← exprToHypothesisExpr ctorName decl.type]
    let conclusionArgs ←
      (← conclusion.getAppArgs.toList.mapM exprToConstructorExpr).mapM retypeTypeApps
    -- Applied to premises and binder types too, not just the conclusion: a type misreported as a
    -- `FuncApp` in a premise would be counted as a value argument, throwing off arity, and one in a
    -- binder type would change the string a leaf generator is looked up under.
    let hyps' ← hyps.mapM retypeHyp
    let vars' ← vars.mapM fun v => do return { v with ty := ← retypeHyp v.ty }
    let linearized := CtorSpec.linearize
      { ctorName := ctorName, vars := vars', hypotheses := hyps', conclusionArgs := conclusionArgs }
    -- Resolve the result type of every function linearization lifted, so a fresh variable standing in
    -- for a nested subterm can be typed. Done here because it needs the environment.
    let lifted := linearized.vars.filterMap fun v =>
      if v.ty == (`_unknownType, []) then linearized.freshVarSource? v.name else none
    let mut funcResults : List (Name × HypothesisExpr) := []
    for fname in lifted.eraseDups do
      if let some ty ← funcResultType ctorName fname then
        funcResults := funcResults ++ [(fname, ty)]
    return CtorSpec.typeFreshVars argTypes funcResults linearized

/-- Reifies a whole inductive relation.

    `recFnName` defaults to `aux_<relation>`, distinct per relation so that several relations can be
    registered in one `InterpEnv`. A second *mode* of the same relation still needs a distinct name;
    `InterpEnv.deriveClosure` mints those. -/
def extractRelSpec (indName : Name) (argNames? : Option (List Name) := none) : MetaM RelSpec := do
  let info ← getConstInfoInduct indName
  let argTypes ← extractArgTypes indName
  let ctors ← info.ctors.mapM (extractCtorSpec argTypes)
  let arity ← forallTelescopeReducing info.type fun args _ => pure args.size
  let usedNames := ctors.flatMap (fun c => c.vars.map VarSpec.name)
  let argNames := argNames?.getD (mkArgNames usedNames arity)
  if argNames.length != arity then
    throwError "extractRelSpec: '{indName}' takes {arity} argument(s) but \
      {argNames.length} name(s) were given"
  return {
    inductiveName := indName
    argNames := argNames
    typeArgIndices := ← extractTypeArgIndices indName
    ctors := ctors
    recFnName := Name.mkSimple ("aux_" ++ shortIdent indName)
  }

/-! ## Rendering it as source

    Emitted with single-backtick, fully-qualified names: always parseable, and correct for a
    namespaced relation where a double-backtick short name would resolve differently at the paste
    site. -/

/-- A `Name` as Lean source that parses back to **the same name**.

    A backtick literal is used whenever one can spell the name. It cannot spell a *hygienic* name —
    `inst._@.Mod._hyg.3`, which is what an anonymous instance binder such as `[DecidableEq α]` is
    called — because such a name has numeric components and macro scopes. Those are emitted as an
    explicit `Name.str`/`Name.num` chain instead.

    The name is reproduced rather than sanitised: binders are matched by name across a constructor's
    `vars`, `hypotheses` and `conclusionArgs`, so renaming one occurrence would have to rename all of
    them, and reproducing it exactly makes that impossible to get wrong. This was a real bug: the literal
    did not reparse, so `derive_relspec` failed on Cedar's `MapNotContainsKey` and the relation was
    silently left out of the closure. -/
def srcName (n : Name) : String :=
  if n.hasMacroScopes || !(n.components.all (·.isStr)) then chain n
  else "`" ++ n.toString (escape := true)
where
  chain : Name → String
    | .anonymous => "Lean.Name.anonymous"
    | .str p str => s!"(Lean.Name.str {chain p} {repr str})"
    | .num p k => s!"(Lean.Name.num {chain p} {k})"

/-- A `ConstructorExpr` as Lean source. -/
partial def srcConstructorExpr : ConstructorExpr → String
  | .Unknown u => s!".Unknown {srcName u}"
  | .Lit (.natVal n) => s!".Lit (.natVal {n})"
  | .Lit (.strVal s) => s!".Lit (.strVal \"{s}\")"
  | .Ctor c args => s!".Ctor {srcName c} [{", ".intercalate (args.map srcConstructorExpr)}]"
  | .TyCtor c args => s!".TyCtor {srcName c} [{", ".intercalate (args.map srcConstructorExpr)}]"
  | .FuncApp f args => s!".FuncApp {srcName f} [{", ".intercalate (args.map srcConstructorExpr)}]"
  -- The level is irrelevant: a `CSort` argument is type-level, so `valueArgs` drops it.
  | .CSort _ => ".CSort .zero"
  | .Hole => ".Hole"

/-- A `HypothesisExpr` as Lean source. -/
def srcHypothesisExpr (h : HypothesisExpr) : String :=
  s!"({srcName h.1}, [{", ".intercalate (h.2.map srcConstructorExpr)}])"

/-- A `VarSpec` as Lean source. -/
def srcVarSpec (v : VarSpec) : String :=
  let sort := if v.isSort then ", isSort := true" else ""
  s!"\{ name := {srcName v.name}, ty := {srcHypothesisExpr v.ty}{sort} }"

/-- A `CtorSpec` as Lean source, one field per line. -/
def srcCtorSpec (c : CtorSpec) : String :=
  let field := fun (name : String) (items : List String) =>
    if items.isEmpty then "" else
      s!"\n      , {name} :=\n          [ " ++ "\n          , ".intercalate items ++ " ]"
  s!"\{ ctorName := {srcName c.ctorName}"
    ++ field "vars" (c.vars.map srcVarSpec)
    ++ field "hypotheses" (c.hypotheses.map srcHypothesisExpr)
    ++ field "conclusionArgs" (c.conclusionArgs.map srcConstructorExpr)
    ++ (if c.delegable.isEmpty then "" else
        s!"\n      , delegable := [{", ".intercalate (c.delegable.map srcName)}]")
    ++ " }"

/-- A `RelSpec` as pasteable Lean source, without the `def` header. -/
def srcRelSpec (r : RelSpec) : String :=
  let names := fun (ns : List Name) => "[" ++ ", ".intercalate (ns.map srcName) ++ "]"
  let typeArgs :=
    if r.typeArgIndices.isEmpty then "" else
      s!"\n  typeArgIndices := [{", ".intercalate (r.typeArgIndices.map toString)}]"
  s!"where\n  inductiveName := {srcName r.inductiveName}\n  argNames := {names r.argNames}"
    ++ typeArgs
    ++ s!"\n  recFnName := {srcName r.recFnName}\n  ctors :=\n    [ "
    ++ "\n    , ".intercalate (r.ctors.map srcCtorSpec)
    ++ " ]"

/-- A `RelSpec` as a complete `def`, ready to paste. -/
def srcRelSpecDef (defName : Name) (r : RelSpec) : String :=
  s!"def {defName} : Specimen.Interp.RelSpec {srcRelSpec r}"

/-! ## The commands -/

/-- The conventional name for an extracted spec: `bstRelSpec` for `BST`. -/
def defaultSpecName (indName : Name) : Name :=
  Name.mkSimple (shortIdent indName ++ "RelSpec")

/-- `#specimen_relspec R` logs a pasteable `RelSpec` literal for the inductive relation `R`.

    Read-only: it inspects the declaration and prints. Use `derive_relspec` to define the spec
    instead of printing it. -/
syntax (name := specimenRelSpecCmd) "#specimen_relspec " ident : command

@[command_elab specimenRelSpecCmd]
def elabSpecimenRelSpec : CommandElab := fun stx => do
  match stx with
  | `(#specimen_relspec $i:ident) => do
    let indName ← liftCoreM <| realizeGlobalConstNoOverload i
    let spec ← liftTermElabM <| extractRelSpec indName
    logInfo (srcRelSpecDef (defaultSpecName indName) spec)
  | _ => throwUnsupportedSyntax

/-- `derive_relspec R` defines `rRelSpec : RelSpec` for the inductive relation `R`;
    `derive_relspec R as myName` uses `myName` instead.

    The definition is produced by elaborating the same source `#specimen_relspec` prints, so what you
    get is what you would have pasted. -/
syntax (name := deriveRelSpecCmd) "derive_relspec " ident (" as " ident)? : command

@[command_elab deriveRelSpecCmd]
def elabDeriveRelSpec : CommandElab := fun stx => do
  match stx with
  | `(derive_relspec $i:ident $[as $nameOpt:ident]?) => do
    let indName ← liftCoreM <| realizeGlobalConstNoOverload i
    let spec ← liftTermElabM <| extractRelSpec indName
    let defName := match nameOpt with
      | some n => n.getId
      | none => defaultSpecName indName
    let src := srcRelSpecDef defName spec
    match Parser.runParserCategory (← getEnv) `command src "<derive_relspec>" with
    | .error e =>
      throwError "derive_relspec: the generated source did not parse ({e}). \
        Rendered source:\n{src}"
    | .ok cmd => elabCommand cmd
  | _ => throwUnsupportedSyntax

end Specimen.Interp
