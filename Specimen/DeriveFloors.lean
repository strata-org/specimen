import Specimen.MExp
import Specimen.Schedules
import Specimen.Debug

/-!
# Deriving a relation's floors

Under `specimen.deriveFloors`, each derived generator worker `W` gets `W.floor : inputs → Nat`, a lower
bound on the least size it can succeed at: over the rules whose input patterns match, the least of one, if the rule
calls the relation again, plus the floors of those calls at their inputs. Only a call on smaller inputs counts (each a variable
bound by the rule's input patterns, or an input passed on): the floor is a recursion on the inputs, linear
in their size, and every other call counts `0`, which keeps it a lower bound. The worker's split then guarantees each call its floor.

Two refinements, tried first (the plain floor above is the fallback):
* *Guards.* A rule's leading equation between what its inputs bind (a literal input index, which
  Specimen checks rather than matches: `h = 0`) restricts it as its patterns do, so a leaf rule no
  longer costs `0` at every input.
* *Relevance.* The floor depends only on some of its inputs: those a rule matches or guards on, and,
  transitively, those passed to such a position of a recursive call. A call counts when the arguments
  at those positions are bound; the others, perhaps values the rule drew, are irrelevant, and the
  floor is called there at its own inputs. So `BST lo k h l`, with `k` drawn, counts by `h`.
-/

open Lean Meta Elab Term

namespace Specimen.DeriveFloors

open Schedules MExp

/-- The variables a constructor expression mentions. -/
partial def ctorExprVars : ConstructorExpr → List Name
  | .Unknown u => [u]
  | .Ctor _ args | .FuncApp _ args | .TyCtor _ args => args.flatMap ctorExprVars
  | _ => []

/-- A rule's leading step, as its floor reads it: a match on what is bound, or an equation between
    what is bound, required to hold (`true`) or to fail. -/
inductive Lead where
  | mtch (explicit : Explicit) (scrutinee : Name) (pattern : Pattern)
  | guard (lhs rhs : ConstructorExpr) (holds : Bool)

/-- A rule's leading matches (and, with `guards`, equations) on its inputs, with what they bind and
    which of those are smaller than the inputs. A check the floor cannot read is passed over: leaving
    a restriction out keeps the floor a lower bound. -/
def readLeads (guards : Bool) (inputs : List Name) (steps : List ScheduleStep) :
    Array Lead × List Name × List Name := Id.run do
  let mut bound := inputs
  let mut smaller : List Name := []
  let mut ls : Array Lead := #[]
  for step in steps do
    match step with
    | .Match explicit scrutinee pattern =>
      unless bound.contains scrutinee do break
      ls := ls.push (.mtch explicit scrutinee pattern)
      bound := bound ++ patternVars pattern
      smaller := smaller ++ patternVars pattern
    | .Check (.NonRec (n, args)) holds =>
      if guards && n == ``Eq && args.length ≥ 2 then
        let lhs := args[args.length - 2]!
        let rhs := args[args.length - 1]!
        if (ctorExprVars lhs ++ ctorExprVars rhs).all bound.contains then
          ls := ls.push (.guard lhs rhs holds)
    | .Check .. => pure ()
    | _ => break
  return (ls, bound, smaller)

/-- The recursive calls of a rule: their arguments, at the floor's inputs. -/
def recCalls (steps : List ScheduleStep) : List (List ConstructorExpr) :=
  steps.filterMap fun
    | .Unconstrained _ (.Rec _ args) _ => some args
    | .SuchThat _ (.Rec _ args) _ => some args
    | _ => none

/-- The input positions the floor depends on (see the module docstring), or every position. -/
def relevantInputs (inputs : List Name) (rules : List (List ScheduleStep)) : List Nat := Id.run do
  let posOf (v : Name) : Option Nat := inputs.idxOf? v
  let mut rel : List Nat := []
  for steps in rules do
    let (ls, _, _) := readLeads true inputs steps
    for l in ls do
      let vs := match l with
        | .mtch _ s _ => [s]
        | .guard lhs rhs _ => ctorExprVars lhs ++ ctorExprVars rhs
      for v in vs do
        if let some i := posOf v then
          unless rel.contains i do rel := rel ++ [i]
  -- what a recursive call takes at a relevant position, transitively
  let mut changed := true
  while changed do
    changed := false
    for steps in rules do
      for args in recCalls steps do
        for j in rel do
          for v in ctorExprVars (args.getD j (.Lit (.natVal 0))) do
            if let some i := posOf v then
              unless rel.contains i do
                rel := rel ++ [i]; changed := true
  return rel

/-- The floor's definition, refined (`refined`: guards and relevance) or plain. -/
def floorCmd (indSched : InductiveSchedule) (w : Name) (inputs : List Name)
    (allBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (refined : Bool)
    (wf : Bool := false) : TermElabM (Array (TSyntax `command)) := do
  let key := indSched.key
  let floorId := mkIdent (w ++ `floor)
  let env ← getEnv
  let rules := (indSched.baseSchedules ++ indSched.recSchedules).map (·.2.1)
  let rel := (if refined then relevantInputs inputs rules else List.range inputs.length).mergeSort
  let binders := rel.toArray.filterMap fun j => allBinders[j]?
  let mut costs : Array (TSyntax `term) := #[]
  for steps in rules do
    let (ls, bound, smaller) := readLeads refined inputs steps
    let sized := countSizeConsumingCalls key.inductiveName steps
    let mut cost : TSyntax `term ← if sized > 0 then `(1) else `(0)
    for args in recCalls steps do
      -- Only a call on smaller inputs counts: its relevant arguments bound by the rule's inputs, one
      -- of them inside a pattern. The floor is then a recursion on the inputs, and a call at the
      -- inputs the rule was called at (a successor rule) counts `0`, which keeps it a lower bound.
      let relArgs := rel.filterMap fun j => args[j]?
      let ok := if refined then
          relArgs.all (fun a => (ctorExprVars a).all bound.contains) &&
          relArgs.any (fun a => (ctorExprVars a).any smaller.contains)
        else
          let vs := args.filterMap fun | .Unknown u => some u | _ => none
          vs.length == args.length && vs.all bound.contains && vs.any smaller.contains
      unless ok do continue
      let mut argStx : Array (TSyntax `term) := #[]
      for j in rel do
        let a := args.getD j (.Unknown inputs[j]!)
        let (stx, _) ← (mexpToTSyntax (constructorExprToMExp .allExplicit a) .Generator).run #[]
        argStx := argStx.push stx
      cost ← `($cost + $floorId $argStx*)
    let mut body : TSyntax `term ← `(some $cost)
    for l in ls.reverse do
      match l with
      | .mtch explicit scrutinee pattern =>
        let lhs ← compilePattern explicit pattern
        body ← if irrefutableErased env pattern then
            `(match $(mkIdent scrutinee):ident with | $lhs => $body)
          else
            `(match $(mkIdent scrutinee):ident with | $lhs => $body | _ => none)
      | .guard lhs rhs holds =>
        let (l, _) ← (mexpToTSyntax (constructorExprToMExp .allExplicit lhs) .Generator).run #[]
        let (r, _) ← (mexpToTSyntax (constructorExprToMExp .allExplicit rhs) .Generator).run #[]
        body ← if holds then `(if $l = $r then $body else none) else `(if $l = $r then none else $body)
    costs := costs.push body
  -- Named, not quoted: `minFloor` is not imported here, so a quoted reference would not resolve.
  let minFloor := mkIdent (Name.mkStr3 "Specimen" "SizeSplit" "minFloor")
  let argsId := mkIdent (w ++ `floorArgs)
  let relStx : Array (TSyntax `term) ← rel.toArray.mapM fun j => `($(Syntax.mkNumLit (toString j)))
  let relIds : Array Ident := rel.toArray.filterMap fun j => inputs[j]?.map mkIdent
  -- Well-founded recursion on the relevant inputs (`wf`), where Lean cannot state the structural
  -- recursion's equations (several matches on one input, say).
  let defCmd ← if wf && !relIds.isEmpty then
      let mut measure : TSyntax `term ← `($(relIds.back!))
      for x in relIds.pop.reverse do measure ← `(($x, $measure))
      `(command| def $floorId:ident $binders:bracketedBinder* : Nat := $minFloor [$costs,*]
          termination_by $measure:term)
    else `(command| def $floorId:ident $binders:bracketedBinder* : Nat := $minFloor [$costs,*])
  return #[defCmd, ← `(command| def $argsId:ident : List Nat := [$relStx,*])]

/-- The floor function `w.floor` for the schedule `indSched`, with `w.floorArgs`, the input positions
it takes, as candidates to try in turn (refined, then plain), or `none` where the relation has type
parameters. Its fallback, the constant `0` at every input, is the second component. -/
def floorCmds (indSched : InductiveSchedule) (w : Name) :
    TermElabM (Option (Array (Array (TSyntax `command)) × Array (TSyntax `command))) := do
  let key := indSched.key
  let indInfo ← getConstInfoInduct key.inductiveName
  forallTelescopeReducing indInfo.type fun xs _ => do
    let argNames := (List.range xs.size).map fun i => indSched.argNames.getD i (Name.mkSimple s!"arg_{i}")
    let mut binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    let mut inputs : List Name := []
    for i in [:xs.size] do
      let ty ← inferType xs[i]!
      if ty.isSort then return none
      if key.outputIndices.contains i then continue
      let n := argNames[i]!
      inputs := inputs ++ [n]
      binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent n) : $(← PrettyPrinter.delab ty))))
    let refined ← floorCmd indSched w inputs binders true
    let refinedWF ← floorCmd indSched w inputs binders true (wf := true)
    let plain ← floorCmd indSched w inputs binders false
    let floorId := mkIdent (w ++ `floor)
    let argsId := mkIdent (w ++ `floorArgs)
    let all : Array (TSyntax `term) ← (List.range inputs.length).toArray.mapM fun j =>
      `($(Syntax.mkNumLit (toString j)))
    let fallback := #[← `(command| def $floorId:ident $binders:bracketedBinder* : Nat := 0),
      ← `(command| def $argsId:ident : List Nat := [$all,*])]
    return some (#[refined, refinedWF, plain], fallback)

end Specimen.DeriveFloors
