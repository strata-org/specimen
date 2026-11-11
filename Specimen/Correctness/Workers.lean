import Specimen.Correctness.CompleteOf

/-! Derived workers by what they derive rather than by name: `worker% gen R [i, …]`, the worker of sort
`gen` for relation `R` at outputs `i, …` (its laws too, `worker% gen R [i] sound`), and tactics and
commands over them. Which declarations are workers, and of what, is the derivation's record
(`Specimen.WorkerRegistry`). -/
open Lean Elab Term Meta

namespace Specimen

/-- The derived worker of sort `sort` (`gen`, `enum`, `check`) for relation `rel` at outputs `is`: the
one declared in namespace `ns?` if given; otherwise the one whose instance is visible here (global, or
scoped to the current namespace or an open one, or local to this file), and if several are, the one
declared in the current namespace. An error if none is, or several. -/
def resolveWorker (sort : String) (rel : Name) (is : List Nat) (ns? : Option Name := none) :
    MetaM Name := do
  let some sort' := (match sort with
      | "gen" => some Schedules.DeriveSort.Generator | "enum" => some .Enumerator
      | "check" => some .Checker | _ => none)
    | throwError "unknown worker sort {sort}: expected gen, enum or check"
  let currNs ← getCurrNamespace
  let opened := (← getOpenDecls).filterMap fun | .simple ns _ => some ns | _ => none
  let mainMod ← getMainModule
  let all : Array (Name × WorkerInfo) := (derivedWorkers (← getEnv)).filter fun (_, i) =>
    i.sort == sort' && i.rel == rel && i.outs == is
  let visible : Array (Name × WorkerInfo) := match ns? with
    | some ns => all.filter fun (w, _) => w.getPrefix == ns
    | none => all.filter fun (_, i) => i.visibility.visibleIn currNs opened mainMod
  let wheres := all.toList.map fun (w, _) => w.getPrefix
  match visible.toList, (visible.filter fun (w, _) => w.getPrefix == currNs).toList with
  | [(w, _)], _ => return w
  | _, [(w, _)] => return w
  | [], _ =>
    if all.isEmpty then throwError "no derived {sort} worker for {rel} at outputs {is}"
    else throwError "no derived {sort} worker for {rel} at outputs {is} is visible here; there are \
      ones declared in {wheres}: open one's namespace, or name it, `worker% (ns := N) …`"
  | ws, _ => throwError "several derived {sort} workers for {rel} at outputs {is} are visible here, \
      declared in {ws.map fun (w, _) => w.getPrefix}: name one, `worker% (ns := N) …`"

syntax workerSort := &"gen" <|> &"enum" <|> &"check"
/-- `(ns := N)`: the worker declared in namespace `N`. -/
syntax workerNs := "(" &"ns" " := " ident ")"
/-- A derived worker by what it derives: `gen R [i, …]`, optionally `(ns := N) gen R [i, …]`. -/
syntax workerRef := (workerNs)? workerSort ident " [" num,* "]"

/-- The worker a `workerRef` names, or its law `law?`. -/
def workerName (ref : Syntax) (law? : Option Syntax) : TermElabM Name := do
  let rec firstAtom : Syntax → String
    | .atom _ v => v
    | .ident _ _ n _ => n.toString
    | .node _ _ args => args.foldl (fun acc a => if acc.isEmpty then firstAtom a else acc) ""
    | _ => ""
  let ns? := if ref[0].isNone then none else some ref[0][0][3].getId
  let rel ← realizeGlobalConstNoOverloadWithInfo ref[2]
  let w ← resolveWorker (firstAtom ref[1]).trimAscii.toString rel
    (ref[4].getSepArgs.toList.map fun a => a.isNatLit?.getD 0) ns?
  let some law := law? | return w
  -- a law may be a reserved name (`eq_def`), realized on first use
  realizeGlobalConstNoOverload (mkIdent (w ++ law.getId))

/-- `worker% gen R [i, …]`: the worker Specimen derived for `R` producing the outputs `i, …`, its
implicit arguments from the expected type or given by name (`(G := SGen)`); `worker% gen R [i, …] law`
its law `law` (`sound`, `complete`, `eq_def`, …). -/
syntax (name := workerTerm) "worker% " workerRef (ident)? (Lean.Parser.Term.namedArgument)* : term

@[term_elab workerTerm] def elabWorker : TermElab := fun stx expectedType? => do
  let n ← workerName stx[1] (if stx[2].isNone then none else some stx[2][0])
  let named ← stx[3].getArgs.mapM fun a => do
    return ({ name := a[1].getId.eraseMacroScopes, val := .stx a[3] } : NamedArg)
  elabAppArgs (← mkConstWithFreshMVarLevels n) named #[] expectedType? (explicit := false)
    (ellipsis := false)

/-- `delta_worker gen R [i, …] law`: `delta` the worker's declaration `law` (its `body`, say). -/
syntax (name := deltaWorker) "delta_worker " workerRef (ident)? : tactic

@[tactic deltaWorker] def evalDeltaWorker : Tactic.Tactic := fun stx => do
  let n ← Tactic.withMainContext <| workerName stx[1] (if stx[2].isNone then none else some stx[2][0])
  Tactic.evalTactic (← `(tactic| delta $(mkIdent n):ident))


/-- `unfold_worker gen R [i, …]`: `unfold` that worker. -/
syntax (name := unfoldWorker) "unfold_worker " workerRef : tactic

@[tactic unfoldWorker] def evalUnfoldWorker : Tactic.Tactic := fun stx => do
  let n ← Tactic.withMainContext <| workerName stx[1] none
  Tactic.evalTactic (← `(tactic| unfold $(mkIdent n):ident))

/-- `#specimen_body_of gen R [i, …]`: `#specimen_body` for that worker. -/
syntax (name := specimenBodyOf) "#specimen_body_of " workerRef : command

@[command_elab specimenBodyOf] def elabSpecimenBodyOf : Command.CommandElab := fun stx => do
  let w ← Command.liftTermElabM <| workerName stx[1] none
  let some cmd := (Parser.runParserCategory (← getEnv) `command s!"#specimen_body {w}").toOption
    | throwError "#specimen_body_of: could not state `#specimen_body {w}`"
  Command.elabCommand cmd

/-- `unfold_worker_step`: open the derived worker the goal is about, at `fuel + 1`, into its body
(`rw [w.eq_body]; delta w.body`), whichever worker it is. -/
syntax (name := unfoldWorkerStep) "unfold_worker_step" : tactic

@[tactic unfoldWorkerStep] def evalUnfoldWorkerStep : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let env ← getEnv
  let some w := (← instantiateMVars (← Tactic.getMainTarget)).find? (fun e =>
      match e.getAppFn.constName? with
      | some c => isDerivedWorker env c [.Generator, .Enumerator]
      | none => false) |>.bind (·.getAppFn.constName?)
    | throwError "unfold_worker_step: no derived worker in the goal"
  unless env.contains (w ++ `eq_body) do Specimen.Correctness.specimenBody w
  Tactic.evalTactic (← `(tactic| (rw [$(mkIdent (w ++ `eq_body)):ident]; delta $(mkIdent (w ++ `body)):ident)))

open Lean Meta Elab Command in
/-- `#specimen_prepare_proofs`: for the workers this file derived, what the proofs about them use,
made once here rather than by each file that needs it: their bodies (`body`, `eq_body`), the
congruence equations of the matchers the bodies use (made in two files imported together, their
auxiliary declarations would clash), and their unfolding equations. -/
elab "#specimen_prepare_proofs" : command => do
  let ws : List (Name × WorkerInfo) := specimenWorkerExt.getEntries (← getEnv)
  let t0 ← IO.monoMsNow
  -- bodies for the generators and enumerators; a checker's body is not needed
  let bodied := ws.filterMap fun (w, i) => if i.sort == .Checker then none else some w
  liftTermElabM do
    for w in bodied do
      try Specimen.Correctness.specimenBody w catch _ => pure ()
  let env ← getEnv
  -- the matchers this file declares in the workers' namespaces
  let nss := ws.map (·.1.getPrefix) |>.eraseDups
  let ms := env.constants.map₂.toList.filterMap fun (n, _) =>
    if nss.any (·.isPrefixOf n) && Lean.Meta.isMatcherCore env n then some n else none
  let k ← liftTermElabM do
    for m in ms do
      try discard <| Lean.Meta.Match.genMatchCongrEqns m catch _ => pure ()
    let mut k : Nat := 0
    for (w, _) in ws do
      try
        if (← getUnfoldEqnFor? w (nonRec := true)).isSome then k := k + 1
      catch _ => pure ()
    return k
  logInfo m!"{ws.length} workers: {bodied.length} bodies, {ms.length} matchers, {k} unfolding equations, in {(← IO.monoMsNow) - t0} ms"

end Specimen
