import Specimen.Debug
import Specimen.Correctness.ReachClose
import Specimen.Correctness.SplitLaws
import Specimen.Correctness.StepOf

/-!
# A derived worker is complete for its relation

`#specimen_complete [W for R outputs [i, …]]` states and proves, for a derived generator worker `W` of
relation `R` in the mode producing `R`'s arguments `i, …`,

  `W.complete : ∀ args, R args → ∃ n m, ∀ fuel iS sz, n ≤ sz → sz < fuel → m ≤ iS →
    Produces (W fuel iS sz ins) outs`

by induction on the derivation. In each case: the induction hypotheses' bounds give the size bound
(`K · Σ nᵢ + 1`, `K` more than the constructor's premises, so that any share of the size a call is
handed covers its bound); the reach walk over the worker's body leaves the choices; and `reach_close`
makes them, taking the calls' values from the hypotheses, the delegated producers' and the
unconstrained draws' from their `BacktrackGenForComplete` and `ArbitrarySizedComplete` instances, and
choosing the bound on `initSize` last, as the sum of what they need.
-/

open Lean Meta Elab Tactic Term Command

namespace Specimen.Correctness

/-- The case of a derivation, for worker `w`: see the module docstring. -/
syntax "specimen_complete_case " "[" ident,* "]" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| specimen_complete_case [$ws,*] $[[$facts,*]]?) => withMainContext do
    -- The recursor's cases state their motives unreduced.
    evalTactic (← `(tactic| try dsimp only at *))
    let tgt ← instantiateMVars (← getMainTarget)
    let some w := ws.getElems.find? fun w => (tgt.find? (·.isConstOf w.getId)).isSome
      | throwError "specimen_complete_case: no worker of the block in{indentExpr tgt}"
    -- The induction hypotheses, taken apart.
    let mut ns : Array Ident := #[]
    let mut k := 1
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      k := k + 1
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``Exists 2 then
        let n := mkIdent (← mkFreshUserName `n)
        let m := mkIdent (← mkFreshUserName `m)
        let h := mkIdent (← mkFreshUserName `ih)
        evalTactic (← `(tactic| obtain ⟨$n, $m, $h⟩ := $(mkIdent d.userName)))
        ns := ns.push n
    let _ := ns
    let _ := k
    let eqBody := mkIdent (w.getId ++ `eq_body)
    let body := mkIdent (w.getId ++ `body)
    -- The bounds on the size and on `initSize` are chosen last, by `reach_close`, as what the
    -- choices need.
    evalTactic (← `(tactic|
      (refine ⟨?_ + 1, ?_, fun fuel iS sz hn hf hm => ?_⟩
       on_goal 3 => (
       cases fuel with
       | zero => exact absurd hf (Nat.not_lt_zero _)
       | succ f =>
       cases sz with
       | zero => exact absurd hn (Nat.not_succ_le_zero _)
       | succ s =>
       have hn := Nat.le_of_succ_le_succ hn
       refine produces_of_reach ?_
       rw [$eqBody:ident]
       delta $body:ident
       walk
       all_goals reach_close $[[$facts,*]]?))))
    -- The bounds nothing needed.
    for g in ← getUnsolvedGoals do
      if (← instantiateMVars (← g.getType)).isConstOf ``Nat && !(← g.isAssigned) then
        g.assign (mkNatLit 0)
    setGoals (← (← getUnsolvedGoals).filterM fun g => return !(← g.isAssigned))

/-- The statement of `w.complete`. -/
def completeStatement (wN rN : Name) (outIdx : Array Nat) : TermElabM Expr := do
  -- The worker draws at `Type`, so a universe-polymorphic relation is taken there.
  let rC := Lean.mkConst rN ((← getConstInfo rN).levelParams.map fun _ => levelZero)
  let wC ← mkAppOptM wN #[some (Lean.mkConst ``SGen), none, none, none, none, none, none]
  forallTelescopeReducing (← inferType rC) fun xs _ => do
    let rApp := mkAppN rC xs
    Meta.check rApp
    let ins := (Array.range xs.size).filterMap fun i => if outIdx.contains i then none else some xs[i]!
    let outs := outIdx.map (xs[·]!)
    let outT ← match outs.toList.reverse with
      | [] => throwError "#specimen_complete: no outputs"
      | o :: os => os.foldlM (fun acc x => mkAppM ``Prod.mk #[x, acc]) o
    let nat := Lean.mkConst ``Nat
    let body ← withLocalDeclD `n nat fun n => withLocalDeclD `m nat fun m =>
      withLocalDeclD `fuel nat fun fuel => withLocalDeclD `iS nat fun iS => withLocalDeclD `sz nat fun sz => do
        let prod ← mkAppM ``Produces #[mkAppN wC (#[fuel, iS, sz] ++ ins), outT]
        let p ← mkArrow (← mkAppM ``LE.le #[n, sz]) (← mkArrow (← mkAppM ``LT.lt #[sz, fuel])
          (← mkArrow (← mkAppM ``LE.le #[m, iS]) prod))
        let inner ← mkForallFVars #[fuel, iS, sz] p
        let em ← mkAppM ``Exists #[← mkLambdaFVars #[m] inner]
        mkAppM ``Exists #[← mkLambdaFVars #[n] em]
    let st ← mkForallFVars xs (← mkArrow (← instantiateMVars rApp) body)
    instantiateMVars st

/-- Prove `w` complete for `r` at outputs `outIdx`, as `w.complete`. -/
theorem complete_spec {Q : Nat → Nat → Prop} (h : ∃ n m, Q n m) :
    Q (Classical.choose h) (Classical.choose (Classical.choose_spec h)) :=
  Classical.choose_spec (Classical.choose_spec h)

/-- `w.complete`, its bounds chosen: `w.completeSpec : ∀ args, R args → ∀ fuel iS sz, … → Produces …`,
a fact a later worker's proof applies. -/
def addCompleteSpec (wN : Name) : TermElabM Unit := do
  let c ← mkConstWithFreshMVarLevels (wN ++ `complete)
  let ty ← inferType c
  let (v, t) ← forallTelescope ty fun xs _ => do
    let e ← mkAppM ``complete_spec #[mkAppN c xs]
    return (← mkLambdaFVars xs e, ← mkForallFVars xs (← inferType e))
  let t ← instantiateMVars t
  let v ← instantiateMVars v
  addDecl <| .thmDecl { name := wN ++ `completeSpec, levelParams := [], type := t, value := v }

def proveComplete (wN rN : Name) (outIdx : Array Nat) (facts : Array Name := #[]) : TermElabM Unit := do
  specimenBody wN
  let stmt ← completeStatement wN rN outIdx
  let fs : Array Term := facts.map fun f => ⟨mkIdent f⟩
  let tac ← `(by
    intros
    rename_i h
    induction h <;> specimen_complete_case [$(mkIdent wN)] [$fs,*])
  -- A case that does not close is an error thrown, not one logged with a `sorry` left in its place.
  let pf ← Term.withoutErrToSorry do
    let pf ← elabTermEnsuringType tac stmt
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars pf
  if pf.hasMVar || pf.hasSorry then throwError "the proof did not close"
  addDecl <| .thmDecl { name := wN ++ `complete, levelParams := [], type := stmt, value := pf }
  addCompleteSpec wN

/-- Prove the workers of a block over a mutual inductive complete together: each theorem is the
inductive's recursor at motives the block's statements, so that its cases see the hypotheses for every
inductive of the block, and each case is closed as `induction`'s are. -/
def proveCompleteMutual (items : Array (Name × Name × Array Nat)) (facts : Array Name := #[]) :
    TermElabM Unit := do
  for (w, _, _) in items do specimenBody w
  let stmts ← items.mapM fun (w, r, is) => completeStatement w r is
  let (_, r₀, _) := items[0]!
  let ind₀ ← getConstInfoInduct r₀
  let group := ind₀.all
  unless group.length == items.size && group.all (fun n => (items.filter (·.2.1 == n)).size == 1) do
    throwError "the block is not one mode of each inductive of a mutual group"
  let wsStx : Array Ident := items.map (mkIdent ·.1)
  let fs : Array Term := facts.map fun f => ⟨mkIdent f⟩
  let caseTac ← `(tactic| (intros; specimen_complete_case [$wsStx,*] [$fs,*]))
  for i in [:items.size] do
    let (wN, rN, _) := items[i]!
    let stmt := stmts[i]!
    let g ← mkFreshExprMVar stmt .syntheticOpaque
    let nArgs ← forallTelescope (← inferType (Lean.mkConst rN)) fun xs _ => pure xs.size
    let (fvs, g') ← g.mvarId!.introN (nArgs + 1)
    let ind ← getConstInfoInduct rN
    let params := (fvs.extract 0 ind.numParams).map Expr.fvar
    let motives ← g'.withContext <| group.toArray.mapM fun J => do
      let some j := items.findIdx? (·.2.1 == J) | throwError "no worker for {J}"
      let sj ← instantiateForall stmts[j]! params
      forallTelescope sj fun xs b => mkLambdaFVars xs b
    let rec_ ← mkConstWithFreshMVarLevels (rN ++ `rec)
    let gs ← g'.withContext <| g'.apply (mkAppN rec_ (params ++ motives))
    -- The statement does not mention the derivation, so the recursor's major premise is left; it is
    -- the derivation introduced.
    let major := Expr.fvar fvs.back!
    for mg in gs do
      if ← mg.isAssigned then continue
      if ← g'.withContext (do isDefEq (← mg.getType) (← inferType major)) then mg.assign major
    for mg in gs do
      if ← mg.isAssigned then continue
      let rest ← Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.run mg (evalTactic caseTac)
      unless rest.isEmpty do throwError "{wN}: a case did not close"
    let pf ← instantiateMVars g
    if pf.hasMVar || pf.hasSorry then throwError "{wN}: the proof did not close"
    addDecl <| .thmDecl { name := wN ++ `complete, levelParams := [], type := stmt, value := pf }
    addCompleteSpec wN

/-- The derived `BacktrackGenFor` instance that runs `w`, with its class arguments. -/
def instanceOf (wN : Name) : MetaM (Option (Name × Expr)) := do
  let st := Meta.instanceExtension.getState (← getEnv)
  for (n, _) in st.instanceNames do
    let some ci := (← getEnv).find? n | continue
    let ty := ci.type
    unless ty.getForallBody.getAppFn.isConstOf ``BacktrackGenFor do continue
    let some v := ci.value? | continue
    if (v.find? fun e => e.isConstOf wN).isSome then return some (n, ty)
  return none

/-- `BacktrackGenForComplete` for `w`'s instance, from `w.complete`: the instance runs `w` at fuel
`size + 1` (`specimen.emitComplete`). -/
def proveInstComplete (wN : Name) (nArgs nOut : Nat) : TermElabM Unit := do
  let some (instN, instTy) ← instanceOf wN | throwError "no BacktrackGenFor instance runs {wN}"
  -- The instance's parameters are the worker's inputs.
  let goal ← forallTelescopeReducing instTy fun ps body => do
    let α := body.appFn!.appArg!
    let P := body.appArg!
    mkForallFVars ps (← mkAppOptM ``BacktrackGenForComplete #[α, P, mkAppN (Lean.mkConst instN) ps])
  let nParams := instTy.getNumHeadForalls
  -- Built as text: the output's pattern and the worker's arguments are plain names.
  let outs := String.intercalate ", " ((List.range nOut).map fun i => s!"o{i}")
  let pat := if nOut == 1 then "o0" else s!"⟨{outs}⟩"
  let holes := String.intercalate " " (List.replicate nArgs "_")
  let src := s!"by\n  intros\n  refine ⟨fun x hx => ?_⟩\n  obtain {pat} := x\n  obtain ⟨n, m, h⟩ := @{wN ++ `complete} {holes} hx\n  exact ⟨n + m, fun s l hs hl => h (s + 1) l s (by omega) (by omega) (by omega)⟩"
  let tac ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok stx => pure stx
    | .error e => throwError "instance proof: {e}"
  let _ := nParams
  let pf ← elabTermEnsuringType tac goal
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  if pf.hasMVar then throwError "the instance's proof did not close"
  let name := wN ++ `instComplete
  addDecl <| .thmDecl { name, levelParams := [], type := goal, value := pf }
  addInstance name .global (eval_prio default)

/-- The workers proved complete so far, for the facts of the next. -/
initialize completedRef : IO.Ref (Array Name) ← IO.mkRef #[]

initialize specimenCompleteHook.set <| some fun gens => do
  if gens.size > 1 then
    try
      let facts ← completedRef.get
      liftTermElabM do
        let env ← getEnv
        proveCompleteMutual (gens.map fun (w, r, is) => (w, r, is.toArray)) (facts.filter (env.contains ·))
        for (w, r, is) in gens do
          let nArgs ← forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels r)) fun xs _ => pure xs.size
          proveInstComplete w nArgs is.length
      for (w, _, _) in gens do completedRef.modify (·.push (w ++ `completeSpec))
    catch e =>
      logWarning m!"specimen.emitComplete: the block \
        {", ".intercalate (gens.toList.map (toString ·.1))} not proved complete: {e.toMessageData}"
    return
  for (w, r, is) in gens do
    try
      let t0 ← IO.monoMsNow
      let facts ← completedRef.get
      liftTermElabM do
        let env ← getEnv
        proveComplete w r is.toArray (facts.filter (env.contains ·))
        let nArgs ← forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels r)) fun xs _ => pure xs.size
        proveInstComplete w nArgs is.length
      completedRef.modify (·.push (w ++ `completeSpec))
      if Lean.Option.get (← getOptions) specimen.reportPhaseTimers then
        logInfo m!"specimen.emitComplete: {w} complete ({(← IO.monoMsNow) - t0} ms)"
    catch e =>
      logWarning m!"specimen.emitComplete: {w} not proved complete: {e.toMessageData}"

syntax completeItem := ident " for " ident " outputs " "[" num,* "]"
syntax "#specimen_complete " "[" completeItem,* "]" : command

elab_rules : command
  | `(#specimen_complete [$items,*]) => liftTermElabM do
    for it in items.getElems do
      let `(completeItem| $w:ident for $r:ident outputs [$is,*]) := it | throwError "bad item"
      let wN ← realizeGlobalConstNoOverloadWithInfo w
      let rN ← realizeGlobalConstNoOverloadWithInfo r
      let outIdx := is.getElems.map (·.getNat)
      proveComplete wN rN outIdx
      let nArgs ← forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels rN)) fun xs _ => pure xs.size
      if (← getOptions).getBool `specimen.emitComplete then
        proveInstComplete wN nArgs outIdx.size

end Specimen.Correctness
