import Specimen.Debug
import Specimen.Correctness.ReachClose
import Specimen.Correctness.LeafComplete
import Specimen.Correctness.SplitLaws
import Specimen.Correctness.StepOf
import Specimen.Correctness.ParallelBlock
import Specimen.Correctness.EnumCompleteOf
import Specimen.Correctness.CheckSoundOf
import Specimen.Correctness.LeafLaws

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

/-- A derived checker's worker (`Except GenError Bool`, not a `Gen` program). -/
def isCheckerWorker (env : Environment) (w : Name) : Bool := Specimen.isDerivedWorker env w [.Checker]

/-- A derived enumerator's worker. -/
def isEnumWorker (env : Environment) (w : Name) : Bool := Specimen.isDerivedWorker env w [.Enumerator]

/-- The case of a derivation, for worker `w`: see the module docstring. -/
syntax "specimen_complete_case " "[" ident,* "]" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| specimen_complete_case [$ws,*] $[[$facts,*]]?) => withMainContext do
    -- The recursor's cases state their motives unreduced.
    evalTactic (← `(tactic| log_time "dsimp" (try dsimp only at *)))
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
    -- The plain search first; a case it does not close is searched again with what costs more:
    -- each premise equating a variable with a term substituted (`s' = addBucket n s`, so that the
    -- choices meet the value the generator computes from it), and `specimen.reachExtended`. The
    -- cases the plain search closes pay nothing for either.
    let attempt (tac : TSyntax `tactic) : TacticM Unit := do
      let saved ← saveState
      try
        Term.withoutErrToSorry <| Tactic.withoutRecover <| evalTactic tac
      catch _ =>
        saved.restore
        evalTactic (← `(tactic| log_time "subst" (try subst_vars)))
        withOptions (specimen.reachExtended.set · true) (evalTactic tac)
    if isCheckerWorker (← getEnv) w.getId then
      -- A checker accepts: its body unfolded, its combinators read as what they accept (a branch
      -- of `checkerBacktrack`, every premise of `andOptList`, the flip of `negOpt`), and the
      -- verdicts, the searches and the calls left to `reach_close`, as a generator's choices are.
      attempt (← `(tactic|
        (refine ⟨?_ + 1, ?_, fun fuel iS sz hn hf hm => ?_⟩
         on_goal 3 => (
         cases fuel with
         | zero => exact absurd hf (Nat.not_lt_zero _)
         | succ f =>
         cases sz with
         | zero => exact absurd hn (Nat.not_succ_le_zero _)
         | succ s =>
         have hn := Nat.le_of_succ_le_succ hn
         log_time "unfold" (unfold $w:ident)
         log_time "simp" (try simp only [Specimen.Correctness.checkerBacktrack_ok_true,
           Specimen.Correctness.andOptList_ok_true, Specimen.Correctness.negOpt_ok, List.mem_cons,
           List.mem_nil_iff, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq,
           and_true, Bool.not_true, Bool.not_false])
         log_time "closeall" (all_goals reach_close $[[$facts,*]]?)
         log_time "bounds" reach_close_bounds))))
      for g in ← getUnsolvedGoals do
        if (← instantiateMVars (← g.getType)).isConstOf ``Nat && !(← g.isAssigned) then
          g.assign (mkNatLit 0)
      setGoals (← (← getUnsolvedGoals).filterM fun g => return !(← g.isAssigned))
      return
    let eqBody := mkIdent (w.getId ++ `eq_body)
    let body := mkIdent (w.getId ++ `body)
    -- a check's verdict, and a checker of the block's, decided by `reach_close`, not split on
    let env ← getEnv
    let checkers := ws.getElems.filter (isCheckerWorker env ·.getId) |>.map (·.getId.toString)
    let keepStr := Syntax.mkStrLit (",".intercalate ("DecOpt.decOpt" :: checkers.toList))
    -- (`specimen.completeDropUnreachable`: branches that cannot return the case's value are not
    -- walked)
    let walkTac ← if specimen.completeDropUnreachable.get (← getOptions) then
        `(tactic| set_option basalt.walk.dropUnreachable true in
          set_option basalt.walk.failHeads
            "Specimen.Fail.fail,Specimen.FailWith.failWith,Specimen.outOfFuel,Specimen.truncated" in
          set_option basalt.walk.choiceHeads "Specimen.Backtrack.backtrack" in walk)
      else `(tactic| walk)
    -- The bounds on the size and on `initSize` are chosen last, by `reach_close`, as what the
    -- choices need.
    attempt (← `(tactic|
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
       log_time "rwdelta" (rw [$eqBody:ident]; delta $body:ident)
       -- a check's verdict is decided by `reach_close` from the check's law, not split on
       log_time "walk" (set_option basalt.walk.keepMatchesOn $keepStr in $walkTac:tactic)
       log_time "closeall" (all_goals reach_close $[[$facts,*]]?)
       log_time "bounds" reach_close_bounds))))
    -- The bounds nothing needed.
    for g in ← getUnsolvedGoals do
      if (← instantiateMVars (← g.getType)).isConstOf ``Nat && !(← g.isAssigned) then
        g.assign (mkNatLit 0)
    setGoals (← (← getUnsolvedGoals).filterM fun g => return !(← g.isAssigned))

/-- The worker's arguments after `fuel initSize size`, given the relation's inputs `ins`: each explicit
argument the next input, and each instance argument (a polymorphic relation's `DecidableEq α`, say) a new
hypothesis, which `k` receives with the arguments. -/
partial def workerArgs {α} (ty : Expr) (ins : List Expr) (acc insts : Array Expr)
    (k : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  match ← whnf ty with
  | .forallE n t b bi =>
    if bi.isInstImplicit then
      -- an instance the relation's own arguments provide (its `[DecidableEq α]`) is that one: the
      -- worker's recursive calls pass it, and a second hypothesis of the same class would not unify
      if let some i ← (try synthInstance? t catch _ => pure none) then
        if i.isFVar then return ← workerArgs (b.instantiate1 i) ins (acc.push i) insts k
      withLocalDecl n .instImplicit t fun h => workerArgs (b.instantiate1 h) ins (acc.push h) (insts.push h) k
    else
      match ins with
      | x :: xs =>
        unless ← isDefEq t (← inferType x) do
          throwError "#specimen_complete: the worker's argument {n} : {t} is not the relation's input {x}"
        workerArgs (b.instantiate1 x) xs (acc.push x) insts k
      | [] => k acc insts
  | _ => k acc insts

/-- `k` under a hypothesis, for each instance in `insts` that draws a type parameter
(`[Basalt.ArbitrarySized α]`), that the draw is complete (`[ArbitrarySizedComplete α]`). -/
def withDrawLaws {β} (insts : Array Expr) (k : Array Expr → MetaM β) (searches : Bool := false) :
    MetaM β := do
  let rec go (i : Nat) (laws : Array Expr) : MetaM β := do
    if h : i < insts.size then
      let x := insts[i]
      let ty ← inferType x
      if ty.isAppOfArity ``Basalt.ArbitrarySized 1 then
        let lawTy ← mkAppOptM ``ArbitrarySizedComplete #[ty.appArg!, x]
        withLocalDecl `law .instImplicit lawTy fun l => do
          -- a checker searches for its witnesses, through the draws' searches: their hits too
          if searches then
            let hitsTy ← mkAppOptM ``ArbitrarySizedHits #[ty.appArg!, x]
            withLocalDecl `lawHits .instImplicit hitsTy fun lh => go (i + 1) (laws.push l |>.push lh)
          else go (i + 1) (laws.push l)
      else go (i + 1) laws
    else k laws
  go 0 #[]

/-- `e` with every universe metavariable still unassigned at `0`: the levels its unification with the
worker's arguments did not fix. -/
def defaultLevelMVars (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  return e.replaceLevel fun l => some (l.replace fun l' => if l'.isMVar then some .zero else none)

/-- A checker's statement: `∀ args [insts], R args → ∃ n m, ∀ fuel iS sz, … → W fuel iS sz args = .ok true`,
every argument of the relation an input. -/
def checkCompleteStatement (wN rN : Name) : TermElabM Expr := do
  -- The relation's universes fixed by the worker's arguments (`Sort u` taken at `Type` where the worker
  -- draws its values, not at `Prop`), the rest at `0`.
  let rC ← mkConstWithFreshMVarLevels rN
  -- (the worker's own universes alike: a type parameter it generalized to `Sort u` is the relation's)
  let wC ← mkConstWithFreshMVarLevels wN
  forallTelescopeReducing (← inferType rC) fun xs _ => do
    let rApp := mkAppN rC xs
    let nat := Lean.mkConst ``Nat
    let wTy ← instantiateForall (← inferType wC) #[mkNatLit 0, mkNatLit 0, mkNatLit 0]
    workerArgs wTy xs.toList #[] #[] fun wargs insts => do
      let body ← withLocalDeclD `n nat fun n => withLocalDeclD `m nat fun m =>
        withLocalDeclD `fuel nat fun fuel => withLocalDeclD `iS nat fun iS => withLocalDeclD `sz nat fun sz => do
          let run := mkAppN wC (#[fuel, iS, sz] ++ wargs)
          let okT ← mkAppOptM ``Except.ok #[Lean.mkConst ``Plausible.GenError, Lean.mkConst ``Bool, Lean.mkConst ``Bool.true]
          let acc ← mkEq run okT
          let p ← mkArrow (← mkAppM ``LE.le #[n, sz]) (← mkArrow (← mkAppM ``LT.lt #[sz, fuel])
            (← mkArrow (← mkAppM ``LE.le #[m, iS]) acc))
          let inner ← mkForallFVars #[fuel, iS, sz] p
          let em ← mkAppM ``Exists #[← mkLambdaFVars #[m] inner]
          mkAppM ``Exists #[← mkLambdaFVars #[n] em]
      let st ← withDrawLaws (searches := true) insts fun laws => do
        mkForallFVars (xs ++ insts ++ laws) (← mkArrow (← instantiateMVars rApp) body)
      defaultLevelMVars st

/-- The statement of `w.complete`: `∀ args [insts], R args → ∃ n m, ∀ fuel iS sz, … → Produces …`, with
an instance hypothesis for each instance argument of the worker. -/
def completeStatement (wN rN : Name) (outIdx : Array Nat) : TermElabM Expr := do
  if isCheckerWorker (← getEnv) wN then return ← checkCompleteStatement wN rN
  -- The worker draws at `Type`, so a universe-polymorphic relation is taken there: its universes fixed
  -- by the worker's arguments (`Sort u` at `Type`, not `Prop`), the rest at `0`.
  let rC ← mkConstWithFreshMVarLevels rN
  -- The worker likewise: a polymorphic one's type arguments are the relation's (a type parameter it
  -- generalized to `Sort u` taken at the relation's `Type`).
  let wConst ← mkConstWithFreshMVarLevels wN
  let wC ← mkAppOptM' wConst #[some (Lean.mkConst ``SGen), none, none, none, none, none, none]
  forallTelescopeReducing (← inferType rC) fun xs _ => do
    let rApp := mkAppN rC xs
    Meta.check rApp
    let ins := (Array.range xs.size).filterMap fun i => if outIdx.contains i then none else some xs[i]!
    let outs := outIdx.map (xs[·]!)
    let outT ← match outs.toList.reverse with
      | [] => throwError "#specimen_complete: no outputs"
      | o :: os => os.foldlM (fun acc x => mkAppM ``Prod.mk #[x, acc]) o
    let nat := Lean.mkConst ``Nat
    let wTy ← instantiateForall (← inferType wC) #[mkNatLit 0, mkNatLit 0, mkNatLit 0]
    workerArgs wTy ins.toList #[] #[] fun wargs insts => do
      let body ← withLocalDeclD `n nat fun n => withLocalDeclD `m nat fun m =>
        withLocalDeclD `fuel nat fun fuel => withLocalDeclD `iS nat fun iS => withLocalDeclD `sz nat fun sz => do
          let prod ← mkAppM ``Produces #[mkAppN wC (#[fuel, iS, sz] ++ wargs), outT]
          let p ← mkArrow (← mkAppM ``LE.le #[n, sz]) (← mkArrow (← mkAppM ``LT.lt #[sz, fuel])
            (← mkArrow (← mkAppM ``LE.le #[m, iS]) prod))
          let inner ← mkForallFVars #[fuel, iS, sz] p
          let em ← mkAppM ``Exists #[← mkLambdaFVars #[m] inner]
          mkAppM ``Exists #[← mkLambdaFVars #[n] em]
      let st ← withDrawLaws insts fun laws => do
        mkForallFVars (xs ++ insts ++ laws) (← mkArrow (← instantiateMVars rApp) body)
      defaultLevelMVars st

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
  unless isCheckerWorker (← getEnv) wN do specimenBody wN
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

/-- `specimen_or_admit t`: `t`, or, with `specimen.admitFailedParts`, when it fails (a heartbeat
timeout included), the goal admitted and a warning in place of the errors it logged. -/
syntax "specimen_or_admit " tactic : tactic

elab_rules : tactic
  | `(tactic| specimen_or_admit $t) => do
    unless specimen.admitFailedParts.get (← getOptions) do
      evalTactic t; return
    let s ← saveState
    let msgs := (← getThe Core.State).messages
    let failed ← tryCatchRuntimeEx (do evalTactic t; pure none) fun ex => pure (some ex)
    let errs := ((← getThe Core.State).messages.toList.drop msgs.toList.length).filter (·.severity == .error)
    if failed.isNone && errs.isEmpty then return
    let why ← match failed with
      | some ex => ex.toMessageData.toString
      | none => (errs.head!).data.toString
    s.restore
    modifyThe Core.State ({ · with messages := msgs })
    logWarning m!"completeness part not proved, admitted: {(← Term.getDeclName?).getD .anonymous}: {why.take 300}"
    for g in ← getGoals do g.admit
    setGoals []

/-- `proveComplete` as a `theorem` command, which Lean elaborates in parallel with the rest
(`specimen.parallelProofs`): the statement a reducible definition `w.complete_stmt`, the proof
`w.complete_raw` of it, and `w.complete` the statement unfolded, so that what follows sees it at once
and only the proof waits. A proof that does not close is an error logged on the theorem. -/
def proveCompleteParallel (wN rN : Name) (outIdx : Array Nat) (facts : Array Name := #[]) :
    CommandElabM Unit := do
  unless isCheckerWorker (← getEnv) wN do liftTermElabM <| specimenBody wN
  let stmt ← liftTermElabM <| completeStatement wN rN outIdx
  let stmtN := wN ++ `complete_stmt
  let rawN := wN ++ `complete_raw
  liftTermElabM do
    addDecl <| .defnDecl { name := stmtN, levelParams := [], type := mkSort levelZero, value := stmt,
                           hints := .abbrev, safety := .safe }
    setReducibleAttribute stmtN
  let fs : Array Term := facts.map fun f => ⟨mkIdent f⟩
  let w : Ident := mkIdent wN
  let sId : Ident := mkIdent (`_root_ ++ stmtN)
  let rId : Ident := mkIdent (`_root_ ++ rawN)
  let lbl := Syntax.mkStrLit s!"complete {wN}"
  elabCommand (← `(command| theorem $rId:ident : $sId:ident := by
    specimen_or_admit (log_time $lbl (
      delta $sId:ident
      intros
      rename_i h
      induction h <;> specimen_complete_case [$w:ident] [$fs,*]))))
  liftTermElabM do
    addDecl <| .thmDecl { name := wN ++ `complete, levelParams := [], type := stmt,
                          value := Lean.mkConst rawN }
    addCompleteSpec wN

/-- Split every conjunction among the hypotheses: a mutual block's induction hypotheses, one
conjunct for each mode of the premise's inductive. -/
elab "specimen_split_conj_hyps" : tactic => do
  let mut progress := true
  while progress do
    progress := false
    let g ← getMainGoal
    let some h ← g.withContext do
        (← getLCtx).findDeclM? fun d => do
          if d.isImplementationDetail then return none
          return if (← whnfR (← instantiateMVars d.type)).isAppOfArity ``And 2 then some d.fvarId else none
      | break
    let gs ← g.cases h
    replaceMainGoal (gs.map (·.mvarId)).toList
    progress := true

/-- The conjunction of `ps` (`True` if none). -/
def mkConj (ps : List Expr) : Expr :=
  match ps with
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkAnd p (mkConj ps)

/-- The `i`-th conjunct of a proof `pf` of `mkConj ps`. -/
def projConj (pf : Expr) (ps : List Expr) (i : Nat) : MetaM Expr :=
  -- the projections built with their types given: `mkAppM` would infer them, reading the parts'
  -- theorems, which wait for their proofs (elaborated in parallel) to be done
  match ps, i with
  | [_], 0 => pure pf
  | p :: qs, 0 => pure (mkApp3 (mkConst ``And.left) p (mkConj qs) pf)
  | p :: qs, i + 1 => projConj (mkApp3 (mkConst ``And.right) p (mkConj qs) pf) qs i
  | [], _ => throwError "projConj: no conjunct"

/-- One inductive of a mutual block's group, set up for its recursor: the goal (the conjunction of the
block's statements about it, over its arguments and derivation), the recursor applied at the
motives, and its cases left. -/
structure MutualSetup where
  rN : Name
  modes : Array Nat
  g : Expr
  g' : MVarId
  params : Array Expr
  minors : Array MVarId
  deriving Inhabited

/-- The setup of each inductive of the group the block derives in some mode. For each, its recursor
at motives the conjunction of the block's statements about each inductive (one for each mode the
block derives it in; `True` for none), so that its cases see the hypotheses for every inductive and
mode of the block. -/
def mutualSetup (items : Array (Name × Name × Array Nat)) (stmts : Array Expr) :
    TermElabM (Array MutualSetup) := do
  let (_, r₀, _) := items[0]!
  let ind₀ ← getConstInfoInduct r₀
  let group := ind₀.all
  unless items.all (fun it => group.contains it.2.1) do
    throwError "the block is not over one mutual group"
  let modesOf (J : Name) : Array Nat := (Array.range items.size).filter (items[·]!.2.1 == J)
  let mut out := #[]
  for rN in group do
    let modes := modesOf rN
    if modes.isEmpty then continue
    let nArgs ← forallTelescope (← inferType (Lean.mkConst rN)) fun xs _ => pure xs.size
    -- `∀ xs, R xs → body₁ ∧ … ∧ bodyₖ`, the bodies the modes' statements past `xs` and the derivation
    let conjStmt ← forallTelescope stmts[modes[0]!]! fun ys _ => do
      let xs := ys.extract 0 (nArgs + 1)
      unless ys.size == nArgs + 1 do throwError "a polymorphic worker in a mutual block"
      let bodies ← modes.toList.mapM fun i => instantiateForall stmts[i]! xs
      mkForallFVars xs (mkConj bodies)
    let g ← mkFreshExprMVar conjStmt .syntheticOpaque
    let (fvs, g') ← g.mvarId!.introN (nArgs + 1)
    let ind ← getConstInfoInduct rN
    let params := (fvs.extract 0 ind.numParams).map Expr.fvar
    let motives ← g'.withContext <| group.toArray.mapM fun J => do
      let ms := modesOf J
      let nJ ← forallTelescope (← inferType (Lean.mkConst J)) fun xs _ => pure xs.size
      if ms.isEmpty then
        -- `fun indices h => True`, over the inductive's indices and derivation at these parameters
        let jTy ← instantiateForall (← inferType (Lean.mkConst J)) params
        forallTelescope jTy fun is _ => do
          let jApp := mkAppN (Lean.mkConst J) (params ++ is)
          withLocalDeclD `h jApp fun h => mkLambdaFVars (is.push h) (mkConst ``True)
      else
        let sj ← instantiateForall stmts[ms[0]!]! params
        forallTelescope sj fun ys _ => do
          let xs := ys.extract 0 (nJ - params.size + 1)
          let bodies ← ms.toList.mapM fun i => do instantiateForall stmts[i]! (params ++ xs)
          mkLambdaFVars xs (mkConj bodies)
    -- the motives are propositions, and the relation is taken at `Type` (`completeStatement`)
    let rec_ := Lean.mkConst (rN ++ `rec) ((← getConstInfo (rN ++ `rec)).levelParams.map fun _ => levelZero)
    let gs ← g'.withContext <| g'.apply (mkAppN rec_ (params ++ motives))
    -- The statement does not mention the derivation, so the recursor's major premise is left; it is
    -- the derivation introduced.
    let major := Expr.fvar fvs.back!
    let mut minors := #[]
    for mg in gs do
      if ← mg.isAssigned then continue
      if ← g'.withContext (do isDefEq (← mg.getType) (← inferType major)) then mg.assign major
      else minors := minors.push mg
    out := out.push { rN, modes, g, g', params, minors }
  return out

/-- Each mode's theorem, its conjunct of the setup's goal, now proved. -/
def mutualFinish (items : Array (Name × Name × Array Nat)) (stmts : Array Expr) (st : MutualSetup) :
    TermElabM Unit := do
  let pf ← instantiateMVars st.g
  if pf.hasMVar || pf.hasSorry then
    let ms := (pf.collectMVars {}).result
    let tys ← ms.mapM fun m => do return m!"{mkMVar m} : {← m.getType}"
    throwError "{st.rN}: the proof did not close (expr mvars {pf.hasExprMVar}, level mvars \
      {pf.hasLevelMVar}, sorry {pf.hasSorry}): {MessageData.joinSep tys.toList ", "}"
  for k in [:st.modes.size] do
    let i := st.modes[k]!
    let (wN, _, _) := items[i]!
    let stmt := stmts[i]!
    let v ← forallTelescope stmt fun xs _ => do
      let bodies ← st.modes.toList.mapM fun i' => instantiateForall stmts[i']! xs
      mkLambdaFVars xs (← projConj (mkAppN pf xs) bodies k)
    let v ← instantiateMVars v
    addDecl <| .thmDecl { name := wN ++ `complete, levelParams := [], type := stmt, value := v }
    addCompleteSpec wN

/-- The tactic closing a case of a mutual block: split into its modes, each closed as
`induction`'s are. -/
def mutualCaseTac (items : Array (Name × Name × Array Nat)) (facts : Array Name) :
    TermElabM (TSyntax `tactic) := do
  let wsStx : Array Ident := items.map (mkIdent ·.1)
  let fs : Array Term := facts.map fun f => ⟨mkIdent f⟩
  `(tactic| (intros; specimen_split_conj_hyps; first
    | exact True.intro
    | (repeat' apply And.intro
       all_goals specimen_complete_case [$wsStx,*] [$fs,*])))

/-- Prove the workers of a block over a mutual inductive complete together (see `mutualSetup`): each
case split into its modes, and each closed as `induction`'s are. Each mode's theorem is then its
conjunct. -/
def proveCompleteMutual (items : Array (Name × Name × Array Nat)) (facts : Array Name := #[]) :
    TermElabM Unit := do
  for (w, _, _) in items do unless isCheckerWorker (← getEnv) w do specimenBody w
  let stmts ← items.mapM fun (w, r, is) => completeStatement w r is
  let caseTac ← mutualCaseTac items facts
  for st in ← mutualSetup items stmts do
    for mg in st.minors do
      let rest ← Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.run mg (evalTactic caseTac)
      unless rest.isEmpty do throwError "{st.rN}: a case did not close"
    mutualFinish items stmts st

/-- The conjuncts of a case's conclusion (`mkConj`'s nesting; each mode's statement is an `∃`). -/
partial def splitConj (e : Expr) : MetaM (List Expr) := do
  let e' ← whnfR e.headBeta
  match e'.and? with
  | some (a, b) => return a :: (← splitConj b)
  | none => return [e']

/-- How many parts each split component has, by its first worker (`#specimen_prove_setup`, from the
statements' phase). -/
initialize specimenPartCountExt : SimplePersistentEnvExtension (Name × Nat) (Std.HashMap Name Nat) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (w, n) => s.insert w n
    addImportedFn := fun as => as.foldl (fun s a => a.foldl (fun s (w, n) => s.insert w n) s) {} }

/-- Which of a block's completeness steps to run: all, or (the block split across files) its parts'
statements, a slice of its parts, the parts the slices left, or the assembly of its theorems from the
parts. -/
inductive CompletePhase where
  | all
  | stmts
  /-- the parts `j` with `(j + off) % n = i` (`off`: the parts of the components striped before it) -/
  | slice (i n off : Nat)
  /-- the parts not yet declared (a slice under `specimen.skipFailedParts` leaves out the ones it
  could not prove), proved here, in a file that imports more -/
  | proveMissing
  | finish
  deriving Inhabited, BEq

/-- `proveCompleteMutual`, each case and mode a theorem of its own, over the group's parameters and the
case's arguments, which Lean proves in parallel (`specimen.parallelProofs`). The recursors of the
group's inductives have the same cases at the same motives, so each is proved once, and every
recursor is applied to them, each case the conjunction of its modes (`True`, for an inductive the
block derives in no mode). A theorem that does not close is an error logged on it. -/
def proveCompleteMutualParallel (items : Array (Name × Name × Array Nat)) (facts : Array Name := #[])
    (phase : CompletePhase := .all) : CommandElabM Unit := do
  let w₀ := items[0]!.1
  let partName (j m : Nat) : Name := w₀ ++ Name.mkSimple s!"complete_case_{j}_{m}"
  -- the parts' statements, as definitions the theorems are stated with: the `m`-th conjunct of case
  -- `j`, over the parameters and the case's arguments
  let tA ← IO.monoMsNow
  let parts ← liftTermElabM do
    for (w, _, _) in items do unless isCheckerWorker (← getEnv) w do specimenBody w
    let tB ← IO.monoMsNow
    let stmts ← items.mapM fun (w, r, is) => completeStatement w r is
    let tC ← IO.monoMsNow
    let setups ← mutualSetup items stmts
    let tD ← IO.monoMsNow
    timerLog s!"  cblock {w₀} body {tB - tA} stmts {tC - tB} setup {tD - tC} ms"
    let st := setups[0]!
    let mut parts : Array Name := #[]
    for j in [:st.minors.size] do
      let ty ← instantiateMVars (← st.minors[j]!.getType)
      let tys ← st.g'.withContext <| forallTelescope ty fun xs body => do
        let cs ← splitConj body
        cs.mapM fun c => do
          if c.isConstOf ``True then return none
          return some (← instantiateMVars (← mkForallFVars (st.params ++ xs) c))
      for m in [:tys.length] do
        let some t := tys[m]! | continue
        if t.hasMVar then throwError "{st.rN}: a case's statement has a metavariable"
        let n := partName j m
        if phase == .all || phase == .stmts then
          addDecl <| .defnDecl { name := n ++ `stmt, levelParams := [], type := mkSort levelZero,
                                 value := t, hints := .abbrev, safety := .safe }
          setReducibleAttribute (n ++ `stmt)
        parts := parts.push n
    pure parts
  let tE ← IO.monoMsNow
  timerLog s!"  complete-block {w₀} queued {parts.size} parts (part stmts {tE - tA} ms)"
  if phase == .stmts then
    modifyEnv (specimenPartCountExt.addEntry · (w₀, parts.size))
    for i in [:parts.size] do timerLog s!"  PARTINDEX {i} {parts[i]!}"
    logInfo m!"PARTS {parts.size}"
    return
  let range : Nat × Nat := match phase with
    | .finish => (0, 0)
    | _ => (0, parts.size)
  let wsStx : Array Ident := items.map (mkIdent ·.1)
  let fs : Array Term := facts.map fun f => ⟨mkIdent f⟩
  -- a slice is every `n`-th part, so that the slow ones, which come in runs, are spread out
  let envNow ← getEnv
  let mine : Array Name := match phase with
    | .slice i k off => (parts.toList.zipIdx.filter (fun (_, j) => (j + off) % k == i)).toArray.map (·.1)
    | .proveMissing => parts.filter (!envNow.contains ·)
    | _ => parts.extract range.1 range.2
  if phase == .proveMissing then
    timerLog s!"  prove-missing {w₀}: {mine.size} parts"
    logInfo m!"proving {mine.size} parts the slices left"
  -- `specimen.skipFailedParts` (a slice): each part proved in a task of its own and declared only
  -- if its proof closes, so that a part a slice cannot prove (it needs what a later file imports) is
  -- left to the assembly's file instead of admitted
  let skip := specimen.skipFailedParts.get (← getOptions) &&
    (match phase with | .slice .. => true | _ => false)
  if skip then
    let mut tasks : Array (Name × Task (Except Exception (Option (Expr × Array ConstantInfo)))) := #[]
    for n in mine do
      let sId : Ident := mkIdent (`_root_ ++ n ++ `stmt)
      let lbl := Syntax.mkStrLit s!"complete {n}"
      let tac ← `(tactic| log_time $lbl (
        delta $sId:ident
        intros
        specimen_split_conj_hyps
        specimen_complete_case [$wsStx,*] [$fs,*]))
      let act ← wrapAsync (fun (_ : Unit) => liftTermElabM do
          let env0 ← getEnv
          let m ← mkFreshExprMVar (Lean.mkConst (n ++ `stmt)) .syntheticOpaque
          let closed ← try
              let gs ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run m.mvarId!
                (Lean.Elab.Tactic.withoutRecover (Lean.Elab.Tactic.evalTactic tac))
              pure gs.isEmpty
            catch _ => pure false
          unless closed do return none
          let pf ← instantiateMVars m
          if pf.hasMVar || pf.hasSorry then return none
          -- the auxiliary declarations the proof made (`simp`'s lemmas, say), which it refers to
          let envT ← getEnv
          let isNew (c : Name) : Bool := !env0.contains c && (envT.constants.map₂.contains c)
          -- only what the proof refers to, transitively: the rest (equations Lean caches, say) is
          -- made again where it is needed
          let mut aux : Array ConstantInfo := #[]
          let mut seen : NameSet := {}
          let mut todo : Array Name := pf.getUsedConstants.filter isNew
          while h : todo.size > 0 do
            let c := todo[todo.size - 1]
            todo := todo.pop
            if seen.contains c then continue
            seen := seen.insert c
            let some ci := envT.find? c | continue
            aux := aux.push ci
            let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
            todo := todo ++ used.filter (fun d => isNew d && !seen.contains d)
          return some (pf, aux)) none
      tasks := tasks.push (n, ← (act () : EIO Exception _).asTask)
    let mut left : Array Name := #[]
    for (n, t) in tasks do
      match t.get with
      | .ok (some (pf, aux)) =>
        liftCoreM do
          -- in dependency order: each once all it uses is declared
          let env0 ← getEnv
          let mut pending := aux.filter fun ci => !env0.contains ci.name
          while !pending.isEmpty do
            let env ← getEnv
            let ready := pending.filter fun ci =>
              let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
              used.all fun d => env.contains d || d == ci.name
            if ready.isEmpty then throwError "{n}: auxiliary declarations with unmet dependencies: {pending.map (·.name)}"
            for ci in ready do
              match ci with
              | .thmInfo v => addDecl (.thmDecl v)
              | .defnInfo v => addDecl (.defnDecl v)
              | .opaqueInfo v => addDecl (.opaqueDecl v)
              | .axiomInfo v => addDecl (.axiomDecl v)
              | _ => pure ()
            pending := pending.filter fun ci => !ready.any (·.name == ci.name)
          addDecl <| .thmDecl { name := n, levelParams := [], type := Lean.mkConst (n ++ `stmt), value := pf }
      | _ => left := left.push n
    unless left.isEmpty do
      timerLog s!"  parts left to the assembly ({left.size}): {left}"
      logInfo m!"{left.size} parts left to the assembly: {left}"
    return
  for n in mine do
    let sId : Ident := mkIdent (`_root_ ++ n ++ `stmt)
    let tId : Ident := mkIdent (`_root_ ++ n)
    let lbl := Syntax.mkStrLit s!"complete {n}"
    let tp ← IO.monoMsNow
    elabCommand (← `(command| theorem $tId:ident : $sId:ident := by
      specimen_or_admit (log_time $lbl (
        delta $sId:ident
        intros
        specimen_split_conj_hyps
        specimen_complete_case [$wsStx,*] [$fs,*]))))
    -- (with `Elab.async` off, the part's whole elaboration, its kernel check included)
    if !Elab.async.get (← getOptions) then
      timerLog s!"  PARTELAB {n} {(← IO.monoMsNow) - tp} ms"
  let tF ← IO.monoMsNow
  timerLog s!"  cblock {w₀} elabCommands {tF - tE} ms"
  match phase with
  | .slice .. | .proveMissing => return
  | _ => pure ()
  -- every recursor, at the cases, each the conjunction of its parts
  liftTermElabM do
    let ta ← IO.monoMsNow
    let stmts ← items.mapM fun (w, r, is) => completeStatement w r is
    let tb ← IO.monoMsNow
    let setups ← mutualSetup items stmts
    timerLog s!"  cblock {w₀} assemble-stmts {tb - ta} setup {(← IO.monoMsNow) - tb} ms"
    for st in setups do
      for j in [:st.minors.size] do
        let mg := st.minors[j]!
        let ty ← instantiateMVars (← mg.getType)
        let v ← st.g'.withContext <| forallTelescope ty fun xs body => do
          let cs ← splitConj body
          let pfs := (List.range cs.length).map fun m =>
            if cs[m]!.isConstOf ``True then Lean.mkConst ``True.intro
            else
              mkAppN (Lean.mkConst (partName j m)) (st.params ++ xs)
          -- (types given, not inferred: inferring them reads the parts' theorems, which wait for
          -- their proofs)
          let rec conj : List (Expr × Expr) → Expr
            | [] => Lean.mkConst ``True.intro
            | [(p, _)] => p
            | (p, t) :: ps => mkApp4 (mkConst ``And.intro) t (mkConj (ps.map (·.2))) p (conj ps)
          let pf ← mkExpectedTypeHint (conj (pfs.zip cs)) body
          mkLambdaFVars xs pf
        mg.assign v
      let tG ← IO.monoMsNow
      mutualFinish items stmts st
      timerLog s!"  cblock {w₀} {st.rN} assemble {tG - tF} finish {(← IO.monoMsNow) - tG} ms"

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
  let env ← getEnv
  let chk := isCheckerWorker env wN
  let (cls, law) := if chk then (``DecOpt, ``DecOptComplete)
    else if isEnumWorker env wN then (``EnumFor, ``EnumForComplete)
    else (``BacktrackGenFor, ``BacktrackGenForComplete)
  let some (instN, instTy) ← instanceRunning wN cls | throwError "no {cls} instance runs {wN}"
  -- A scoped instance (`scoped derive_mutual`) outside its namespace: its namespace's scoped
  -- declarations activated, as `open` would, so that the law's statement and proof resolve it;
  -- only while they are built, in a scope of their own (`pushScope`), not for the rest of the file.
  let isScoped := !(Meta.instanceExtension.getState (← getEnv)).instanceNames.contains instN
  -- The instance's parameters are the worker's inputs.
  let ilps := (← getConstInfo instN).levelParams
  -- `w.complete` is stated at universe `0` (`completeStatement`): so is the instance's law
  let mono := (← getConstInfo (wN ++ `complete)).levelParams.isEmpty && !ilps.isEmpty
  let instTy := if mono then instTy.instantiateLevelParams ilps (ilps.map fun _ => Level.zero) else instTy
  let ilvls := if mono then ilps.map (fun _ => Level.zero) else ilps.map mkLevelParam
  let ilps := if mono then [] else ilps
  let build : TermElabM (Expr × Expr) := do
    if isScoped then
      pushScope
      activateScoped instN.getPrefix
    let goal ← forallTelescopeReducing instTy fun ps body => do
      -- an instance argument of a class an earlier one already provides (the relation's
      -- `[DecidableEq α]` and the type parameter's) is that one, as the worker's statement takes it
      -- (`workerArgs`); instance resolution fills both alike wherever the law is used
      let mut args : Array Expr := #[]
      let mut kept : Array Expr := #[]
      for p in ps do
        if (← p.fvarId!.getBinderInfo).isInstImplicit then
          let ty ← inferType p
          if let some q ← kept.findM? fun q => do isDefEq (← inferType q) ty then
            args := args.push q; continue
        args := args.push p; kept := kept.push p
      let inst := mkAppN (Lean.mkConst instN ilvls) args
      let body := body.replaceFVars ps args
      let insts ← kept.filterM fun p => return (← p.fvarId!.getBinderInfo).isInstImplicit
      withDrawLaws (searches := chk) insts fun laws => do
        if chk then
          mkForallFVars (kept ++ laws) (← mkAppOptM law #[body.appArg!, inst])
        else
          let α := body.appFn!.appArg!
          let P := body.appArg!
          mkForallFVars (kept ++ laws) (← mkAppOptM law #[α, P, inst])
    let nParams := instTy.getNumHeadForalls
    -- Built as text: the output's pattern and the worker's arguments are plain names.
    let outs := String.intercalate ", " ((List.range nOut).map fun i => s!"o{i}")
    let pat := if nOut == 1 then "o0" else s!"⟨{outs}⟩"
    -- One hole for each argument of `w.complete` before its relation hypothesis, the instance
    -- hypotheses of a polymorphic worker included.
    let nHoles ← forallTelescopeReducing (← getConstInfo (wN ++ `complete)).type fun xs _ => pure (xs.size - 1)
    let _ := nArgs
    let holes := String.intercalate " " (List.replicate nHoles "_")
    let src := if chk then
        s!"by\n  intros\n  refine ⟨fun hx => ?_⟩\n  obtain ⟨n, m, h⟩ := @{wN ++ `complete} {holes} hx\n  exact ⟨n + m, fun s hs => h (s + 1) s s (by omega) (by omega) (by omega)⟩"
      else
        s!"by\n  intros\n  refine ⟨fun x hx => ?_⟩\n  obtain {pat} := x\n  obtain ⟨n, m, h⟩ := @{wN ++ `complete} {holes} hx\n  exact ⟨n + m, fun s l hs hl => h (s + 1) l s (by omega) (by omega) (by omega)⟩"
    let tac ← match Parser.runParserCategory (← getEnv) `term src with
      | .ok stx => pure stx
      | .error e => throwError "instance proof: {e}"
    let _ := nParams
    let pf ← Term.withoutErrToSorry do
      let pf ← elabTermEnsuringType tac goal
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars pf
    pure (goal, pf)
  -- (the scope popped, not the environment restored: the auxiliary lemmas the elaboration adds stay)
  let (goal, pf) ← try build finally if isScoped then popScope
  if pf.hasMVar || pf.hasSorry then throwError "the instance's proof did not close"
  let name := wN ++ `instComplete
  addDecl <| .thmDecl { name, levelParams := ilps, type := goal, value := pf }
  addInstance name .global (eval_prio default)

/-- The workers proved complete so far, for the facts of the next. -/
initialize completedRef : IO.Ref (Array Name) ← IO.mkRef #[]

/-- The components `specimen.deferComplete` recorded, in the order they were derived. -/
initialize specimenDeferredExt :
    SimplePersistentEnvExtension (Array (Name × Name × List Nat)) (Array (Array (Name × Name × List Nat))) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push e
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- What `#specimen_prove_setup` left to the part files: the components split, and the scope it ran in
(options, namespace, `open`s), which `#specimen_prove_part` and `#specimen_prove_split_finish` run in
too: the proofs' tactics resolve some names through it. -/
structure SplitRecord where
  large : Array Nat
  opts : Options
  ns : Name
  openDecls : List OpenDecl
  deriving Inhabited

initialize specimenSplitExt : SimplePersistentEnvExtension SplitRecord (Option SplitRecord) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ r => some r
    addImportedFn := fun as => as.foldl (fun s a => a.foldl (fun _ r => some r) s) none }

/-- Prove a component complete, or run one step of it (`phase`, for a block of several workers split
across files). -/
def completeBlock (gens : Array (Name × Name × List Nat)) (phase : CompletePhase := .all) :
    CommandElabM Unit := do
  -- an enumerator's searches, for the checkers that search with it (`specimen.completeAllSorts`)
  if (phase == .all || phase == .stmts) && !(Lean.Option.get (← getOptions) specimen.searchSeparately) then
    -- (no `env.contains` check for what is done: a name not there is answered only once every
    -- declaration still being elaborated is, which would wait for the earlier components' proofs)
    let env ← getEnv
    let enums := (gens.map (·.1)).filter (isEnumWorker env)
    unless enums.isEmpty do
      let t0 ← IO.monoMsNow
      try
        -- (in parallel even for one worker: proved in line, its `unfold` realizes the worker's
        -- equation, which waits for every declaration still being checked)
        let par := Lean.Option.get (← getOptions) specimen.parallelProofs
        -- (not `par && (← …)`, whose lifted `←` would run the parallel proof whatever `par`)
        let parallel ← if par then proveSearchHitsParallel enums else pure false
        unless parallel do
          liftTermElabM <| proveSearchHits enums
        timerLog s!"  searchHits {enums[0]!} ({enums.size}) ok {(← IO.monoMsNow) - t0} ms"
      catch e =>
        timerLog s!"  searchHits {enums[0]!} FAIL {(← IO.monoMsNow) - t0} ms: {(← e.toMessageData.toString).take 1500}"
        logWarning m!"specimen.emitComplete: the searches of {enums} not proved: {e.toMessageData}"
  if gens.size > 1 then
    let t0 ← IO.monoMsNow
    try
      let facts ← completedRef.get
      let facts := facts.filter ((← getEnv).contains ·)
      let items := gens.map fun (w, r, is) => (w, r, is.toArray)
      if Lean.Option.get (← getOptions) specimen.parallelProofs || phase != .all then
        proveCompleteMutualParallel items facts phase
      else
        liftTermElabM <| proveCompleteMutual items facts
      unless phase == .all || phase == .finish do return
      let tI ← IO.monoMsNow
      liftTermElabM do
        for (w, r, is) in gens do
          let nArgs ← forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels r)) fun xs _ => pure xs.size
          proveInstComplete w nArgs is.length
      timerLog s!"  cblock {gens[0]!.1} instComplete {(← IO.monoMsNow) - tI} ms"
      for (w, _, _) in gens do completedRef.modify (·.push (w ++ `completeSpec))
      timerLog s!"  complete-hook block {gens.size} {gens[0]!.1} ok {(← IO.monoMsNow) - t0} ms"
    catch e =>
      timerLog s!"  complete-hook block {gens.size} {gens[0]!.1} FAIL {(← IO.monoMsNow) - t0} ms"
      logWarning m!"specimen.emitComplete: the block \
        {", ".intercalate (gens.toList.map (toString ·.1))} not proved complete: {e.toMessageData}"
    return
  let par := Lean.Option.get (← getOptions) specimen.parallelProofs
  for (w, r, is) in gens do
    let t0 ← IO.monoMsNow
    try
      let facts ← completedRef.get
      let facts := facts.filter ((← getEnv).contains ·)
      -- a polymorphic worker's statement has instance hypotheses; it is proved in line
      let poly := !(← getConstInfo w).levelParams.isEmpty || !(← getConstInfo r).levelParams.isEmpty
      if par && !poly then
        -- one theorem for each constructor, as for a block; failing that, one for the worker
        try proveCompleteMutualParallel #[(w, r, is.toArray)] facts
        catch e =>
          timerLog s!"  complete-hook {w} per-case setup failed: {(← e.toMessageData.toString).take 200}"
          proveCompleteParallel w r is.toArray facts
      else if par then
        proveCompleteParallel w r is.toArray facts
      else
        liftTermElabM <| proveComplete w r is.toArray facts
      liftTermElabM do
        let nArgs ← forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels r)) fun xs _ => pure xs.size
        proveInstComplete w nArgs is.length
      completedRef.modify (·.push (w ++ `completeSpec))
      timerLog s!"  complete-hook {w} ok {(← IO.monoMsNow) - t0} ms"
      if Lean.Option.get (← getOptions) specimen.reportPhaseTimers then
        logInfo m!"specimen.emitComplete: {w} complete ({(← IO.monoMsNow) - t0} ms)"
    catch e =>
      timerLog s!"  complete-hook {w} FAIL {(← IO.monoMsNow) - t0} ms"
      logWarning m!"specimen.emitComplete: {w} not proved complete: {e.toMessageData}"

initialize specimenCompleteHook.set <| some fun gens => do
  if Lean.Option.get (← getOptions) specimen.deferComplete then
    modifyEnv (specimenDeferredExt.addEntry · gens)
    return
  completeBlock gens

/-- The completeness facts for the recorded component `k`: the theorems of the components before it,
those the files imported so far have. -/
def deferredFacts (k : Nat) : CommandElabM Unit := do
  let blocks := specimenDeferredExt.getState (← getEnv)
  let env ← getEnv
  let names := ((blocks.extract 0 k).foldl (fun acc b => acc ++ b.map (·.1 ++ `completeSpec)) #[]).filter
    env.contains
  completedRef.set names

/-- The recorded component `k`. -/
def deferredBlock (k : Nat) : CommandElabM (Array (Name × Name × List Nat)) := do
  let blocks := specimenDeferredExt.getState (← getEnv)
  let some b := blocks[k]? | throwError "no recorded component {k} (there are {blocks.size})"
  return b

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


/-- The constants an imported module's audit found depend on no axiom but `propext`,
`Classical.choice` and `Quot.sound` (`#specimen_audit_record`): a later audit stops at them. -/
initialize specimenAuditedExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun as => as.foldl (fun s a => a.foldl (·.insert ·) s) {} }

/-- Which of `roots` and the constants they depend on depend on an axiom but the standard three: a
depth-first walk with a memo (`true`: such an axiom), stopping at what an imported audit recorded. -/
def auditWalk (env : Environment) (roots : Array Name) : Std.HashMap Name Bool := Id.run do
  let clean := specimenAuditedExt.getState env
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let depsOf (ci : ConstantInfo) : Array Name :=
    ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  let mut memo : Std.HashMap Name Bool := Std.HashMap.emptyWithCapacity 100000
  for root in roots do
    -- an explicit stack of (constant, its dependencies once expanded)
    let mut stack : Array (Name × Option (Array Name)) := #[(root, none)]
    while h : stack.size > 0 do
      match stack[stack.size - 1] with
      | (c, some cs) =>
        stack := stack.pop
        let r := match env.find? c with
          | some (.axiomInfo _) => !(std.contains c)
          | _ => cs.any fun d => memo.getD d false
        memo := memo.insert c r
      | (c, none) =>
        if memo.contains c then stack := stack.pop; continue
        if clean.contains c then memo := memo.insert c false; stack := stack.pop; continue
        memo := memo.insert c false  -- in progress: a cycle reads `false`
        let cs := match env.find? c with
          | some ci => depsOf ci
          | none => #[]
        stack := stack.set! (stack.size - 1) (c, some cs)
        for d in cs do
          unless memo.contains d do stack := stack.push (d, none)
  return memo

/-- The sort of a derived worker, read off its name: `gen`, `enum` or `check`. -/
def workerSort? (env : Environment) (w : Name) : Option String :=
  (Specimen.workerInfo? env w).bind fun i => match i.sort with
    | .Generator => some "gen" | .Enumerator => some "enum" | .Checker => some "check" | .Theorem => none

/-- The laws a worker of sort `sort` has once proved sound (`complete := false`) or complete. -/
def requiredLaws (sort : String) (complete : Bool) : List Name :=
  if complete then (if sort == "enum" then [`complete, `instComplete, `searchHits] else [`complete, `instComplete])
  else match sort with
    | "gen" => [`sound]
    | "enum" => [`sound, `searchSound]
    | "check" => [`checkSound]
    | _ => []

/-- The laws of `ws` that are missing: for soundness every worker's; for completeness every
generator's, and an enumerator's or a checker's when another of its sort in `ws` has them (the
enumerators and checkers are proved complete only under `specimen.completeAllSorts`). -/
def missingLaws (env : Environment) (ws : Array Name) (complete : Bool) : Array Name := Id.run do
  let sorted := ws.filterMap fun w => (workerSort? env w).map (w, ·)
  let proved (sort : String) : Bool := sort == "gen" || !complete ||
    sorted.any fun (w, s) => s == sort && env.contains (w ++ `complete)
  let mut out := #[]
  for (w, sort) in sorted do
    if proved sort then
      for l in requiredLaws sort complete do
        unless env.contains (w ++ l) do out := out.push (w ++ l)
  return out

/-- `#specimen_audit_record`: audit this module's own constants, and record the ones (and what they
depend on) that depend on no axiom but the standard three, for a later audit to stop at. -/
syntax (name := specimenAuditRecord) "#specimen_audit_record" : command

@[command_elab specimenAuditRecord] def elabSpecimenAuditRecord : CommandElab := fun _ => do
  let env ← getEnv
  let t0 ← IO.monoMsNow
  let roots := env.constants.map₂.foldl (fun acc c _ => acc.push c) #[]
  let memo := auditWalk env roots
  let clean := specimenAuditedExt.getState env
  let mut k : Nat := 0
  for (c, bad) in memo do
    if !bad && !clean.contains c then
      modifyEnv (specimenAuditedExt.addEntry · c); k := k + 1
  timerLog s!"  audit-record: {roots.size} roots, {k} recorded, {(← IO.monoMsNow) - t0} ms"

/-- `#specimen_audit "suffix"`: for the derived workers whose names end in `suffix` (generators
`specimen_gen_…`, enumerators `specimen_enum_…`, checkers `specimen_check_…`), how many have each
law (`sound`, `checkSound`, `searchSound`, `complete`, `instComplete`, `searchHits`), and how many
`complete` theorems depend on an axiom other than `propext`, `Classical.choice` and `Quot.sound`
(stopping at what imported `#specimen_audit_record`s found depends on none). An error if a worker
lacks a law that its sort's proved laws include (`laws missing`), or if a law depends on another
axiom. -/
syntax (name := specimenAudit) "#specimen_audit " str : command

@[command_elab specimenAudit] def elabSpecimenAudit : CommandElab := fun stx => do
  let suffix := stx[1].isStrLit?.getD ""
  let env ← getEnv
  let ws := (Specimen.derivedWorkers env).filterMap fun (c, _) => match c with
    | .str _ l => if l.endsWith suffix then (workerSort? env c).map (c, ·) else none
    | _ => none
  for k in ["gen", "enum", "check"] do
    let ws := ws.filter (·.2 == k) |>.map (·.1)
    let has (s : String) := (ws.filter fun w => env.contains (w ++ Name.mkSimple s)).size
    logInfo m!"{k}: workers {ws.size}; sound {has "sound"}; checkSound {has "checkSound"}; searchSound {has "searchSound"}; complete {has "complete"}; instComplete {has "instComplete"}; searchHits {has "searchHits"}"
  let roots := ws.filterMap fun (w, _) => if env.contains (w ++ `complete) then some (w ++ `complete) else none
  -- every law of every worker: soundness, the searches', completeness, the instances'
  let laws := ws.flatMap fun (w, _) =>
    #[`sound, `checkSound, `searchSound, `searchFinds, `searchHits, `complete, `instComplete,
      `instSearch].filterMap fun s => if env.contains (w ++ s) then some (w ++ s) else none
  -- laws missing: soundness if any worker has it, completeness if any has it
  let names := ws.map (·.1)
  let soundOn := names.any fun w => env.contains (w ++ `sound) || env.contains (w ++ `checkSound)
  let missing := (if soundOn then missingLaws env names false else #[]) ++
    (if roots.isEmpty then #[] else missingLaws env names true)
  logInfo m!"laws missing: {missing.size}"
  unless missing.isEmpty do
    throwError "{missing.size} laws were not proved: {missing.toList.take 20}"
  let t0 ← IO.monoMsNow
  let memo := auditWalk env laws
  let nbad := (roots.filter fun r => memo.getD r false).size
  let badLaws := laws.filter fun r => memo.getD r false
  timerLog s!"  audit: {memo.size} constants walked, {(← IO.monoMsNow) - t0} ms"
  logInfo m!"complete with nonstandard axioms: {nbad}"
  logInfo m!"laws checked: {laws.size}; with nonstandard axioms: {badLaws.size}"
  unless badLaws.isEmpty do
    throwError "{badLaws.size} laws depend on an axiom other than `propext`, `Classical.choice` \
      and `Quot.sound`: {badLaws.toList.take 20}"


/-! ## Proving a derivation's laws across files

A derivation records its components (`specimen.deferSound`, `specimen.deferComplete`); these commands
prove them, in files Lake checks in parallel. A component is named by one of its workers, by the
worker's sort, relation and outputs (`gen HasType [2, 6]`), so the files do not depend on the order
the derivation found its components in.

* `#specimen_prove_sound`: the soundness of every worker.
* `#specimen_prove_all_but [c, …]`: the enumerators' searches, and every component but those listed,
  which are proved by the three commands below, split across files.
* `#specimen_prove_stmts c`: the statements of component `c`'s parts.
* `#specimen_prove_slice c i of n`: every `n`-th of `c`'s parts, from the `i`-th; a part the slice
  cannot prove (it needs what a later file imports) is not declared.
* `#specimen_prove_finish c`: the parts of `c` no imported file declares, then `c`'s theorems.

Each command fails if a proof does not close, and checks that the laws it proves depend on no axiom
but `propext`, `Classical.choice` and `Quot.sound`: the build succeeds only if every law holds. -/

/-- A component, by the sort, relation and outputs of one of its workers. -/
syntax specimenComponent := (&"gen" <|> &"enum" <|> &"check") ident " [" num,* "]"

/-- The recorded component a reference names. -/
def resolveComponent (stx : TSyntax ``specimenComponent) : CommandElabM Nat := do
  -- `sort ident [n, …]`: the sort an atom, the outputs the numerals between the brackets
  let rec firstAtom : Syntax → String
    | .atom _ v => v
    | .ident _ _ n _ => n.toString
    | .node _ _ args => args.foldl (fun acc a => if acc.isEmpty then firstAtom a else acc) ""
    | _ => ""
  let sortStr := (firstAtom stx.raw[0]).trimAscii.toString
  let r : Ident := ⟨stx.raw[1]⟩
  let is := (stx.raw[3].getSepArgs.map fun a => a.isNatLit?.getD 0).toList
  let rel ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  resolveComponent.find sortStr rel is
where
  find (sortStr : String) (rel : Name) (is : List Nat) : CommandElabM Nat := do
    let env ← getEnv
    let blocks := specimenDeferredExt.getState env
    for k in [:blocks.size] do
      for (w, r', is') in blocks[k]! do
        if r' == rel && is' == is && workerSort? env w == some sortStr then return k
    let same := blocks.toList.flatMap fun b => b.toList.filterMap fun (w, r', is') =>
      if r' == rel then some s!"{(workerSort? env w).getD "?"} {is'}" else none
    throwError "no recorded component has a {sortStr} worker for {rel} with outputs {is}; \
      {rel}'s workers: {same}"

/-- The laws of these workers (soundness, the searches', completeness, the instances'): fail if one
is missing (`missingLaws`) or depends on an axiom but the standard three; record what is clean, for
later files' checks. -/
def auditWorkers (ws : Array Name) (what : String) (complete : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let missing := missingLaws env ws complete
  unless missing.isEmpty do
    throwError "{what}: {missing.size} laws were not proved: {missing.toList.take 20}"
  let laws := ws.flatMap fun w =>
    #[`sound, `checkSound, `searchSound, `searchFinds, `searchHits, `complete, `instComplete,
      `instSearch].filterMap fun s => if env.contains (w ++ s) then some (w ++ s) else none
  let memo := auditWalk env laws
  let bad := laws.filter (memo.getD · false)
  unless bad.isEmpty do
    throwError "{what}: {bad.size} of {laws.size} laws depend on an axiom other than `propext`, \
      `Classical.choice` and `Quot.sound`: {bad.toList.take 20}"
  let clean := specimenAuditedExt.getState env
  for (c, b) in memo do
    if !b && !clean.contains c then modifyEnv (specimenAuditedExt.addEntry · c)
  logInfo m!"{what}: {laws.size} laws, each depending only on the standard axioms"

/-- The enumerators' searches of these components; an error if one does not close. -/
def proveSearches (ks : List Nat) : CommandElabM Unit := do
  for k in ks do
    let env ← getEnv
    let enums := (← deferredBlock k).map (·.1) |>.filter (isEnumWorker env)
    unless enums.isEmpty do
      unless ← proveSearchHitsParallel enums do liftTermElabM <| proveSearchHits enums

/-- The options these commands run under: searches proved by `#specimen_prove_all_but` alone, no
part admitted, a slice's unproved parts left out. -/
def withProofOptions (x : CommandElabM α) : CommandElabM α :=
  let set (o : Options) : Options :=
    specimen.skipFailedParts.set (specimen.admitFailedParts.set (specimen.searchSeparately.set o true) false) true
  withScope (fun sc => { sc with opts := set sc.opts }) x

/-- Run in the scope `#specimen_prove_setup` recorded, with the opened namespaces' scoped declarations
active, and at its recursion depth, which `set_option maxRecDepth` also sets in the command state
rather than only in the scope. -/
def withRecordedScope (r : SplitRecord) (x : CommandElabM α) : CommandElabM α := do
  let d := (← get).maxRecDepth
  modify fun s => { s with maxRecDepth := maxRecDepth.get r.opts }
  -- as `open` does: the opened namespaces' scoped declarations (a `scoped derive_mutual`'s instances)
  for o in r.openDecls do
    if let .simple ns _ := o then activateScoped ns
  try withScope (fun sc => { sc with opts := r.opts, currNamespace := r.ns, openDecls := r.openDecls }) x
  finally modify fun s => { s with maxRecDepth := d }

/-- `#specimen_prove_sound`: the soundness steps the derivation recorded, then the check of every
worker's soundness laws. -/
syntax "#specimen_prove_sound" : command
/-- `#specimen_prove_all_but [c, …]`: the enumerators' searches of every component, and every
component but those listed. -/
syntax "#specimen_prove_all_but " "[" specimenComponent,* "]" : command
/-- `#specimen_prove_stmts c`: the statements of component `c`'s parts. -/
syntax "#specimen_prove_stmts " specimenComponent : command
/-- `#specimen_prove_slice c i of n`: every `n`-th part of component `c` from the `i`-th, each declared
only if its proof closes. -/
syntax "#specimen_prove_slice " specimenComponent num &" of " num : command
/-- `#specimen_prove_finish c`: the parts of component `c` no imported file declares, then `c`'s
theorems, then the check of its workers' laws. -/
syntax "#specimen_prove_finish " specimenComponent : command
/-- `#specimen_blocks`: the recorded components, each by its first worker, with its size. -/
syntax "#specimen_blocks" : command
/-- `#specimen_prove_setup`: the enumerators' searches, every component with fewer than
`specimen.splitMinWorkers` workers, and the statements of the others' parts, which
`#specimen_prove_part` files prove and `#specimen_prove_split_finish` completes. -/
syntax "#specimen_prove_setup" : command
/-- `#specimen_prove_part i of n`: every `n`-th of the split components' parts, counted across them
all, from the `i`-th; a part this file cannot prove (it needs an earlier split component's theorems) is
left to `#specimen_prove_split_finish`. -/
syntax "#specimen_prove_part " num &" of " num : command
/-- `#specimen_prove_split_finish`: for each split component in order, the parts no imported file
declares, then its theorems, then the check of its workers' laws. -/
syntax "#specimen_prove_split_finish" : command

elab_rules : command
  | `(#specimen_prove_sound) => do
    let some stx := (Parser.runParserCategory (← getEnv) `command "#specimen_sound_replay").toOption
      | throwError "#specimen_prove_sound needs `#specimen_sound_replay` (import Specimen)"
    elabCommand stx
    let ws := (specimenDeferredExt.getState (← getEnv)).flatMap (·.map (·.1))
    auditWorkers ws "soundness" false
  | `(#specimen_prove_all_but [$cs,*]) => withProofOptions do
    let skip ← cs.getElems.mapM resolveComponent
    let n := (specimenDeferredExt.getState (← getEnv)).size
    proveSearches (List.range n)
    for k in [:n] do
      if skip.contains k then continue
      deferredFacts k
      completeBlock (← deferredBlock k)
    let blocks := specimenDeferredExt.getState (← getEnv)
    let ws := (List.range n).filter (!skip.contains ·) |>.toArray.flatMap fun k =>
      (blocks[k]!).map (·.1)
    auditWorkers ws s!"{n - skip.size} components" true
  | `(#specimen_prove_stmts $c) => withProofOptions do
    let k ← resolveComponent c
    deferredFacts k
    completeBlock (← deferredBlock k) .stmts
  | `(#specimen_prove_slice $c $i of $n) => withProofOptions do
    let k ← resolveComponent c
    deferredFacts k
    completeBlock (← deferredBlock k) (.slice i.getNat n.getNat 0)
  | `(#specimen_prove_finish $c) => withProofOptions do
    let k ← resolveComponent c
    deferredFacts k
    let b ← deferredBlock k
    completeBlock b .proveMissing
    completeBlock b .finish
    auditWorkers (b.map (·.1)) s!"component {b[0]!.1}" true
  | `(#specimen_prove_setup) => do
    let opts ← getOptions
    let sc ← getScope
    withProofOptions do
      let blocks := specimenDeferredExt.getState (← getEnv)
      let min := specimen.splitMinWorkers.get opts
      let large := (List.range blocks.size).filter (blocks[·]!.size ≥ min) |>.toArray
      proveSearches (List.range blocks.size)
      for k in [:blocks.size] do
        deferredFacts k
        if large.contains k then completeBlock (← deferredBlock k) .stmts
        else completeBlock (← deferredBlock k)
      let ws := (List.range blocks.size).filter (!large.contains ·) |>.toArray.flatMap fun k =>
        (blocks[k]!).map (·.1)
      auditWorkers ws s!"{blocks.size - large.size} components" true
      modifyEnv (specimenSplitExt.addEntry · { large, opts, ns := sc.currNamespace, openDecls := sc.openDecls })
      let env ← getEnv
      let name (k : Nat) : String :=
        let (w, r, is) := (blocks[k]!)[0]!
        s!"{(workerSort? env w).getD "?"} {r} {is}"
      logInfo m!"{large.size} components split across the part files: {large.toList.map name}"
  | `(#specimen_prove_part $i of $n) => do
    let some r := specimenSplitExt.getState (← getEnv)
      | throwError "#specimen_prove_part: import the file that runs `#specimen_prove_setup`"
    withRecordedScope r <| withProofOptions do
      let counts := specimenPartCountExt.getState (← getEnv)
      let mut off := 0
      for k in r.large do
        let b ← deferredBlock k
        deferredFacts k
        completeBlock b (.slice i.getNat n.getNat off)
        off := off + counts.getD b[0]!.1 0
  | `(#specimen_prove_split_finish) => do
    let some r := specimenSplitExt.getState (← getEnv)
      | throwError "#specimen_prove_split_finish: import the part files"
    withRecordedScope r <| withProofOptions do
      for k in r.large do
        let b ← deferredBlock k
        deferredFacts k
        completeBlock b .proveMissing
        completeBlock b .finish
        auditWorkers (b.map (·.1)) s!"component {b[0]!.1}" true
  | `(#specimen_blocks) => do
    let blocks := specimenDeferredExt.getState (← getEnv)
    for k in [:blocks.size] do
      let b := blocks[k]!
      let (w, r, is) := b[0]!
      logInfo m!"{(workerSort? (← getEnv) w).getD "?"} {r} {is}: {b.size} workers"

end Specimen.Correctness
