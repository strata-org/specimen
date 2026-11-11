import Specimen.Correctness.SoundOf
import Specimen.Correctness.CheckHyps
import Specimen.Correctness.SearchFinds

/-!
# A derived checker is sound for its relation

Under `specimen.emitSound`, each derived checker worker `W` of relation `R` gets

  `W.checkSound : ∀ fuel initSize size ins, W fuel initSize size ins = .ok true → R ins`

The workers of a block are proved together, by induction on the fuel: `check_hyps` reads the run
(unfolding the block's workers, with the induction hypothesis and the laws of the checkers they call
as facts), and `ctor_leaf` closes each leaf by one of `R`'s constructors. The generators that call a
checker use its law at their leaves.
-/

namespace Specimen.Correctness

open Lean Meta Elab Tactic Term Command

/-- A checker worker's soundness statement: `∀ fuel initSize size ins, w … = .ok true → r ins`. -/
def checkStatement (wN rN : Name) : TermElabM Expr := do
  let wC ← mkConstWithFreshMVarLevels wN
  let rC ← mkConstWithFreshMVarLevels rN
  let stmtOf (wC rC : Expr) : MetaM Expr := do
    forallTelescopeReducing (← inferType wC) fun xs _ => do
      let run := mkAppN wC xs
      let .app (.app (.const ``Except us) ε) bool ← whnfR (← inferType run)
        | throwError "checker {wN}: expected a run in `Except _ Bool`"
      let okTrue := mkApp3 (.const ``Except.ok us) ε bool (mkConst ``Bool.true)
      let acc ← mkEq run okTrue
      -- each instance it searches a type parameter's values through, with that search's law, as an
      -- enumerator's `searchFinds` statement has (`searchFindsStatements`)
      let rec withLaws (i : Nat) (laws : Array Expr) : MetaM Expr := do
        if h : i < xs.size then
          let x := xs[i]
          let ty ← inferType x
          if (← x.fvarId!.getBinderInfo).isInstImplicit && ty.isAppOfArity ``Basalt.ArbitrarySized 1 then
            let lawTy ← mkAppOptM ``ArbitrarySizedSearch #[ty.appArg!, x]
            withLocalDecl `law .instImplicit lawTy fun l => withLaws (i + 1) (laws.push l)
          else withLaws (i + 1) laws
        else mkForallFVars (xs ++ laws) (← mkArrow acc (mkAppN rC (← relInputs xs)))
      withLaws 0 #[]
  -- The relation at the inputs fixes the worker's universes; the rest are the theorems' own.
  Meta.check (← stmtOf wC rC)
  let wC ← Term.levelMVarToParam (← instantiateMVars wC)
  let rC ← Term.levelMVarToParam (← instantiateMVars rC)
  instantiateMVars (← stmtOf wC rC)

/-- Prove the checker workers `items` (worker, relation) of one block sound together, with `facts` for
the checkers they call: `w.checkSound` for each. With `gens` (worker, relation, output indices), the
generators or enumerators of the same mutual block, which call these checkers and which the checkers
search with: each `w.sound` too, in the same induction, since each needs the other's law at the
previous fuel. -/
def proveCheckSound (items : Array (Name × Name)) (facts : Array Term)
    (gens : Array (Name × Name × Array Nat) := #[]) : TermElabM Unit := do
  -- (worker, statement, its unfolding equation if a generator)
  let mut ws : Array (Name × Expr × Option Name) := #[]
  for (wN, rN, outIdx) in gens do
    let (eqn, stmt) ← soundStatement wN rN outIdx
    ws := ws.push (wN, stmt, some eqn)
  for (wN, rN) in items do
    ws := ws.push (wN, ← checkStatement wN rN, none)
  let lps := (ws.foldl (fun acc (w : Name × Expr × Option Name) => collectLevelParams acc w.2.1) {}).params.toList
  let conj ← withLocalDeclD `fuel (Lean.mkConst ``Nat) fun fuel => do
    let parts := ws.map fun (_, s, _) => s.bindingBody!.instantiate1 fuel
    let c := parts.pop.foldr (fun p acc => mkAnd p acc) parts.back!
    mkForallFVars #[fuel] c
  let k := ws.size
  let caseNames : Array Ident := (Array.range k).map fun i => mkIdent (Name.mkSimple s!"w{i}")
  let holes : Array Term ← caseNames.mapM fun n => `(?$n)
  let ckIds : Array Ident := items.map (mkIdent ·.1)
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `(ih) else
    let mut t ← `(ih)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let factsAll : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts)
  let generic : Array Term := #[← `(@succ_gen_eqRight), ← `(@succ_gen_eqLeft),
    ← `(@succ_enum_eqRight), ← `(@succ_enum_eqLeft)]
  let factsGen : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts ++ generic)
  let zeroOf (i : Nat) : TermElabM (TSyntax `tactic) := do
    match ws[i]!.2.2 with
    | some eqn => `(tactic| (intros; rw [$(mkIdent eqn):ident]; walk))
    | none => `(tactic| (intros; check_hyps unfolding [$ckIds,*]))
  let succOf (i : Nat) : TermElabM (TSyntax `tactic) := do
    match ws[i]!.2.2 with
    | some eqn => `(tactic| (
        intros
        rw [$(mkIdent eqn):ident]
        timed "unfold" (unfold_gen_instances [$factsGen,*])
        timed "walk" (walk [$factsGen,*])
        timed "ctor_leaf" (all_goals ((try check_hyps [$factsGen,*]); ctor_leaf))))
    | none => `(tactic| (intros; timed "cs.check_hyps" (check_hyps [$factsAll,*] unfolding [$ckIds,*]) <;>
          timed "cs.ctor_leaf" ctor_leaf))
  let byCases (f : Nat → TermElabM (TSyntax `tactic)) : TermElabM (TSyntax `tactic) := do
    if k == 1 then return ← f 0
    let mut t ← `(tactic| refine ⟨$holes,*⟩)
    for i in [:k] do
      let ti ← f i
      t ← `(tactic| ($t; case $(caseNames[i]!):ident => $ti:tactic))
    return t
  let zt ← byCases zeroOf
  let st ← byCases succOf
  let tac ← `(by
      intro fuel
      induction fuel with
      | zero => $zt:tactic
      | succ f ih => $st:tactic)
  let pf ← elabTermEnsuringType tac conj
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  reportTacticTimes "checkSound"
  if pf.hasMVar then throwError "the proof did not close"
  if pf.hasSorry then throwError "the proof did not close: a leaf was admitted"
  let blockName := ws[0]!.1 ++ `checkSound_block
  addDecl <| .thmDecl { name := blockName, levelParams := lps, type := ← instantiateMVars conj, value := pf }
  for i in [:k] do
    let (wN, stmt, eqn?) := ws[i]!
    let v ← forallTelescope stmt fun xs _ => do
      let mut e := mkApp (Lean.mkConst blockName (lps.map mkLevelParam)) xs[0]!
      if k > 1 then
        for _ in [:i] do e ← mkAppM ``And.right #[e]
        if i < k - 1 then e ← mkAppM ``And.left #[e]
      mkLambdaFVars xs (mkAppN e (xs.extract 1 xs.size))
    let suffix := if eqn?.isSome then `sound else `checkSound
    addDecl <| .thmDecl { name := wN ++ suffix, levelParams := lps, type := stmt, value := v }

/-- `proveCheckSound`, each worker's base case and step a theorem of its own, which Lean proves in
parallel (`specimen.parallelProofs`); `false`, having done nothing, for statements with universe
parameters. -/
def proveCheckSoundParallel (items : Array (Name × Name)) (facts : Array Term)
    (gens : Array (Name × Name × Array Nat)) : CommandElabM Bool := do
  let ws ← liftTermElabM do
    let mut ws : Array (Name × Expr × Option Name) := #[]
    for (wN, rN, outIdx) in gens do
      let (eqn, stmt) ← soundStatement wN rN outIdx (genEqn := false)
      -- the enumerator's equations by `rfl` (`W.eq_zero`, `W.eq_body`): rewriting by `W.eq_def`
      -- generates it, a proof by splitting every `match` of the body, as large as the body and
      -- checked by the kernel on the thread that first needs it
      if (← IO.getEnv "SPECIMEN_BODY_NORFL").isNone && !(← getEnv).contains (wN ++ `eq_body) then
        try discard <| specimenBodyByRfl wN catch _ => pure ()
      ws := ws.push (wN, stmt, some eqn)
    for (wN, rN) in items do
      ws := ws.push (wN, ← checkStatement wN rN, none)
    return ws
  let env ← getEnv
  let rwZero (w eqn : Name) : CommandElabM (TSyntax `tactic) :=
    if env.contains (w ++ `eq_zero) then `(tactic| rw [$(mkIdent (w ++ `eq_zero)):ident])
    else `(tactic| rw [$(mkIdent eqn):ident])
  let rwSucc (w eqn : Name) : CommandElabM (TSyntax `tactic) :=
    if env.contains (w ++ `eq_body) then
      `(tactic| (rw [$(mkIdent (w ++ `eq_body)):ident]; delta $(mkIdent (w ++ `body)):ident))
    else `(tactic| rw [$(mkIdent eqn):ident])
  let lps := (ws.foldl (fun acc (w : Name × Expr × Option Name) => collectLevelParams acc w.2.1) {}).params.toList
  unless lps.isEmpty do return false
  let k := ws.size
  let ckIds : Array Ident := items.map (mkIdent ·.1)
  let ih := mkIdent `ih
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `($ih:ident) else
    let mut t ← `($ih:ident)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let factsAll : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts)
  let generic : Array Term := #[← `(@succ_gen_eqRight), ← `(@succ_gen_eqLeft),
    ← `(@succ_enum_eqRight), ← `(@succ_enum_eqLeft)]
  let factsGen : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts ++ generic)
  let block := ws[0]!.1 ++ `checkSound_block
  let stmts := ws.map fun (w, st, _) => (w, st)
  proveBlockParallel stmts "checkSound" block
    (fun i => do
      match ws[i]!.2.2 with
      | some eqn => do `(tactic| (intros; $(← rwZero ws[i]!.1 eqn):tactic; walk))
      | none => `(tactic| (intros; check_hyps unfolding [$ckIds,*])))
    (fun i => do
      match ws[i]!.2.2 with
      | some eqn => do `(tactic| (
          intros
          $(← rwSucc ws[i]!.1 eqn):tactic
          unfold_gen_instances [$factsGen,*]
          walk [$factsGen,*]
          all_goals ((try check_hyps [$factsGen,*]); ctor_leaf)))
      | none => `(tactic| (intros; check_hyps [$factsAll,*] unfolding [$ckIds,*] <;> ctor_leaf)))
  liftTermElabM <| splitBlock block [] stmts `checkSound
    (ws.map fun (_, _, e?) => if e?.isSome then `sound else `checkSound)
  return true

initialize specimenCheckSoundHook.set <| some fun gens checkers sounds => do
  -- the hand-written instances' laws too (`@[specimen_sound]`), for the enumerators proved with the
  -- checkers: a call of a hand-written enumerator is otherwise a value of which nothing is known
  let tagged := (specimenSoundExt.getState (← getEnv)).toArray.filter (!sounds.contains ·)
  let facts : Array Term := (sounds ++ tagged).map fun n =>
    ⟨mkNode ``Lean.Parser.Term.explicit #[mkAtom "@", mkIdent n]⟩
  -- A budget, so that a checker `check_hyps` cannot read in reasonable time fails rather than stalls
  -- the derivation: the generators that need its law then fail, and the rest go on.
  let budget := ((← IO.getEnv "SPECIMEN_CHECK_HEARTBEATS").bind String.toNat?).getD 2000000
  try
    if Lean.Option.get (← getOptions) specimen.parallelProofs && (← IO.getEnv "SPECIMEN_PAR_NO_CHECK").isNone then
      if ← proveCheckSoundParallel checkers facts (gens.map fun (w, r, is) => (w, r, is.toArray)) then
        return
    liftTermElabM <| Core.withCurrHeartbeats <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := budget * 1000 }) <|
      proveCheckSound checkers facts (gens.map fun (w, r, is) => (w, r, is.toArray))
  catch e =>
    reportTacticTimes "checkSound (failed)"
    timerLog s!"    checkSound error: {(← e.toMessageData.toString).take 1500}"
    logWarning m!"specimen.emitSound: checkers {", ".intercalate (checkers.toList.map (toString ·.1))} \
      not proved sound: {e.toMessageData}"

end Specimen.Correctness
