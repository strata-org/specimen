import Specimen.Correctness.SoundOf
import Specimen.Correctness.SearchFinds

/-!
# A derived enumerator's search finds only witnesses

Under `specimen.emitSound`, each derived enumerator worker `W` of relation `R` gets, besides its
soundness at `SGen` (`W.sound`, as a generator's),

  `W.searchFinds : ∀ fuel iS size ins, SearchFinds (W (G := Search) …) (W (G := SGen) …)`
  `W.searchSound : ∀ fuel iS size ins k, (run of W at Search, asking k) accepts → ∃ a, R ins a ∧ k a = .ok true`

the first by induction on the fuel and `walk`, the second by `search_accepts`. A checker that searches
for a premise's witness with `W` (`Specimen.CheckerSearch`) uses `W.searchSound`.
-/

namespace Specimen.Correctness

open Lean Meta Elab Tactic Term Command

/-- The workers' `searchFinds` statements, `∀ fuel …, SearchFinds (W at Search …) (W at SGen …)`. -/
def searchFindsStatements (ws : Array Name) : TermElabM (Array Expr) := do
  let mut stmts : Array Expr := #[]
  for wN in ws do
    let c ← mkConstWithFreshMVarLevels wN
    let wS ← workerAtSGen.atSGen wN c (mkConst ``Specimen.Search)
    let wG ← workerAtSGen.atSGen wN c
    let st ← forallTelescopeReducing (← inferType wG) fun xs _ => do
      -- each instance it draws a type parameter's values through, with that instance's law
      let rec withLaws (i : Nat) (laws : Array Expr) : MetaM Expr := do
        if h : i < xs.size then
          let x := xs[i]
          let ty ← inferType x
          if (← x.fvarId!.getBinderInfo).isInstImplicit && ty.isAppOfArity ``Basalt.ArbitrarySized 1 then
            let lawTy ← mkAppOptM ``ArbitrarySizedSearch #[ty.appArg!, x]
            withLocalDecl `law .instImplicit lawTy fun l => withLaws (i + 1) (laws.push l)
          else withLaws (i + 1) laws
        else
          let body ← mkAppM ``SearchFinds #[mkAppN wS xs, mkAppN wG xs]
          mkForallFVars (xs ++ laws) body
      withLaws 0 #[]
    stmts := stmts.push (← Term.levelMVarToParam (← instantiateMVars st))
  stmts ← stmts.mapM instantiateMVars
  return stmts

/-- Prove `w.searchFinds` for the enumerator workers `ws` of one block, with `facts` for the
enumerators they call. -/
def proveSearchFinds (ws : Array Name) (facts : Array Term) : TermElabM Unit := do
  let stmts ← searchFindsStatements ws
  let lps := (stmts.foldl (fun acc st => collectLevelParams acc st) {}).params.toList
  let conj ← withLocalDeclD `fuel (Lean.mkConst ``Nat) fun fuel => do
    let parts := stmts.map fun s => s.bindingBody!.instantiate1 fuel
    mkForallFVars #[fuel] (parts.pop.foldr (fun p acc => mkAnd p acc) parts.back!)
  let k := ws.size
  let holes : Array Term ← (List.replicate k ()).toArray.mapM fun _ => `(?_)
  let wIds : Array Ident := ws.map mkIdent
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `(ih) else
    let mut t ← `(ih)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let factsAll : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts)
  let split ← if k == 1 then `(tactic| skip) else `(tactic| refine ⟨$holes,*⟩)
  let tac ← `(tactic| (
      intro fuel
      induction fuel with
      | zero => $split:tactic <;> intros <;> (first $[| unfold $wIds:ident]*) <;> (try unfold_arbitrary) <;> walk
      | succ f ih => $split:tactic <;> intros <;> (first $[| unfold $wIds:ident]*) <;> (try unfold_arbitrary) <;>
          walk [$factsAll,*]))
  -- Run as a tactic, not a `by` block, so a goal the walk leaves is reported rather than admitted.
  let goal ← mkFreshExprMVar conj
  let left ← Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.run goal.mvarId!
    (Lean.Elab.Tactic.withoutRecover (Lean.Elab.Tactic.evalTactic tac))
  unless left.isEmpty do
    let shown ← left.take 2 |>.mapM fun g => do return toString (← Meta.ppGoal g)
    timerLog s!"  searchFinds open goals ({left.length}):\n{("\n---\n".intercalate shown).take 6000}"
    throwError "the proof did not close: {left.length} goals the walk left"
  let pf ← instantiateMVars goal
  if pf.hasMVar then throwError "the proof did not close"
  if pf.hasSorry then throwError "the proof did not close: a goal was admitted"
  let blockName := ws[0]! ++ `searchFinds_block
  addDecl <| .thmDecl { name := blockName, levelParams := lps, type := ← instantiateMVars conj, value := pf }
  for i in [:k] do
    let stmt := stmts[i]!
    let v ← forallTelescope stmt fun xs _ => do
      let mut e := mkApp (Lean.mkConst blockName (lps.map mkLevelParam)) xs[0]!
      if k > 1 then
        for _ in [:i] do e ← mkAppM ``And.right #[e]
        if i < k - 1 then e ← mkAppM ``And.left #[e]
      mkLambdaFVars xs (mkAppN e (xs.extract 1 xs.size))
    addDecl <| .thmDecl { name := ws[i]! ++ `searchFinds, levelParams := lps, type := stmt, value := v }

/-- `proveSearchFinds`, each worker's base case and step a theorem of its own, which Lean proves in
parallel (`specimen.parallelProofs`); `false`, having done nothing, for statements with universe
parameters. -/
def proveSearchFindsParallel (ws : Array Name) (facts : Array Term) : CommandElabM Bool := do
  let stmts ← liftTermElabM <| searchFindsStatements ws
  unless stmts.all (collectLevelParams {} · |>.params.isEmpty) do return false
  let k := ws.size
  let ih := mkIdent `ih
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `($ih:ident) else
    let mut t ← `($ih:ident)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let factsAll : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts)
  let block := ws[0]! ++ `searchFinds_block
  let named := (Array.range k).map fun i => (ws[i]!, stmts[i]!)
  proveBlockParallel named "searchFinds" block
    (fun i => `(tactic| (intros; unfold $(mkIdent ws[i]!):ident; (try unfold_arbitrary); walk)))
    (fun i => `(tactic| (intros; unfold $(mkIdent ws[i]!):ident; (try unfold_arbitrary); walk [$factsAll,*])))
  liftTermElabM <| splitBlock block [] named `searchFinds
  return true

/-- `w.searchSound`, from `w.searchFinds` and `w.sound`: over `w.searchFinds`' binders, `w.sound` at
those that are not instance laws. -/
def proveSearchSound (wN : Name) : TermElabM Unit := do
  let ci ← getConstInfo (wN ++ `sound)
  -- At the universes `w.sound` states the worker at, which its relation fixed.
  let some (.const _ ls) := ci.type.find? fun e => e.isConst && e.constName! == wN
    | throwError "{wN}.sound does not mention {wN}"
  let findsN := wN ++ `searchFinds
  let findsC ← if (← getConstInfo findsN).levelParams.length == ls.length then pure (Lean.mkConst findsN ls)
    else mkConstWithFreshMVarLevels findsN
  let soundC := Lean.mkConst (wN ++ `sound) (ci.levelParams.map mkLevelParam)
  let v ← forallTelescope (← inferType findsC) fun xs _ => do
    let plain ← xs.filterM fun x => return !((← inferType x).isAppOf ``ArbitrarySizedSearch)
    let pf ← mkAppM ``search_accepts #[mkAppN findsC xs, mkAppN soundC plain]
    let pfTy ← inferType pf
    forallTelescope pfTy fun ys _ => mkLambdaFVars (xs ++ ys) (mkAppN pf ys)
  let v ← instantiateMVars v
  let ty ← instantiateMVars (← inferType v)
  let lps' := (collectLevelParams {} ty).params.toList
  addDecl <| .thmDecl { name := wN ++ `searchSound, levelParams := lps', type := ty, value := v }

initialize specimenEnumSoundHook.set <| some fun enums sounds => do
  let facts : Array Term := sounds.filterMap fun n =>
    if n.getString! == "searchFinds" then
      some ⟨mkNode ``Lean.Parser.Term.explicit #[mkAtom "@", mkIdent n]⟩ else none
  try
    -- Proved before, ahead of the soundness the second needs, in a block with checkers.
    let todo ← enums.filterM fun w => return !(← getEnv).contains (w ++ `searchFinds)
    unless todo.isEmpty do
      let par := Lean.Option.get (← getOptions) specimen.parallelProofs
      unless par && (← proveSearchFindsParallel todo facts) do
        liftTermElabM <| proveSearchFinds todo facts
    for w in enums do
      let env ← getEnv
      if env.contains (w ++ `sound) && env.contains (w ++ `searchFinds) && !env.contains (w ++ `searchSound) then
        liftTermElabM <| proveSearchSound w
  catch e =>
    timerLog s!"    searchFinds error: {(← e.toMessageData.toString).take 1500}"
    logWarning m!"specimen.emitSound: enumerators {", ".intercalate (enums.toList.map toString)} \\
      not proved to search soundly: {e.toMessageData}"

end Specimen.Correctness
