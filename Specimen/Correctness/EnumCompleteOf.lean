import Specimen.Correctness.EnumSoundOf
import Specimen.Correctness.CheckComplete
import Specimen.Correctness.ParallelBlock

/-!
# A derived enumerator's search reaches what it enumerates

For each derived enumerator worker `W` (`specimen.completeAllSorts`):

  `W.searchHits : ∀ fuel iS size ins, SearchHits (W (G := SGen) …) (W (G := Search) …)`

by induction on the fuel and `walk`; and for its `EnumFor` instance, `EnumForSearch`,
which with `EnumForComplete` (its `W.complete`) gives the `CheckerSearchComplete` a checker that
searches with it needs.
-/

namespace Specimen.Correctness

open Lean Meta Elab Tactic Term Command

/-- `∀ fuel …, SearchHits (W at SGen …) (W at Search …)` (twice, as the statement pair the caller takes),
with, for each type parameter the worker draws (`[Basalt.ArbitrarySized α]`), that draw's
`ArbitrarySizedHits`. -/
def searchHitsStatements (ws : Array Name) : TermElabM (Array Expr × Array Expr) := do
  let mut hits : Array Expr := #[]
  let mut tots : Array Expr := #[]
  for wN in ws do
    let c ← mkConstWithFreshMVarLevels wN
    let wS ← workerAtSGen.atSGen wN c (mkConst ``Specimen.Search)
    let wG ← workerAtSGen.atSGen wN c
    let (h, t) ← forallTelescopeReducing (← inferType wG) fun xs _ => do
      let rec withLaws (i : Nat) (laws : Array Expr) : MetaM (Expr × Expr) := do
        if hi : i < xs.size then
          let x := xs[i]
          let ty ← inferType x
          if (← x.fvarId!.getBinderInfo).isInstImplicit && ty.isAppOfArity ``Basalt.ArbitrarySized 1 then
            let lawTy ← mkAppOptM ``ArbitrarySizedHits #[ty.appArg!, x]
            withLocalDecl `law .instImplicit lawTy fun l => withLaws (i + 1) (laws.push l)
          else withLaws (i + 1) laws
        else
          let h ← mkForallFVars (xs ++ laws) (← mkAppM ``SearchHits #[mkAppN wG xs, mkAppN wS xs])
          return (h, h)
      withLaws 0 #[]
    hits := hits.push (← Term.levelMVarToParam (← instantiateMVars h))
    tots := tots.push (← Term.levelMVarToParam (← instantiateMVars t))
  return (← hits.mapM instantiateMVars, ← tots.mapM instantiateMVars)

/-- The conjunction over the block, by one induction on the fuel, `tac0`/`tacS` closing each worker's
base case and step, the induction hypothesis `ih` its projections. -/
def proveFuelBlock (ws : Array Name) (stmts : Array Expr) (lem : Name)
    (tac0 tacS : Ident → Array Term → TermElabM (TSyntax `tactic)) : TermElabM Unit := do
  let conj ← withLocalDeclD `fuel (Lean.mkConst ``Nat) fun fuel => do
    let parts := stmts.map fun s => s.bindingBody!.instantiate1 fuel
    mkForallFVars #[fuel] (parts.pop.foldr (fun p acc => mkAnd p acc) parts.back!)
  let k := ws.size
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `(ih) else
    let mut t ← `(ih)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let holes : Array Term ← (List.replicate k ()).toArray.mapM fun _ => `(?_)
  let split ← if k == 1 then `(tactic| skip) else `(tactic| refine ⟨$holes,*⟩)
  let goal ← mkFreshExprMVar conj
  let gs ← Lean.Elab.Tactic.run goal.mvarId! (evalTactic (← `(tactic| (intro fuel; induction fuel))))
  let [g0, gS] := gs | throwError "{lem}: the induction"
  for (g, isZero) in [(g0, true), (gS, false)] do
    let gs ← Lean.Elab.Tactic.run g (do
      if !isZero then evalTactic (← `(tactic| rename_i f ih))
      evalTactic split)
    for i in [:k] do
      let w := mkIdent ws[i]!
      let tac ← if isZero then tac0 w ihs else tacS w ihs
      let t0 ← IO.monoMsNow
      -- a budget: a search the tactics cannot take apart fails the worker rather than the file
      let left ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 * 1000 }) <|
        Term.withoutErrToSorry <| Lean.Elab.Tactic.run gs[i]! (Tactic.withoutRecover (evalTactic tac))
      timerLog s!"  {lem} {ws[i]!} {if isZero then "zero" else "succ"} {(← IO.monoMsNow) - t0} ms"
      unless left.isEmpty do
        let shown ← left.take 2 |>.mapM fun g => do return toString (← Meta.ppGoal g)
        timerLog s!"  {lem} open goals ({left.length}):\n{("\n---\n".intercalate shown).take 4000}"
        throwError "{lem} {ws[i]!}: {left.length} goals left"
  let pf ← instantiateMVars goal
  if pf.hasMVar || pf.hasSorry then throwError "{lem}: the proof did not close"
  let lps := (stmts.foldl (fun acc st => collectLevelParams acc st) {}).params.toList
  let blockName := ws[0]! ++ (lem.appendAfter "_block")
  addDecl <| .thmDecl { name := blockName, levelParams := lps, type := ← instantiateMVars conj, value := pf }
  for i in [:k] do
    let stmt := stmts[i]!
    let v ← forallTelescope stmt fun xs _ => do
      let mut e := mkApp (Lean.mkConst blockName (lps.map mkLevelParam)) xs[0]!
      if k > 1 then
        for _ in [:i] do e ← mkAppM ``And.right #[e]
        if i < k - 1 then e ← mkAppM ``And.left #[e]
      mkLambdaFVars xs (mkAppN e (xs.extract 1 xs.size))
    addDecl <| .thmDecl { name := ws[i]! ++ lem, levelParams := lps, type := stmt, value := v }

/-- The derived instance of class `cls` whose body runs `w`. -/
def instanceRunning (wN : Name) (cls : Name) : MetaM (Option (Name × Expr)) := do
  let st := Meta.instanceExtension.getState (← getEnv)
  for (n, _) in st.instanceNames do
    let some ci := (← getEnv).find? n | continue
    let ty := ci.type
    unless ty.getForallBody.getAppFn.isConstOf cls do continue
    let some v := ci.value? | continue
    if (v.find? fun e => e.isConstOf wN).isSome then return some (n, ty)
  -- A scoped instance (`scoped derive_mutual`) is not among the active ones outside its namespace: the
  -- declarations of this module, then, whose type is the class's (only when none is active, so
  -- that the common case scans nothing more).
  for (n, ci) in (← getEnv).constants.map₂.toList do
    unless ci.type.getForallBody.getAppFn.isConstOf cls do continue
    let some v := ci.value? | continue
    if (v.find? fun e => e.isConstOf wN).isSome then return some (n, ci.type)
  return none

/-- Each enumerator's `EnumForSearch`, from its `searchHits`. -/
def addEnumForSearchInsts (ws : Array Name) : TermElabM Unit := do
  for wN in ws do
    let some (instN, instTy) ← instanceRunning wN ``EnumFor | continue
    let ilps := (← getConstInfo instN).levelParams
    let goal ← forallTelescopeReducing instTy fun ps body => do
      let α := body.appFn!.appArg!
      let P := body.appArg!
      let rec withLaws (i : Nat) (laws : Array Expr) : MetaM Expr := do
        if hi : i < ps.size then
          let x := ps[i]
          let ty ← inferType x
          if (← x.fvarId!.getBinderInfo).isInstImplicit && ty.isAppOfArity ``Basalt.ArbitrarySized 1 then
            let lawTy ← mkAppOptM ``ArbitrarySizedHits #[ty.appArg!, x]
            withLocalDecl `law .instImplicit lawTy fun l => withLaws (i + 1) (laws.push l)
          else withLaws (i + 1) laws
        else mkForallFVars (ps ++ laws) (← mkAppOptM ``EnumForSearch #[α, P, mkAppN (Lean.mkConst instN (ilps.map mkLevelParam)) ps])
      withLaws 0 #[]
    let nIns ← forallTelescope (← getConstInfo (wN ++ `searchHits)).type fun xs _ => do
      return (← (xs.extract 3 xs.size).filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit).size
    let holes := String.intercalate " " (List.replicate nIns "_")
    let src := s!"by\n  intros\n  exact ⟨fun s l => {wN ++ `searchHits} (s + 1) l s {holes}⟩"
    let stx ← match Parser.runParserCategory (← getEnv) `term src with
      | .ok stx => pure stx
      | .error e => throwError "EnumForSearch proof: {e}"
    let pf ← Term.withoutErrToSorry do
      let pf ← elabTermEnsuringType stx goal
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars pf
    if pf.hasMVar || pf.hasSorry then throwError "EnumForSearch {wN}: the proof did not close"
    let name := wN ++ `instSearch
    addDecl <| .thmDecl { name, levelParams := ilps, type := goal, value := pf }
    addInstance name .global (eval_prio default)

/-- `W.searchHits` for an enumerator block, and each worker's `EnumForSearch`. -/
def proveSearchHits (ws : Array Name) : TermElabM Unit := do
  let (hits, _) ← searchHitsStatements ws
  proveFuelBlock ws hits `searchHits
    (fun w _ => `(tactic| (intros; unfold $w:ident; walk)))
    (fun w ihs => `(tactic| (intros; unfold $w:ident; walk [$ihs,*])))
  addEnumForSearchInsts ws


/-- `proveSearchHits`, each worker's base case and step a theorem of its own, which Lean proves in
parallel (`specimen.parallelProofs`); `false`, having done nothing, for statements with universe
parameters. -/
def proveSearchHitsParallel (ws : Array Name) : CommandElabM Bool := do
  let (hits, _) ← liftTermElabM <| searchHitsStatements ws
  unless hits.all (collectLevelParams {} · |>.params.isEmpty) do return false
  let k := ws.size
  let ih := mkIdent `ih
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `($ih:ident) else
    let mut t ← `($ih:ident)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let block := ws[0]! ++ `searchHits_block
  let named := (Array.range k).map fun i => (ws[i]!, hits[i]!)
  proveBlockParallel named "searchHits" block
    (fun i => do `(tactic| (intros; unfold $(mkIdent ws[i]!):ident; walk)))
    (fun i => do `(tactic| (intros; unfold $(mkIdent ws[i]!):ident; walk [$ihs,*])))
  liftTermElabM do
    splitBlock block [] named `searchHits
    addEnumForSearchInsts ws
  return true

end Specimen.Correctness
