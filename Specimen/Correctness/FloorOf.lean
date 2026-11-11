import Specimen.Correctness.SoundOf
import Specimen.Correctness.FloorLaws
import Specimen.Correctness.StepOf
import Specimen.Correctness.CheckSoundOf
import Specimen.Correctness.EnumSoundOf

/-!
# A derived floor is a lower bound

Under `specimen.deriveFloors` and `specimen.emitSound`, each derived generator worker `W` with a
derived floor gets

  `W.floorSound : ∀ fuel iS n ins, succObs.spec (W fuel iS n ins) (fun _ => W.floor ins ≤ n)`

— whatever it produces at size `n`, its floor is at most `n` — by fuel induction, the
walk over its body, and at each leaf `floor_close`: the rule the branch ran costs at most what its
split handed out.
-/

open Lean Meta Elab Tactic Term Command

namespace Specimen.Correctness

/-- The statement of `w.floorSound`. -/
def floorStatement (wN : Name) : TermElabM Expr := do
  -- At the worker's universe parameters; the floor's own are fixed by its arguments.
  let (wC, _) ← workerAtSGenParams wN
  let fl ← mkConstWithFreshMVarLevels (wN ++ `floor)
  forallTelescopeReducing (← inferType wC) fun xs _ => do
    let ins := xs.extract 3 xs.size
    -- the floor takes the inputs at its positions (`floorArgs`), when it records them
    let env ← getEnv
    let ins := match Specimen.floorArgPositions env wN with
      | some ps => ps.toArray.filterMap fun j => ins[j]?
      | none => ins
    let sz := xs[2]!
    let post ← withLocalDeclD `x (← inferType (mkAppN wC xs)).appArg! fun x => do
      mkLambdaFVars #[x] (← mkAppM ``LE.le #[← mkAppM' fl ins, sz])
    let spec ← mkAppOptM ``Obs.spec #[none, none, none, none, none, none,
      some (Lean.mkConst ``succObs), none, some (mkAppN wC xs), some post]
    mkForallFVars xs spec

/-- Prove the floors of the workers `ws` (one block, mutual or not) lower bounds together: one fuel
induction over the conjunction of their statements, as `#specimen_sound` does. -/
def proveFloorSounds (ws : Array Name) : TermElabM Unit := do
  for w in ws do specimenBody w
  let stmts ← ws.mapM fun w => do instantiateMVars (← floorStatement w)
  let conj ← withLocalDeclD `fuel (Lean.mkConst ``Nat) fun fuel => do
    let parts := stmts.map fun st => st.bindingBody!.instantiate1 fuel
    let c := parts.pop.foldr (fun p acc => mkAnd p acc) parts.back!
    mkForallFVars #[fuel] c
  let k := ws.size
  let holes : Array Term ← (List.replicate k ()).toArray.mapM fun _ => `(?_)
  -- The unfolding equation, not `eq_1`: that would have Lean derive every equation of the worker,
  -- splitting each of its `match`es, which on a body like Cedar's `HasType` takes minutes.
  let eq1s : Array Ident ← ws.mapM fun w => do
    let some e ← getUnfoldEqnFor? w (nonRec := true) | throwError "no unfolding equation for {w}"
    pure (mkIdent e)
  let eqBodies : Array Ident := ws.map (mkIdent <| · ++ `eq_body)
  let bodies : Array Ident := ws.map (mkIdent <| · ++ `body)
  let ihs : Array (TSyntax `rcasesPat) ← (Array.range k).mapM fun i =>
    `(rcasesPat| $(mkIdent (Name.mkSimple s!"ih{i}")):ident)
  let tac ← if k == 1 then `(by
      intro fuel
      induction fuel with
      | zero => intros; timed "rw" (first $[| rw [$eq1s:ident]]*); timed "walk" walk
      | succ f ih =>
        intro iS n
        intros
        timed "rw" (first $[| rw [$eqBodies:ident]]*)
        timed "delta" (first $[| delta $bodies:ident]*)
        cases n <;> timed "walk" walk <;> timed "floor_close" floor_close)
    else `(by
      intro fuel
      induction fuel with
      | zero => refine ⟨$holes,*⟩ <;> intros <;> timed "rw" (first $[| rw [$eq1s:ident]]*) <;>
          timed "walk" walk
      | succ f ih =>
        obtain ⟨$ihs,*⟩ := ih
        refine ⟨$holes,*⟩ <;> intro iS n <;> intros <;> timed "rw" (first $[| rw [$eqBodies:ident]]*) <;>
          timed "delta" (first $[| delta $bodies:ident]*) <;> cases n <;> timed "walk" walk <;>
          timed "floor_close" floor_close)
  let pf ← Term.withoutErrToSorry do
    let pf ← elabTermEnsuringType tac conj
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars pf
  reportTacticTimes "floor"
  if pf.hasMVar || pf.hasSorry then throwError "the proof did not close"
  let conj ← instantiateMVars conj
  let blockName := ws[0]! ++ `floorSound_block
  let lps := (collectLevelParams {} conj).params.toList
  addDecl <| .thmDecl { name := blockName, levelParams := lps, type := conj, value := pf }
  for i in [:k] do
    let stmt := stmts[i]!
    let v ← forallTelescope stmt fun xs _ => do
      let mut e := mkApp (Lean.mkConst blockName (lps.map mkLevelParam)) xs[0]!
      if k > 1 then
        for _ in [:i] do e ← mkAppM ``And.right #[e]
        if i < k - 1 then e ← mkAppM ``And.left #[e]
      mkLambdaFVars xs (mkAppN e (xs.extract 1 xs.size))
    addDecl <| .thmDecl { name := ws[i]! ++ `floorSound, levelParams := lps, type := stmt, value := v }

/-- `proveFloorSounds`, each worker's base case and step a theorem of its own, which Lean proves in
parallel (`specimen.parallelProofs`); `false`, having done nothing, for statements with universe
parameters. -/
def proveFloorSoundsParallel (ws : Array Name) : CommandElabM Bool := do
  -- No equations made here: each proof rewrites by its worker's reserved `eq_def`, generated where
  -- first needed, off the main thread.
  let (stmts, eq1s) ← liftTermElabM do
    let stmts ← ws.mapM fun w => do instantiateMVars (← floorStatement w)
    return (stmts, ws.map (· ++ `eq_def))
  unless stmts.all (collectLevelParams {} · |>.params.isEmpty) do return false
  let k := ws.size
  let ihs : Array (TSyntax `rcasesPat) ← (Array.range k).mapM fun i =>
    `(rcasesPat| $(mkIdent (Name.mkSimple s!"ih{i}")):ident)
  let ih := mkIdent `ih
  let block := ws[0]! ++ `floorSound_block
  let named := (Array.range k).map fun i => (ws[i]!, stmts[i]!)
  proveBlockParallel named "floorSound" block
    (fun i => `(tactic| (intros; rw [$(mkIdent eq1s[i]!):ident]; walk)))
    (fun i => do
      let eq := mkIdent eq1s[i]!
      let split ← if k == 1 then `(tactic| skip) else `(tactic| obtain ⟨$ihs,*⟩ := $ih:ident)
      `(tactic| (
        $split:tactic
        intro iS n
        intros
        rw [$eq:ident]
        cases n <;> walk <;> floor_close)))
  liftTermElabM <| splitBlock block [] named `floorSound
  return true

def proveFloorSound (wN : Name) : TermElabM Unit := proveFloorSounds #[wN]

initialize specimenFloorHook.set <| some fun gens => do
  -- TEMPORARY (timing): skip the floors' proofs
  if (← IO.getEnv "SPECIMEN_SKIP_FLOOR_PROOFS").isSome then return
  try
    if Lean.Option.get (← getOptions) specimen.parallelProofs && (← IO.getEnv "SPECIMEN_PAR_NO_FLOOR").isNone then
      if ← proveFloorSoundsParallel (gens.map (·.1)) then return
    liftTermElabM (proveFloorSounds (gens.map (·.1)))
  catch e =>
    timerLog s!"    floor error: {(← e.toMessageData.toString).take 1500}"
    logWarning m!"specimen.deriveFloors: \
    {", ".intercalate (gens.toList.map (toString ·.1))} floors not proved lower bounds: {e.toMessageData}"

end Specimen.Correctness
