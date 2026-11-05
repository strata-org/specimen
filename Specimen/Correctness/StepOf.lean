import Specimen.Correctness.SizeMeasure

/-!
# A derived worker is the fuel iteration of its step

The emitter writes a worker as `match fuel with | 0 => outOfFuel | fuel' + 1 => body`, where `body`
calls the worker only as `worker fuel' initSize …`. `#specimen_step W` reads the step off `W`'s
unfolding equation, abstracting those calls into the previous level, defines it as `W.step`, and
proves `W.eq_genRelB : W fuel initSize size i = genRelB (W.step initSize) fuel size i`, so the generic
theorems about `genRelB` and `fixGen` apply to the derived worker itself.

This version handles a worker with one input after the size; the inputs of a wider one would be
tupled.
-/

namespace Specimen.Correctness

open Lean Meta Elab Command Term

/-- The step and the bridge for one derived worker. -/
elab "#specimen_step " id:ident : command => liftTermElabM do
  let w ← realizeGlobalConstNoOverloadWithInfo id
  let some eqn ← getUnfoldEqnFor? w (nonRec := true) | throwError "no unfolding equation for {w}"
  let sgen := Lean.mkConst ``SGen
  let eqnC ← mkConstWithFreshMVarLevels eqn
  let e ← mkAppOptM' eqnC #[some sgen, none, none, none, none, none, none]
  let ety ← instantiateMVars (← inferType e)
  -- `∀ fuel initSize size i, W … fuel initSize size i = match fuel with …`
  let (stepVal, stepTy) ← forallTelescopeReducing ety fun xs eq => do
    unless xs.size == 4 do throwError "#specimen_step: expected `fuel initSize size input`, got {xs.size}"
    let fuel := xs[0]!; let initSize := xs[1]!; let size := xs[2]!; let i := xs[3]!
    let some (_, lhs, rhs) := eq.eq? | throwError "not an equation"
    let wPrefix := lhs.getAppFn.beta (lhs.getAppArgs.extract 0 (lhs.getAppNumArgs - 4))
    let some m ← matchMatcherApp? rhs | throwError "#specimen_step: the body is not a `match` on the fuel"
    let alt := m.alts[1]!
    let iTy ← inferType i
    let outTy ← inferType lhs
    lambdaTelescope alt fun ps body => do
      let fuel' := ps[0]!
      let prevTy ← mkArrow (Lean.mkConst ``Nat) (← mkArrow iTy outTy)
      withLocalDeclD `prev prevTy fun prev => do
        let rec_ := mkAppN wPrefix #[fuel', initSize]
        let body' := body.replace fun e => if e == rec_ then some prev else none
        if body'.containsFVar fuel'.fvarId! then
          throwError "#specimen_step: the body uses the fuel other than in a recursive call"
        let _ := fuel
        let v ← mkLambdaFVars #[initSize, prev, size, i] body'
        return (v, ← inferType v)
  let stepName := w ++ `step
  addDecl <| .defnDecl {
    name := stepName, levelParams := [], type := stepTy, value := stepVal,
    hints := .abbrev, safety := .safe }
  setReducibleAttribute stepName
  -- The bridge, by induction on the fuel.
  let stepC := Lean.mkConst stepName
  let thmTy ← forallTelescopeReducing ety fun xs eq => do
    let some (_, lhs, _) := eq.eq? | throwError "not an equation"
    let rhs ← mkAppM ``genRelB #[mkApp stepC xs[1]!, xs[0]!, xs[2]!, xs[3]!]
    mkForallFVars xs (← mkEq lhs rhs)
  let pf ← elabTermEnsuringType (← `(by
      intro fuel
      induction fuel with
      | zero => intro initSize size i; rw [$(mkIdent eqn):ident]; rfl
      | succ f ih =>
        intro initSize size i
        rw [$(mkIdent eqn):ident]
        have hf := funext fun s => funext fun j => ih initSize s j
        exact congrArg (fun p => $(mkIdent stepName):ident initSize p size i) hf))
    thmTy
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  if pf.hasMVar then throwError "#specimen_step: the bridge proof did not close"

  addDecl <| .thmDecl { name := w ++ `eq_genRelB, levelParams := [], type := thmTy, value := pf }

/-- `W.body` and `W.eq_body : W (fuel' + 1) initSize size args = W.body initSize fuel' size args`, for
any derived worker `W`, one of a mutual block included: the body calls the block's workers at `fuel'`
as they are. Rewriting with `W.eq_body` brings in a constant rather than the body, which a walk then
unfolds itself; rewriting with `W`'s own unfolding equation instead costs as much as the body is
large, in every proof that does it. -/
def specimenBody (w : Name) : TermElabM Unit := do
  if (← getEnv).contains (w ++ `eq_body) then return
  let some eqn ← getUnfoldEqnFor? w (nonRec := true) | throwError "no unfolding equation for {w}"
  let sgen := Lean.mkConst ``SGen
  -- At the worker's own universe parameters, which the body and its equation keep.
  let lps := (← getConstInfo w).levelParams
  let eqnC := Lean.mkConst eqn (lps.map mkLevelParam)
  let e ← mkAppOptM' eqnC #[some sgen, none, none, none, none, none, none]
  let ety ← instantiateMVars (← inferType e)
  let (bodyVal, thmTy, lhsHead) ← forallTelescopeReducing ety fun xs eq => do
    unless xs.size ≥ 3 do throwError "#specimen_body: expected `fuel initSize size …`"
    let initSize := xs[1]!; let rest := xs.extract 2 xs.size
    let some (_, lhs, rhs) := eq.eq? | throwError "not an equation"
    let some m ← matchMatcherApp? rhs | throwError "#specimen_body: the body is not a `match` on the fuel"
    lambdaTelescope m.alts[1]! fun ps body => do
      let fuel' := ps[0]!
      let v ← mkLambdaFVars (#[initSize, fuel'] ++ rest) body
      let wHead := lhs.getAppFn.beta (lhs.getAppArgs.extract 0 (lhs.getAppNumArgs - xs.size))
      return (v, ← inferType v, wHead)
  let _ := thmTy
  let bodyName := w ++ `body
  addDecl <| .defnDecl {
    name := bodyName, levelParams := lps, type := ← inferType bodyVal, value := bodyVal,
    hints := .regular 0, safety := .safe }
  let bodyC := Lean.mkConst bodyName (lps.map mkLevelParam)
  let thm ← forallTelescopeReducing ety fun xs _ => do
    let initSize := xs[1]!; let rest := xs.extract 2 xs.size
    withLocalDeclD `fuel' (Lean.mkConst ``Nat) fun fuel' => do
      let lhs := mkAppN lhsHead (#[mkNatAdd fuel' (mkNatLit 1), initSize] ++ rest)
      let rhs := mkAppN bodyC (#[initSize, fuel'] ++ rest)
      mkForallFVars (#[fuel', initSize] ++ rest) (← mkEq lhs rhs)
  let pf ← elabTermEnsuringType (← `(by intros; rw [$(mkIdent eqn):ident]; rfl)) thm
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  if pf.hasMVar then throwError "#specimen_body: the equation's proof did not close"
  addDecl <| .thmDecl { name := w ++ `eq_body, levelParams := lps, type := thm, value := pf }

@[inherit_doc specimenBody]
elab "#specimen_body " id:ident : command => liftTermElabM do
  specimenBody (← realizeGlobalConstNoOverloadWithInfo id)

end Specimen.Correctness
