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

/-- `specimenBody` from the worker's definition as written (structural recursion's `EqnInfo`), its
equation checked by `rfl`; `false`, having added nothing, where that is not to be had. -/
def specimenBodyByRfl (w : Name) : TermElabM Bool := do
  let some info := Lean.Elab.Structural.eqnInfoExt.find? (← getEnv) w | return false
  try
    let lps := info.levelParams
    let wC := Lean.mkConst w (lps.map mkLevelParam)
    -- `∀ {G} [insts] fuel initSize size args, W … = value …`: the equations are stated at every
    -- monad and instances, which `rfl` proves alike, so that one rewrites the generators' goals (at
    -- `SGen`) and the searches' (at `Search`)
    let ety0 ← forallTelescope info.type fun xs _ => do
      mkForallFVars xs (← mkEq (mkAppN wC xs) (info.value.beta xs))
    let res ← forallTelescope ety0 fun all eq => do
      unless all.size ≥ 10 do throwError "expected `G insts fuel initSize size …`"
      let pre := all.extract 0 7
      let xs := all.extract 7 all.size
      let initSize := xs[1]!; let rest := xs.extract 2 xs.size
      let some (_, lhs, rhs) := eq.eq? | throwError "not an equation"
      let some m ← matchMatcherApp? rhs | throwError "the body is not a `match` on the fuel"
      let wHead := lhs.getAppFn.beta (lhs.getAppArgs.extract 0 (lhs.getAppNumArgs - xs.size))
      -- the fuel-`0` case, `W 0 initSize … = <its branch>`, also by `rfl`
      let zalt := m.alts[0]!
      let zbody := match zalt with
        | .lam _ _ b _ => b.instantiate1 (mkConst ``Unit.unit)
        | b => b
      let zlhs := mkAppN wHead (#[mkNatLit 0, initSize] ++ rest)
      let zthm ← mkForallFVars (pre ++ #[initSize] ++ rest) (← mkEq zlhs zbody)
      let zpf ← mkLambdaFVars (pre ++ #[initSize] ++ rest) (← mkEqRefl zlhs)
      lambdaTelescope m.alts[1]! fun ps body => do
        let fuel' := ps[0]!
        let bodyVal ← mkLambdaFVars (pre ++ #[initSize, fuel'] ++ rest) body
        let bodyTy ← inferType bodyVal
        -- `W.body`'s statement needs its constant: built from a local stand-in, then abstracted
        withLocalDeclD `bodyC bodyTy fun bodyF => do
          let lhs1 := mkAppN wHead (#[mkNatAdd fuel' (mkNatLit 1), initSize] ++ rest)
          let rhs1 := mkAppN bodyF (pre ++ #[initSize, fuel'] ++ rest)
          let bs := pre ++ #[fuel', initSize] ++ rest
          let thm ← mkLambdaFVars #[bodyF] (← mkForallFVars bs (← mkEq lhs1 rhs1))
          let pf ← mkLambdaFVars bs (← mkEqRefl lhs1)
          return (bodyVal, bodyTy, thm, pf, zthm, zpf)
    let (bodyVal, bodyTy, thmF, pf, zthm, zpf) := res
    let bodyName := w ++ `body
    let env₀ ← getEnv
    addDecl <| .defnDecl {
      name := bodyName, levelParams := lps, type := bodyTy, value := bodyVal,
      hints := .regular 0, safety := .safe }
    let bodyC := Lean.mkConst bodyName (lps.map mkLevelParam)
    let thm := thmF.beta #[bodyC]
    let ok ← (do addDecl <| .thmDecl { name := w ++ `eq_body, levelParams := lps, type := thm, value := pf }
                 pure true) <|> pure false
    unless ok do setEnv env₀
    if ok then
      -- the zero case is only a convenience: without it, a proof rewrites by `eq_def`
      let env₁ ← getEnv
      let ok0 ← (do addDecl <| .thmDecl { name := w ++ `eq_zero, levelParams := lps, type := zthm,
                                          value := zpf }
                    pure true) <|> pure false
      unless ok0 do setEnv env₁
      -- `W.eq_def`, which `unfold W` uses, by cases on the fuel from these two: realized by Lean
      -- instead, it is proved by splitting every `match` of the body, seconds for a large one
      if ok0 && !(← getEnv).contains (w ++ `eq_def) then
        let env₂ ← getEnv
        let okd ← (do
            let st := ety0
            let pf ← forallTelescope st fun all _ => do
              let pre := all.extract 0 7
              let fuel := all[7]!; let initSize := all[8]!; let rest := all.extract 9 all.size
              let motive ← withLocalDeclD `f (Lean.mkConst ``Nat) fun f => do
                let e ← instantiateForall st (pre ++ #[f] ++ #[initSize] ++ rest)
                mkLambdaFVars #[f] e
              let z := mkAppN (Lean.mkConst (w ++ `eq_zero) (lps.map mkLevelParam)) (pre ++ #[initSize] ++ rest)
              let sc ← withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
                mkLambdaFVars #[n] (mkAppN (Lean.mkConst (w ++ `eq_body) (lps.map mkLevelParam))
                  (pre ++ #[n, initSize] ++ rest))
              let c := mkAppN (Lean.mkConst ``Nat.casesOn [levelZero]) #[motive, fuel, z, sc]
              mkLambdaFVars all c
            Meta.check pf
            unless ← isDefEq (← inferType pf) st do throwError "eq_def: type mismatch"
            addDecl <| .thmDecl { name := w ++ `eq_def, levelParams := lps, type := st, value := pf }
            pure true) <|> pure false
        unless okd do setEnv env₂
    return ok
  catch _ => return false

/-- `W.body` and `W.eq_body : W (fuel' + 1) initSize size args = W.body initSize fuel' size args`, for
any derived worker `W`, one of a mutual block included: the body calls the block's workers at `fuel'`
as they are. Rewriting with `W.eq_body` brings in a constant rather than the body, which a walk then
unfolds itself; rewriting with `W`'s own unfolding equation instead costs as much as the body is
large, in every proof that does it. -/
def specimenBody (w : Name) : TermElabM Unit := do
  if (← getEnv).contains (w ++ `eq_body) then return
  -- Structurally recursive, the worker's equation holds by `rfl` from the definition as written,
  -- which Lean keeps; its unfolding lemma, proved by splitting every `match` of the body, costs
  -- seconds for a large one.
  if (← IO.getEnv "SPECIMEN_BODY_NORFL").isNone then
    if ← specimenBodyByRfl w then return
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
