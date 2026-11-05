import Specimen.Correctness.SuccObs
import Specimen.Debug
import Specimen.Correctness.CheckHyps
import Specimen.Correctness.ParallelBlock

/-!
# A derived worker is sound for its relation

`#specimen_sound [W₁ for R₁ outputs [i, …], …] using [f, …]` states and proves, for each derived
worker `Wₖ` of relation `Rₖ` in the mode producing `Rₖ`'s arguments `i, …` (counted over all of
`Rₖ`'s binders, implicit ones included, as in the workers' names):

  `Wₖ.sound : ∀ fuel initSize size ins, succObs.spec (Wₖ fuel initSize size ins) (fun v => Rₖ …)`

with the inputs and the projections of the produced value `v` at their positions. The workers of one
command are proved together, so a mutual block is one command. The proof is fuel induction; at each
level, the walk over a worker's unfolding with the previous level's laws and the callees' laws
`f, …` as facts, and, at each leaf, one of the relation's constructors (`ctor_leaf`).
-/

namespace Specimen.Correctness

open Lean Meta Elab Tactic Term Command

syntax "ctor_leaf" : tactic

/-- `ctor_leaf` within `ctor_leaf`, for a premise: no leaf preparation, and no report on failure. (A
syntax of its own rather than a depth counter, which proofs elaborated in parallel would share.) -/
syntax "ctor_leaf_nested" : tactic


initialize specimenCheckExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := NameSet.insert
    addImportedFn := fun as => as.foldl (fun s a => a.foldl NameSet.insert s) {} }

/-- `(test) = true → R …`: what a hand-written checker's passing test establishes, for a leaf of a
derived generator's soundness proof whose check that checker decided. `ctor_leaf` tries these before
`R`'s constructors. -/
initialize registerBuiltinAttribute {
  name := `specimen_check
  descr := "a hand-written checker's law, `(test) = true → R …`, for derived generators' soundness proofs"
  add := fun decl _ _ => modifyEnv (specimenCheckExt.addEntry · decl) }

/-- What a goal or a law's conclusion is about: the relation, and whether it is negated. -/
private def checkKey (t : Expr) : MetaM (Option (Bool × Name)) := do
  let t ← whnfR (← instantiateMVars t)
  if t.isAppOfArity ``Not 1 then
    return (← whnfR t.appArg!).getAppFn.constName?.map (true, ·)
  return t.getAppFn.constName?.map (false, ·)

/-- Close `g` by a `@[specimen_check]` law about its relation (negated or not), from a hypothesis. -/
private def byCheckLaw (g : MVarId) : TacticM Bool := do
  let some key ← checkKey (← g.getType) | return false
  for l in (specimenCheckExt.getState (← getEnv)).toArray do
    -- Not reducing: that would read a law's `¬ R …` as `R … → False`.
    let lk ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels l)) fun _ b => checkKey b
    unless lk == some key do continue
    let saved ← saveState
    try
      setGoals [g]
      evalTactic (← `(tactic| (apply $(mkIdent l):ident <;> assumption)))
      if (← getUnsolvedGoals).isEmpty then return true
    catch _ => pure ()
    saved.restore
  return false

/-- Run `tac` on `g` alone; keep its effect only if it closes `g`. -/
private def closesOn (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [g]
    evalTactic tac
    if (← getUnsolvedGoals).isEmpty then return true
    saved.restore; return false
  catch _ => saved.restore; return false

/-- Close a constructor's premises `gs`. First every premise a hypothesis matches, repeatedly, since a
match can fix a witness another premise shares. Then each remaining proposition: by `rfl` while it still
has an unfixed witness, otherwise by `rfl`, `decide` or `omega`, and with `full` also `simp_all` or a
constructor, recursively. A data premise (a witness) is never built: it must have been fixed. -/
private partial def closePremises (gs : List MVarId) (full : Bool) : TacticM Bool := do
  let open_ (gs : List MVarId) := gs.filterM fun g => return !(← g.isAssigned)
  -- How many hypotheses `g` unifies with, committing to none.
  let hypMatches (g : MVarId) : TacticM Nat := g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let mut n := 0
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let saved ← Meta.saveState
      let ok ← try isDefEq d.type ty catch _ => pure false
      saved.restore
      if ok then n := n + 1
    return n
  -- A premise only one hypothesis matches first: a witness it fixes is the right one, where a greedy
  -- first match (`ValidEntityType ?ety₁` against either of two types) can fix a wrong one, which no
  -- later premise can undo. Then, if none is unique, one of several, as before.
  let rec byHyps (gs : List MVarId) : TacticM (List MVarId) := do
    let mut left := []
    let mut progress := false
    let mut ambiguous : Option MVarId := none
    for g in ← open_ gs do
      if ← g.isAssigned then continue
      -- A witness is fixed by the premises that mention it, never by a hypothesis of its type.
      unless ← isProp (← g.getType) do left := left ++ [g]; continue
      let n ← hypMatches g
      if (← IO.getEnv "CHK_DEBUG").isSome then
        IO.eprintln s!"byHyps: {n} match {← ppExpr (← instantiateMVars (← g.getType))}"
      -- (Not `n == 1 && (← closesOn …)`: the lifted `←` would run the greedy match on every premise.)
      let closed ← if n == 1 then closesOn g (← `(tactic| assumption)) else pure false
      if closed then progress := true
      else
        if n > 1 && ambiguous.isNone then ambiguous := some g
        left := left ++ [g]
    if progress then return ← byHyps left
    if let some g := ambiguous then
      if ← closesOn g (← `(tactic| assumption)) then return ← byHyps (left.erase g)
    return left
  let gs ← byHyps gs
  for g in gs do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    unless ← isProp ty do continue
    let closed ← if ty.hasExprMVar then closesOn g (← `(tactic| rfl))
      else if ← closesOn g (← `(tactic| first | rfl | decide | omega)) then pure true
      else if ← byCheckLaw g then pure true
      else if full then closesOn g (← `(tactic| first | (simp_all; done) | ctor_leaf_nested))
      else pure false
    unless closed do
      if (← IO.getEnv "CHK_DEBUG").isSome then IO.eprintln s!"closePremises: stuck on {← ppExpr ty}"
      return false
  return (← open_ (← byHyps gs)).isEmpty

/-- A negated decided check, `(!decide p) = true`, as the proposition `¬ p`. Only for `decide`: a
hand-written checker's negated test keeps its shape, which its `@[specimen_check]` law is stated in. -/
theorem not_decide_eq_true_iff {p : Prop} [Decidable p] : ((!decide p) = true) ↔ ¬ p := by
  simp

/-- One constructor search for the main goal (see `ctor_leaf`); `top` for the leaf itself. -/
private def ctorLeafCore (top : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  unless ← isProp (← goal.getType) do throwError "ctor_leaf: not a proposition"
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some head := ty.getAppFn.constName? | throwError "ctor_leaf: not an inductive goal"
  let some (.inductInfo iv) := (← getEnv).find? head | throwError "ctor_leaf: {head} is not inductive"
  let t0 ← IO.monoNanosNow
  -- A check a hand-written checker decided: its law, from the test's hypothesis.
  if ← byCheckLaw goal then setGoals []; return
  for full in [false, true] do
    for c in iv.ctors do
      let saved ← saveState
      try
        setGoals [goal]
        timeIn "ctor_leaf.apply" (evalTactic (← `(tactic| apply $(mkIdent c):ident)))
        let ok ← timeIn (if full then "ctor_leaf.premises(full)" else "ctor_leaf.premises") do
          closePremises (← getGoals) full
        if ok then
          if full then
            timerLog s!"  ctor_leaf {head} needed the full search: {c.getString!}, \
              {((← IO.monoNanosNow) - t0) / 1000000} ms"
          setGoals []
          return
      catch _ => pure ()
      saved.restore
  -- Only where the search gave up, not each failed attempt inside it.
  if top then
    let shown ← Meta.ppGoal goal
    timerLog s!"  ctor_leaf FAILED on {head} after {((← IO.monoNanosNow) - t0) / 1000000} ms:\n{(toString shown).take 12000}"
  throwError "ctor_leaf: no constructor of {head} closes\n{MessageData.ofGoal goal}"

/-- Close a goal `R …`, a proposition, by one of `R`'s constructors, its premises as `closePremises`
does; each constructor in turn, backtracking.

A first pass tries each constructor with the cheap closers alone. The walk leaves the premises a
generator established as hypotheses, so that pass usually finds the constructor; the full search, whose
`simp_all` and recursion are costly against the many constructors and large contexts of a relation like
Cedar's `HasType`, runs only when it does not. -/
elab_rules : tactic | `(tactic| ctor_leaf) => withMainContext do
  -- At a leaf: what the generator checked by `decide` is stated, and values a sub-generator or a check
  -- determined by an equation are substituted.
  do
    evalTactic (← `(tactic| try simp only [Specimen.Correctness.not_decide_eq_true_iff, decide_eq_true_eq, decide_eq_false_iff_not] at *))
    -- A pair a sub-generator produced, into its components, so that an equation about one of them
    -- (`p.1 = .set s`) is one `subst_vars` can use.
    let mut split := false
    for _ in [:16] do
      let some p ← withMainContext do
          (← getLCtx).findDeclM? fun d => do
            if d.isImplementationDetail then return none
            return if (← whnfR (← instantiateMVars d.type)).isAppOfArity ``Prod 2 then some d.fvarId else none
        | break
      let gs ← (← getMainGoal).cases p
      replaceMainGoal (gs.map (·.mvarId)).toList
      split := true
    if split then evalTactic (← `(tactic| try dsimp only at *))
  evalTactic (← `(tactic| try subst_vars))
  ctorLeafCore true

elab_rules : tactic | `(tactic| ctor_leaf_nested) => withMainContext do
  evalTactic (← `(tactic| try subst_vars))
  ctorLeafCore false

/-- The relation applied at the worker's inputs and the produced value `v`'s projections. -/
private def soundPost (r : Expr) (outIdx : Array Nat) (ins : Array Expr) (outTy : Expr) :
    MetaM Expr := do
  let nArgs ← forallTelescopeReducing (← inferType r) fun xs _ => return xs.size
  withLocalDeclD `v outTy fun v => do
    let k := outIdx.size
    let proj (p : Nat) : MetaM Expr := do
      if k == 1 then return v
      let mut e := v
      for _ in [:p] do e ← mkAppM ``Prod.snd #[e]
      if p < k - 1 then e ← mkAppM ``Prod.fst #[e]
      return e
    let mut args := #[]
    let mut nextIn := 0
    for a in [:nArgs] do
      if let some p := outIdx.idxOf? a then
        args := args.push (← proj p)
      else
        let some x := ins[nextIn]? | throwError "#specimen_sound: fewer inputs than the relation has arguments"
        args := args.push x
        nextIn := nextIn + 1
    let body := mkAppN r args
    -- Type-checking unifies the relation's universe levels with its arguments'.
    Meta.check body
    let body ← instantiateMVars body
    mkLambdaFVars #[v] body

/-- Facts about hand-written instances, for the proofs `specimen.emitSound` runs. -/
initialize specimenSoundExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := NameSet.insert
    addImportedFn := fun as => as.foldl (fun s a => a.foldl NameSet.insert s) {} }

/-- A law `succObs.spec (BacktrackGenFor.gen …) …` of a hand-written instance, used by the soundness
proofs of the generators `derive_mutual` derives under `specimen.emitSound`. -/
initialize registerBuiltinAttribute {
  name := `specimen_sound
  descr := "a generator law the soundness proofs of derived generators may use"
  add := fun decl _ _ => modifyEnv (specimenSoundExt.addEntry · decl) }

/-- A worker's inputs as the relation's arguments: after fuel and the two sizes, without the instances
a worker over a relation with type parameters takes for them. -/
def relInputs (xs : Array Expr) : MetaM (Array Expr) :=
  (xs.extract 3 xs.size).filterM fun x => return !(← x.fvarId!.getBinderInfo).isInstImplicit

/-- A worker's unfolding equation and soundness statement, `∀ fuel initSize size ins, succObs.spec
(w …) (fun v => r …)`, for the mode producing `r`'s arguments `outIdx`. -/
def soundStatement (wN rN : Name) (outIdx : Array Nat) (genEqn : Bool := true) :
    TermElabM (Name × Expr) := do
  -- Without `genEqn`, the equation's reserved name, which a proof that rewrites by it generates
  -- (once, wherever it is first needed: in a proof elaborated in parallel, off the main thread).
  let eqn ← if genEqn then
      let some eqn ← getUnfoldEqnFor? wN (nonRec := true) | throwError "no unfolding equation for {wN}"
      pure eqn
    else pure (wN ++ `eq_def)
  let wC ← workerAtSGen wN
  let rC ← mkConstWithFreshMVarLevels rN
  -- The relation at the worker's inputs fixes the worker's universes; what it leaves free is the
  -- theorems' own universe parameters.
  forallTelescopeReducing (← inferType wC) fun xs body => do
    Meta.check (← mkLambdaFVars xs (← soundPost rC outIdx (← relInputs xs) body.appArg!))
  let wC ← Term.levelMVarToParam (← instantiateMVars wC)
  let rC ← Term.levelMVarToParam (← instantiateMVars rC)
  let stmt ← forallTelescopeReducing (← inferType wC) fun xs body => do
    let post ← soundPost rC outIdx (← relInputs xs) body.appArg!
    let spec ← mkAppOptM ``Obs.spec #[none, none, none, none, none, none,
      some (Lean.mkConst ``succObs), none, some (mkAppN wC xs), some post]
    mkForallFVars xs spec
  return (eqn, ← instantiateMVars stmt)

/-- Prove each worker `w` sound for its relation `r` in the mode producing `r`'s arguments `outIdx`,
together, with `facts` for the callees: `w.sound_block` for the first, and `w.sound` for each. -/
def proveSound (items : Array (Name × Name × Array Nat)) (facts : Array Term) : TermElabM Unit := do
  -- Each worker: its name, unfolding equation, and statement.
  let mut ws : Array (Name × Name × Expr) := #[]
  let t0 ← IO.monoNanosNow
  let lap (what : String) : TermElabM Unit := do
    timerLog s!"    {what}: {((← IO.monoNanosNow) - t0) / 1000000} ms"
  for (wN, rN, outIdx) in items do
    let tw ← IO.monoNanosNow
    let (eqn, stmt) ← soundStatement wN rN outIdx
    ws := ws.push (wN, eqn, stmt)
    timerLog s!"      statement {wN.getString!.take 60}: {((← IO.monoNanosNow) - tw) / 1000000} ms"
  let lps := (ws.foldl (fun acc (w : Name × Name × Expr) => collectLevelParams acc w.2.2) {}).params.toList
  -- `∀ fuel, S₁ fuel ∧ … ∧ Sₖ fuel`
  let conj ← withLocalDeclD `fuel (Lean.mkConst ``Nat) fun fuel => do
    let parts := ws.map fun (_, _, s) => s.bindingBody!.instantiate1 fuel
    let c := parts.pop.foldr (fun p acc => mkAnd p acc) parts.back!
    mkForallFVars #[fuel] c
  let k := ws.size
  let holes : Array Term ← (List.replicate k ()).toArray.mapM fun _ => `(?_)
  let eqns : Array Ident := ws.map fun (_, e, _) => mkIdent e
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `(ih) else
    let mut t ← `(ih)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let generic : Array Term := #[← `(@succ_gen_eqRight), ← `(@succ_gen_eqLeft),
    ← `(@succ_enum_eqRight), ← `(@succ_enum_eqLeft)]
  let factsAll : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts ++ generic)
  let tac ← if k == 1 then `(by
      intro fuel
      induction fuel with
      | zero => intros; timed "rw" (first $[| rw [$eqns:ident]]*); timed "walk" walk
      | succ f ih =>
        intros
        timed "rw" (first $[| rw [$eqns:ident]]*)
        timed "unfold" (unfold_gen_instances [$factsAll,*])
        timed "walk" (walk [$factsAll,*])
        timed "ctor_leaf" (all_goals ((try check_hyps [$factsAll,*]); ctor_leaf)))
    else do
      -- One case per worker, its steps timed under its own name, to see which worker a block's time is.
      -- `specimen_gen_<Rel>_<outs>__<module>`: the relation and mode
      let short (n : Name) : String :=
        let s := n.getString!
        let s := (s.splitOn "__").head!
        (s.splitOn "Relational_").getLast?.getD s
      let profile := (← IO.getEnv "SPECIMEN_WALK_PROFILE").isSome
      let names : Array Ident := (Array.range k).map fun i => mkIdent (Name.mkSimple s!"w{i}")
      let named : Array Term ← names.mapM fun n => `(?$n)
      let mut zt ← `(tactic| refine ⟨$named,*⟩)
      let mut st ← `(tactic| refine ⟨$named,*⟩)
      for i in [:k] do
        let (wN, e, _) := ws[i]!
        let eq := mkIdent e
        let lw := Syntax.mkStrLit s!"walk:{short wN}"
        let lc := Syntax.mkStrLit s!"ctor_leaf:{short wN}"
        let zi ← `(tactic| (intros; rw [$eq:ident]; walk))
        let marker := Syntax.mkStrLit s!"WALK {short wN}"
        let walkT ← if profile then
            `(tactic| (trace $marker; set_option basalt.walk.profile true in walk [$factsAll,*]))
          else `(tactic| walk [$factsAll,*])
        let si ← `(tactic| (
          intros
          timed "rw" (rw [$eq:ident])
          timed "unfold" (unfold_gen_instances [$factsAll,*])
          timed $lw $walkT
          timed $lc (all_goals ((try check_hyps [$factsAll,*]); ctor_leaf))))
        zt ← `(tactic| ($zt; case $(names[i]!):ident => $zi:tactic))
        st ← `(tactic| ($st; case $(names[i]!):ident => $si:tactic))
      `(by
        intro fuel
        induction fuel with
        | zero => $zt:tactic
        | succ f ih => $st:tactic)
  lap s!"statements ({k} workers, {facts.size} facts)"
  let pf ← elabTermEnsuringType tac conj
  synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  lap "tactic"
  reportTacticTimes "tactic"
  if pf.hasMVar then throwError "the proof did not close"
  -- `all_goals` admits a goal its tactic fails on, after logging the error; such a proof is no proof.
  if pf.hasSorry then throwError "the proof did not close: a leaf was admitted"
  let auxName := ws[0]!.1 ++ `sound_block
  let conj ← instantiateMVars conj
  addDecl <| .thmDecl { name := auxName, levelParams := lps, type := conj, value := pf }
  lap "kernel"
  for i in [:k] do
    let (wN, _, stmt) := ws[i]!
    let v ← forallTelescopeReducing stmt fun xs _ => do
      let mut e := mkApp (Lean.mkConst auxName (lps.map mkLevelParam)) xs[0]!
      if k > 1 then
        for _ in [:i] do e ← mkAppM ``And.right #[e]
        if i < k - 1 then e ← mkAppM ``And.left #[e]
      mkLambdaFVars xs (mkAppN e (xs.extract 1 xs.size))
    addDecl <| .thmDecl { name := wN ++ `sound, levelParams := lps, type := stmt, value := v }

/-- `wᵢ.<suffix>` for each worker `wᵢ` with statement `Sᵢ`, from `block : ∀ fuel, S₁ fuel ∧ … ∧ Sₖ fuel`. -/
def splitBlock (block : Name) (lps : List Name) (ws : Array (Name × Expr)) (suffix : Name)
    (suffixes : Array Name := #[]) : TermElabM Unit := do
  let k := ws.size
  for i in [:k] do
    let (wN, stmt) := ws[i]!
    let suffix := suffixes.getD i suffix
    let v ← forallTelescopeReducing stmt fun xs _ => do
      let mut e := mkApp (Lean.mkConst block (lps.map mkLevelParam)) xs[0]!
      if k > 1 then
        for _ in [:i] do e ← mkAppM ``And.right #[e]
        if i < k - 1 then e ← mkAppM ``And.left #[e]
      mkLambdaFVars xs (mkAppN e (xs.extract 1 xs.size))
    addDecl <| .thmDecl { name := wN ++ suffix, levelParams := lps, type := stmt, value := v }

/-- `proveSound`, each worker's base case and step a theorem of its own, which Lean proves in
parallel (`specimen.parallelProofs`). `false`, having done nothing, for statements with universe
parameters, which `proveBlockParallel` does not state. -/
def proveSoundParallel (items : Array (Name × Name × Array Nat)) (facts : Array Term) :
    CommandElabM Bool := do
  let ws ← liftTermElabM <| items.mapM fun (wN, rN, outIdx) => do
    let (e, st) ← soundStatement wN rN outIdx (genEqn := false)
    return (wN, e, st)
  let lps := (ws.foldl (fun acc (w : Name × Name × Expr) => collectLevelParams acc w.2.2) {}).params.toList
  unless lps.isEmpty do return false
  let k := ws.size
  let ih := mkIdent `ih
  let ihs : Array Term ← (Array.range k).mapM fun i => do
    if k == 1 then `($ih:ident) else
    let mut t ← `($ih:ident)
    for _ in [:i] do t ← `($t.2)
    if i < k - 1 then t ← `($t.1)
    return t
  let generic : Array Term := #[← `(@succ_gen_eqRight), ← `(@succ_gen_eqLeft),
    ← `(@succ_enum_eqRight), ← `(@succ_enum_eqLeft)]
  let factsAll : Syntax.TSepArray `term "," := Syntax.TSepArray.ofElems (ihs ++ facts ++ generic)
  let block := ws[0]!.1 ++ `sound_block
  let stmts := ws.map fun (w, _, st) => (w, st)
  proveBlockParallel stmts "sound" block
    (fun i => do
      let eq := mkIdent ws[i]!.2.1
      `(tactic| (intros; rw [$eq:ident]; walk)))
    (fun i => do
      let eq := mkIdent ws[i]!.2.1
      `(tactic| (
        intros
        rw [$eq:ident]
        unfold_gen_instances [$factsAll,*]
        walk [$factsAll,*]
        all_goals ((try check_hyps [$factsAll,*]); ctor_leaf))))
  liftTermElabM <| splitBlock block [] stmts `sound
  return true

initialize specimenSoundHook.set <| some fun gens sounds => do
  let tagged := (specimenSoundExt.getState (← getEnv)).toArray
  let facts : Array Term := (sounds ++ tagged).map fun n => ⟨mkNode ``Lean.Parser.Term.explicit
    #[mkAtom "@", mkIdent n]⟩
  try
    let items := gens.map fun (w, r, is) => (w, r, is.toArray)
    if Lean.Option.get (← getOptions) specimen.parallelProofs then
      if ← proveSoundParallel items facts then return
    liftTermElabM <| proveSound items facts
  catch e =>
    timerLog s!"    sound error: {(← e.toMessageData.toString).take 1500}"
    logWarning m!"specimen.emitSound: {", ".intercalate (gens.toList.map (toString ·.1))} not proved \
      sound: {e.toMessageData}"

syntax soundItem := ident " for " ident " outputs " "[" num,* "]"
syntax "#specimen_sound " "[" soundItem,* "]" (" using " "[" term,* "]")? : command

elab_rules : command
  | `(#specimen_sound [$items,*] $[using [$fs,*]]?) => do
    let facts : Array Term := match fs with
      | some fs => fs.getElems
      | none => #[]
    liftTermElabM do
      let mut ws := #[]
      for it in items.getElems do
        let `(soundItem| $w:ident for $r:ident outputs [$is,*]) := it | throwError "bad item"
        ws := ws.push (← realizeGlobalConstNoOverloadWithInfo w, ← realizeGlobalConstNoOverloadWithInfo r,
          is.getElems.map (·.getNat))
      proveSound ws facts

end Specimen.Correctness
