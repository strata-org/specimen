import Specimen.DecOpt
import Specimen.Debug
import Lean

/-!
# What a checker's run establishes

The laws of `DecOpt`'s combinators for a run that accepts (`… = .ok true`), and `check_hyps`, which
breaks such hypotheses about a derived checker's run into the propositions they establish: the branch
of `checkerBacktrack` taken, each conjunct of `andOptList`, the `match`es, the decided propositions,
and, through the given laws, the relations of the calls. Used by the soundness proofs of derived
checkers (`Specimen.Correctness.CheckSoundOf`) and of the generators that call them.
-/

open Plausible

namespace DecOpt

theorem checkerBacktrack_aux_ok_true : ∀ (cs : List (Unit → Except GenError Bool)) (b : Bool),
    checkerBacktrack.aux cs b = .ok true → ∃ c ∈ cs, c () = .ok true
  | [], b, h => by cases b <;> simp [checkerBacktrack.aux, throw, throwThe, MonadExceptOf.throw] at h
  | c :: cs, b, h => by
    cases hc : c () with
    | ok v =>
      cases v
      · simp only [checkerBacktrack.aux, hc] at h
        obtain ⟨c', hc', h'⟩ := checkerBacktrack_aux_ok_true cs b h
        exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩
      · exact ⟨c, List.mem_cons_self, hc⟩
    | error e =>
      simp only [checkerBacktrack.aux, hc] at h
      obtain ⟨c', hc', h'⟩ := checkerBacktrack_aux_ok_true cs true h
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩

/-- A backtracking checker accepts only if one of its branches does. -/
theorem checkerBacktrack_ok_true {cs : List (Unit → Except GenError Bool)}
    (h : checkerBacktrack cs = .ok true) : ∃ c ∈ cs, c () = .ok true :=
  checkerBacktrack_aux_ok_true cs false h

theorem andOpt_ok_true {a b : Except GenError Bool} (h : andOpt a b = .ok true) :
    a = .ok true ∧ b = .ok true := by
  unfold andOpt at h; split at h
  · exact ⟨rfl, h⟩
  · cases h
  · split at h <;> cases h

theorem foldl_andOpt_ok_true : ∀ (bs : List (Except GenError Bool)) (a : Except GenError Bool),
    List.foldl andOpt a bs = .ok true → a = .ok true ∧ ∀ b ∈ bs, b = .ok true
  | [], a, h => ⟨h, by simp⟩
  | b :: bs, a, h => by
    obtain ⟨h1, h2⟩ := foldl_andOpt_ok_true bs (andOpt a b) h
    obtain ⟨ha, hb⟩ := andOpt_ok_true h1
    exact ⟨ha, by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hb, h2⟩⟩

/-- A conjunction of checks accepts only if each does. -/
theorem andOptList_ok_true {bs : List (Except GenError Bool)} (h : andOptList bs = .ok true) :
    ∀ b ∈ bs, b = .ok true := (foldl_andOpt_ok_true bs _ h).2

theorem decOpt_decidable_ok_true {P : Prop} [Decidable P] {n : Nat}
    (h : @DecOpt.decOpt P instDecOptOfDecidable n = .ok true) : P := by
  simp only [DecOpt.decOpt, Except.ok.injEq, decide_eq_true_eq] at h; exact h

end DecOpt

namespace Specimen.Correctness
open Lean Meta Elab Tactic

theorem ok_true_ne_ok_false : (Except.ok false : Except GenError Bool) ≠ .ok true := by simp
theorem negOpt_ok_true {a : Except GenError Bool} (h : DecOpt.negOpt a = .ok true) : a = .ok false := by
  unfold DecOpt.negOpt at h; split at h <;> simp_all

theorem decOpt_decidable_ok_false {P : Prop} [Decidable P] {n : Nat}
    (h : @DecOpt.decOpt P instDecOptOfDecidable n = .ok false) : ¬ P := by
  simp only [DecOpt.decOpt, Except.ok.injEq, decide_eq_false_iff_not] at h; exact h

/-- A hand-written checker's rejection, as the test its negative law (`(!test) = true → ¬ R …`)
reads. -/
theorem not_test_of_ok_false {b : Bool} (h : (Except.ok b : Except GenError Bool) = .ok false) :
    (!b) = true := by cases h; rfl

theorem ok_inj_true {b : Bool} (h : (Except.ok b : Except GenError Bool) = .ok true) : b = true := by
  cases h; rfl

/-- What `h : X = .ok false` establishes, where it can be read: of a decided proposition, its
negation; of a hand-written checker, its test's negation, which its negative law reads; of a value,
nothing to keep or a contradiction. A derived checker's rejection is not read (no law states it). -/
partial def rejected (facts : Array Expr) (unfolds : Array (Name × Name)) (hN : Name) : TacticM Unit :=
    withMainContext do
  let some h := (← getLCtx).findFromUserName? hN | return
  let some (_, lhs, _) := (← instantiateMVars h.type).eq? | return
  let lhs' ← whnfR lhs
  let hId := mkIdent hN
  let run (tac : TSyntax `tactic) : TacticM Unit := do evalTactic tac
  if lhs'.isAppOfArity ``Except.ok 3 then
    let v := lhs'.getArg! 2
    if v.isConstOf ``Bool.false then return
    if v.isConstOf ``Bool.true then run (← `(tactic| cases $hId:ident)); return
    let n := mkIdent (← mkFreshUserName `hnt).eraseMacroScopes
    run (← `(tactic| have $n:ident := not_test_of_ok_false $hId:ident))
    return
  if lhs.isAppOf ``DecOpt.decOpt then
    try
      let n := mkIdent (← mkFreshUserName `hnot).eraseMacroScopes
      run (← `(tactic| have $n:ident := decOpt_decidable_ok_false $hId:ident))
      return
    catch _ =>
      run (← `(tactic| simp only [DecOpt.decOpt] at $hId:ident))
      rejected facts unfolds hN
  let _ := facts; let _ := unfolds

/-- Break the hypotheses `h : X = .ok true` about a checker's run into what they establish: a branch of
`checkerBacktrack`, each conjunct of `andOptList`, a `match` split, a decided proposition, and, through
`facts` (the recursion's hypothesis and the callees' laws `W … = .ok true → R …`), the relation of a
call. Leaves the established propositions as hypotheses, or closes the goal where a run cannot succeed. -/
partial def checkHyps (facts : Array Expr) (unfolds : Array (Name × Name) := #[]) : TacticM Unit :=
    withMainContext do
  let some h ← (← getLCtx).findDeclRevM? fun d => do
      if d.isImplementationDetail then return none
      let t ← instantiateMVars d.type
      let some (_, lhs, rhs) := t.eq? | return none
      unless rhs.isAppOfArity ``Except.ok 3 && (rhs.getArg! 2).isConstOf ``Bool.true do return none
      unless (← inferType lhs).isAppOfArity ``Except 2 do return none
      return some d
    | return
  let lhs := (← instantiateMVars h.type).eq?.get!.2.1
  let lhs' ← whnfR lhs
  let fv := mkFVar h.fvarId
  let again := checkHyps facts unfolds
  let run (tac : TSyntax `tactic) : TacticM Unit := do
    let kind := tac.raw.getKind.toString.splitOn "." |>.getLast!
    timeIn s!"check_hyps.{kind}" (evalTactic tac)
  let hId := mkIdent h.userName
  -- a value
  if lhs'.isAppOfArity ``Except.ok 3 then
    let v := lhs'.getArg! 2
    if v.isConstOf ``Bool.true then (← getMainGoal).clear h.fvarId >>= (replaceMainGoal [·]); again; return
    if v.isConstOf ``Bool.false then run (← `(tactic| exact absurd $hId ok_true_ne_ok_false)); return
    -- `.ok b = .ok true`: the Bool test of a hand-written checker
    let p ← mkAppM ``ok_inj_true #[fv]
    let (_, g) ← (← (← getMainGoal).assert (← mkFreshUserName `htest) (← inferType p) p).intro1
    replaceMainGoal [← g.clear h.fvarId]; again; return
  if lhs'.isAppOfArity ``Except.error 3 || lhs.getAppFn.isConstOf ``throw || lhs.getAppFn.isConstOf ``throwThe then
    run (← `(tactic| cases $hId:ident)); return
  if lhs.isAppOfArity ``DecOpt.checkerBacktrack 1 then
    let c := mkIdent `chk_branch; let hc := mkIdent `chk_mem
    run (← `(tactic| obtain ⟨$c:ident, $hc:ident, $hId:ident⟩ := DecOpt.checkerBacktrack_ok_true $hId:ident))
    replaceMainGoal [← (← getMainGoal).clear h.fvarId]
    run (← `(tactic| simp only [List.mem_cons, List.mem_nil_iff, or_false] at $hc:ident))
    let n := ((lhs.getArg! 0).listLit?.map (·.2.length)).getD 1
    if n > 1 then
      let alts : Array (TSyntax `rcasesPat) ← (List.replicate n ()).toArray.mapM fun _ => `(rcasesPat| $hc:ident)
      run (← `(tactic| rcases $hc:ident with $[$alts]|*))
    run (← `(tactic| all_goals subst $hc:ident))
    if (← IO.getEnv "CHK_DEBUG").isSome then
      for g in ← getGoals do logInfo m!"after branch split:{indentD (MessageData.ofGoal g)}"
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      setGoals [g]
      try again; out := out ++ (← getGoals) catch e => throw e
    setGoals out.toList; return
  if lhs.isAppOfArity ``DecOpt.andOptList 1 then
    -- Fresh names, and the hypothesis read cleared by its id: a nested `andOptList` comes back here,
    -- and a fixed name would clear the new hypothesis and leave this one to be read again.
    let hall := mkIdent (← mkFreshUserName `chk_all).eraseMacroScopes
    run (← `(tactic| have $hall:ident := DecOpt.andOptList_ok_true $hId:ident))
    replaceMainGoal [← (← getMainGoal).clear h.fvarId]
    run (← `(tactic| simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      imp_false, not_false_eq_true, implies_true, true_and, and_true] at $hall:ident))
    run (← `(tactic| repeat' (obtain ⟨_, $hall:ident⟩ := $hall:ident)))
    again; return
  -- a negated check: its operand rejected
  if lhs.isAppOfArity ``DecOpt.negOpt 1 then
    let n := mkIdent (← mkFreshUserName `hrej).eraseMacroScopes
    run (← `(tactic| have $n:ident := negOpt_ok_true $hId:ident))
    run (← `(tactic| clear $hId:ident))
    rejected facts unfolds n.getId
    again; return
  -- a decided proposition
  if lhs.isAppOf ``DecOpt.decOpt then
    try
      run (← `(tactic| replace $hId:ident := DecOpt.decOpt_decidable_ok_true $hId:ident))
      again; return
    catch _ =>
      -- an instance: unfold it to what it runs
      run (← `(tactic| simp only [DecOpt.decOpt] at $hId:ident))
      again; return
  -- A search with an enumerator of the checker's own block: by the enumerator's `searchFinds` and a
  -- fact of its soundness at `SGen` (the induction hypothesis, in a block proved together), a
  -- witness of its relation, of which the rest of the run accepted.
  if lhs.isAppOfArity (Name.mkStr2 "Specimen" "searchWorker") 3 then
    let s := lhs.getArg! 1
    if let some wN := s.getAppFn.constName? then
      let findsN := wN ++ `searchFinds
      if (← getEnv).contains findsN then
        let saved ← saveState
        let found ← try
          let fc ← mkConstWithFreshMVarLevels findsN
          let (xs, bis, body) ← forallMetaTelescope (← inferType fc)
          let bargs := body.getAppArgs
          unless bargs.size ≥ 2 do throwError "no"
          unless ← isDefEq bargs[bargs.size - 2]! s do throwError "no"
          for (x, bi) in xs.zip bis do
            if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
              x.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType x)))
          let finds ← instantiateMVars (mkAppN fc xs)
          let g ← instantiateMVars bargs.back!
          let mut spec? : Option Expr := none
          for f in facts do
            let saved' ← saveState
            let (ys, _, c) ← forallMetaTelescope (← instantiateMVars (← inferType f)).consumeMData
            let c := (← instantiateMVars c).consumeMData
            if c.isAppOf (Name.mkStr2 "Obs" "spec") then
              let cargs := c.getAppArgs
              if cargs.size ≥ 2 then
                if ← isDefEq cargs[cargs.size - 2]! g then
                  spec? := some (← instantiateMVars (mkAppN f ys)); break
            saved'.restore
          let some spec := spec? | do
            let mut cands : Array MessageData := #[]
            for f in facts do
              let (_, _, c) ← forallMetaTelescope (← instantiateMVars (← inferType f)).consumeMData
              if c.isAppOf (Name.mkStr2 "Obs" "spec") then
                let cargs := c.getAppArgs
                cands := cands.push m!"{cargs.size}: {cargs[cargs.size - 2]!}"
              else cands := cands.push m!"head {c.getAppFn}"
            throwError "no soundness fact for{indentExpr g}\namong {facts.size} facts:{indentD (MessageData.joinSep cands.toList "\n")}"
          let pf ← mkAppM (Name.mkStr3 "Specimen" "Correctness" "search_accepts") #[finds, spec, fv]
          some <$> pure pf
        catch e =>
          timerLog s!"  check_hyps: searchWorker over {wN}: {(← e.toMessageData.toString).take 4000}"
          saved.restore
          pure none
        if let some pf := found then
          let rel := (← mkFreshUserName `hrel).eraseMacroScopes
          let (_, g') ← (← (← getMainGoal).assert rel (← inferType pf) pf).intro1P
          replaceMainGoal [← g'.clear h.fvarId]
          let w := mkIdent (← mkFreshUserName `wit).eraseMacroScopes
          let hw := mkIdent (← mkFreshUserName `hwit).eraseMacroScopes
          let hk := mkIdent (← mkFreshUserName `hcont).eraseMacroScopes
          run (← `(tactic| obtain ⟨$w:ident, $hw:ident, $hk:ident⟩ := $(mkIdent rel):ident))
          again; return
  -- a call: a fact
  -- A fact is tried only where its hypothesis is about the same head as this run: unifying against
  -- every fact, at every step, unfolds the inputs' terms each time. A search or a checker's instance
  -- is reached through its class, so either side may be the instance's projection.
  let headOf (e : Expr) : Option Name := do
    let (_, l, _) ← e.eq?
    l.getAppFn.constName?
  let lhsHead := lhs.getAppFn.constName?
  let viaInstance := lhs.isAppOf (Name.mkStr3 "Specimen" "CheckerSearch" "search") || lhs.isAppOf ``DecOpt.decOpt
  for f in facts do
    let fHead ← forallTelescope (← inferType f) fun ys _ => do
      let some y := ys.back? | return none
      return headOf (← instantiateMVars (← inferType y))
    unless viaInstance || fHead.isNone || fHead == lhsHead do continue
    let saved ← saveState
    try
      let t ← inferType f
      let (xs, bis, _) ← forallMetaTelescopeReducing t
      let some hyp := xs.back? | throwError "no hyp"
      unless ← timeIn "check_hyps.factUnify" (isDefEq (← inferType hyp) (← inferType fv)) do throwError "no"
      -- the instances (an enumerator's laws for the types it draws) the match left open
      for (x, bi) in xs.zip bis do
        if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
          x.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType x)))
      let pf ← instantiateMVars (mkAppN f (xs.pop.push fv))
      let ty ← inferType pf
      let rel := (← mkFreshUserName `hrel).eraseMacroScopes
      let (_, g) ← (← (← getMainGoal).assert rel ty pf).intro1P
      replaceMainGoal [← g.clear h.fvarId]
      -- A search for a witness: the witness, its relation, and the rest of the checker's run on it.
      if (← whnfR ty).isAppOf ``Exists then
        let w := mkIdent (← mkFreshUserName `wit).eraseMacroScopes
        let hw := mkIdent (← mkFreshUserName `hwit).eraseMacroScopes
        let hk := mkIdent (← mkFreshUserName `hcont).eraseMacroScopes
        run (← `(tactic| obtain ⟨$w:ident, $hw:ident, $hk:ident⟩ := $(mkIdent rel):ident))
      again; return
    catch _ => saved.restore
  -- a run of a worker being proved: its unfolding
  if let some fn := lhs.getAppFn.constName? then
    if let some (_, eqn) := unfolds.find? (·.1 == fn) then
      run (← `(tactic| rw [$(mkIdent eqn):ident] at $hId:ident))
      again; return
  -- a beta-redex, or a `match` on a constructor: reduce it
  let saved ← saveState
  let reduced ← try
      run (← `(tactic| dsimp only at $hId:ident))
      if (← getGoals).length != 1 then pure true else
      withMainContext do
        match (← getLCtx).findFromUserName? h.userName with
        | some d => pure ((← instantiateMVars d.type) != (← instantiateMVars h.type))
        | none => pure true
    catch _ => pure false
  if reduced then again; return
  saved.restore
  -- a `match` on a variable: split it
  let split ← try run (← `(tactic| split at $hId:ident)); pure true catch _ => pure false
  if split then
    let gs ← getGoals
    let mut out := #[]
    for g in gs do setGoals [g]; again; out := out ++ (← getGoals)
    setGoals out.toList; return
  throwError "checkHyps: cannot read {lhs}"

end Specimen.Correctness

namespace Specimen.Correctness
syntax "check_hyps" (" [" term,* "]")? (" unfolding" " [" ident,* "]")? : tactic

open Lean Elab Tactic in
elab_rules : tactic | `(tactic| check_hyps $[[$fs,*]]? $[unfolding [$us,*]]?) => withMainContext do
  let facts ← match fs with
    | some fs => fs.getElems.filterMapM fun f => do
        try return some (← Term.elabTerm f none) catch _ => return none
    | none => pure #[]
  let unfolds ← match us with
    | some us => us.getElems.mapM fun u => do
        let w ← realizeGlobalConstNoOverload u
        let some eqn ← Meta.getUnfoldEqnFor? w (nonRec := true) | throwError "no unfolding equation for {w}"
        return (w, eqn)
    | none => pure #[]
  try checkHyps facts unfolds
  catch e =>
    timerLog s!"  check_hyps FAILED: {(← e.toMessageData.toString).take 600}\n{(toString (← Meta.ppGoal (← getMainGoal))).take 8000}"
    throw e
end Specimen.Correctness

