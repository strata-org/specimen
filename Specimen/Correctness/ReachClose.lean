import Specimen.Correctness.ReachObs
import Specimen.Correctness.LawClasses

/-!
# Closing what the reach walk leaves

The walk of `reachObs` leaves the choices: a disjunction over the branches that survived pruning, and
in a branch, for each call it did not enter, `∃ v, Produces call v ∧ …`, ending in the equation of the
output. `reach_close` makes them, searching with backtracking:

* an equation is solved first, by unification, since it fixes the values the calls must produce;
* a disjunct is tried in turn;
* `Produces call v` from a fact (a hypothesis, or a term given), whose premises are then bounds;
* a size split's draw, `Produces (drawEven (k + 1) f s) parts`, by the canonical split (`canon`), every
  call its equal share and the last the rest;
* the bounds by `omega`, once the choices fix them.
-/

open Lean Meta Elab Tactic

namespace Specimen.Correctness

open Specimen.SizeSplit

/-- The canonical split of `s` among `k + 1` calls: each the equal share, the last the rest. -/
def canon (k s : Nat) : List Nat := List.replicate k (s / (k + 1)) ++ [s - k * (s / (k + 1))]

/-- `ps`, the remainder `r` added to its last part. -/
def fill : List Nat → Nat → List Nat
  | [], _ => []
  | [p], r => [p + r]
  | p :: ps, r => p :: fill ps r

/-- The parts that give each call its floor and its need, whichever is more, and the last what is left. -/
def fillParts (fs ts : List Nat) (s : Nat) : List Nat :=
  fill (List.zipWith max fs ts) (s - (List.zipWith max fs ts).sum)

theorem sum_replicate_nat (k a : Nat) : (List.replicate k a).sum = k * a := by
  induction k with
  | zero => simp
  | succ k ih => simp only [List.replicate_succ, List.sum_cons, ih]; rw [Nat.succ_mul]; omega

theorem produces_drawEven_canon (k f s : Nat) :
    Produces (drawEven (k + 1) f s : SGen (List Nat)) (canon k s) := by
  have hq : s / (k + 1) * (k + 1) ≤ s := Nat.div_mul_le_self s (k + 1)
  have hfl : s / (k + 1) * min f 1000 / 1000 ≤ s / (k + 1) :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm 1000]; exact Nat.mul_le_mul_left _ (Nat.min_le_right _ _))
  refine produces_drawEven (by simp [canon]) (fun x hx => ?_) ?_
  · simp only [canon, List.mem_append, List.mem_replicate, List.mem_singleton] at hx
    rcases hx with ⟨-, rfl⟩ | rfl
    · exact hfl
    · have : k * (s / (k + 1)) + s / (k + 1) ≤ s := by rw [← Nat.succ_mul, Nat.mul_comm]; exact hq
      omega
  · simp only [canon, List.sum_append, sum_replicate_nat, List.sum_cons, List.sum_nil, Nat.add_zero]
    have : k * (s / (k + 1)) ≤ s := Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ k))
      (by rw [Nat.mul_comm]; exact hq)
    omega

theorem sizeAt_canon_lt (k s i : Nat) (h : i < k) : sizeAt (canon k s) i = s / (k + 1) := by
  rw [sizeAt, canon, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [h]),
    List.getElem?_replicate]
  simp [h]

theorem sizeAt_canon_last (k s : Nat) : sizeAt (canon k s) k = s - k * (s / (k + 1)) := by
  rw [sizeAt, canon, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem nat_div_eq_hdiv (a b : Nat) : Nat.div a b = a / b := rfl

/-- The bounds a choice left, once it fixed them. -/
syntax "reach_bound" : tactic
macro_rules
  | `(tactic| reach_bound) => `(tactic| (
      (try simp only [nat_div_eq_hdiv, sizeAt_canon_last, sizeAt_canon_lt, Nat.lt_irrefl, Nat.zero_lt_succ,
        Nat.one_mul, Nat.zero_mul, Nat.sub_zero, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.sum_cons, List.sum_nil, Nat.add_zero, fillParts, fill, Specimen.SizeSplit.sizeAt,
        List.getD_cons_zero, List.getD_cons_succ] at *) <;>
      first
        | omega
        | (have := Nat.div_mul_le_self ‹Nat› 2; omega)))

private partial def headKind (ty : Expr) : MetaM String := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isAppOfArity ``Eq 3 then return "eq"
  if ty.isAppOfArity ``Or 2 then return "or"
  if ty.isAppOfArity ``And 2 then return "and"
  if ty.isAppOfArity ``Exists 2 then return "ex"
  if ty.isAppOfArity ``True 0 || ty.isConstOf ``True then return "true"
  if ty.isAppOf ``Specimen.Correctness.Produces then return "produces"
  if (← matchMatcherApp? ty).isSome && (ty.find? (·.isAppOf ``DecOpt.decOpt)).isSome then return "check"
  return "other"

initialize registerTraceClass `specimen.reach

/-- A bound `t ≤ e` on an expression `e` of a variable `x` that a hypothesis `?M ≤ x` bounds, with
`?M` still to choose: it is left for `?M` to cover, once every choice is made. -/
def boundGroup? (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``LE.le 4 do return none
  let t := ty.getArg! 2
  let e := ty.getArg! 3
  for d in (← getLCtx) do
    let h ← instantiateMVars d.type
    unless h.isAppOfArity ``LE.le 4 && (h.getArg! 2).isMVar && (h.getArg! 3).isFVar do continue
    let x := (h.getArg! 3).fvarId!
    if e.containsFVar x && !t.containsFVar x && !t.hasExprMVar then return some (h.getArg! 2)
  return none

def deferredBound? (g : MVarId) : MetaM Bool := return (← boundGroup? g).isSome

/-- Solve `gs` together, backtracking over the choices; the bounds left for an `?M` are returned. -/
partial def reachSolve (facts : Array Expr) (gs : List MVarId) (deferred : List MVarId)
    (depth : Nat := 0) (waiting : List MVarId := []) : TacticM (Option (List MVarId)) := do
  if depth > 400 then return none
  let gs ← gs.filterM fun g => return !(← g.isAssigned)
  match gs with
  | [] => return some deferred
  | _ =>
  -- An equation waiting for the choices is taken up again only when nothing else is left.
  let active := gs.filter (!waiting.contains ·)
  let active := if active.isEmpty then gs else active
  let waiting := if active.length == gs.length then [] else waiting
  let kinds ← active.mapM fun g => do
    let ty ← instantiateMVars (← g.getType)
    return (g, ← headKind ty, ty.hasExprMVar)
  -- Equations first, since they fix values; then decompositions; then calls; a bound waits until
  -- the choices have fixed it.
  let pick := (kinds.find? (·.2.1 == "eq")) <|> (kinds.find? (·.2.1 == "true")) <|>
    (kinds.find? (·.2.1 == "and")) <|> (kinds.find? (·.2.1 == "ex")) <|>
    (kinds.find? (·.2.1 == "or")) <|> (kinds.find? (·.2.1 == "produces")) <|>
    (kinds.find? fun (_, _, mv) => !mv) <|> kinds.head?
  let some (g, kind, hasMV) := pick | return none
  trace[specimen.reach] "{depth} {kind}: {← instantiateMVars (← g.getType)}"
  let rest := gs.filter (· != g)
  -- A failed choice leaves nothing behind, not even the errors its tactics logged.
  let attempt (k : TacticM (List MVarId)) (defer : List MVarId := deferred) :
      TacticM (Option (List MVarId)) := do
    let s ← saveState
    let msgs := (← getThe Core.State).messages
    try
      let new ← k
      if let some d ← reachSolve facts (new ++ rest) defer (depth + 1) waiting then return some d
      s.restore; modifyThe Core.State ({ · with messages := msgs }); return none
    catch ex =>
      trace[specimen.reach] "failed: {ex.toMessageData}"
      s.restore; modifyThe Core.State ({ · with messages := msgs }); return none
  let firstOf (ks : List (TacticM (List MVarId))) : TacticM (Option (List MVarId)) := do
    for k in ks do
      if let some d ← attempt k then return some d
    return none
  let applyC (c : Name) : TacticM (List MVarId) := do g.apply (← mkConstWithFreshMVarLevels c)
  match kind with
  | "true" => attempt (do g.assign (mkConst ``True.intro); pure [])
  | "eq" =>
    if let some d ← firstOf [
        (do g.refl; pure []),
        (Lean.Elab.Tactic.run g (evalTactic (← `(tactic|
          simp only [Prod.mk.injEq, List.cons.injEq, reduceCtorEq] <;> (try constructor)))))] then
      return some d
    -- An equation the choices have not fixed yet waits for them.
    if hasMV && !waiting.contains g && rest.any (!waiting.contains ·) then
      return ← reachSolve facts (rest ++ [g]) deferred (depth + 1) (g :: waiting)
    return none
  | "and" => attempt (applyC ``And.intro)
  | "ex" => attempt (do
      let gs ← applyC ``Exists.intro
      -- A witness of a product type is a pair of choices, so that a projection of it unifies.
      for w in gs do
        if ← w.isAssigned then continue
        let rec split (w : MVarId) : MetaM Unit := do
          let ty ← whnfR (← w.getType)
          if ty.isAppOfArity ``Prod 2 then
            let a ← mkFreshExprMVar ty.appFn!.appArg!
            let b ← mkFreshExprMVar ty.appArg!
            w.assign (← mkAppM ``Prod.mk #[a, b])
            split a.mvarId!; split b.mvarId!
        if (← whnfR (← w.getType)).isAppOfArity ``Prod 2 then split w
      pure gs)
  | "or" => firstOf [applyC ``Or.inl, applyC ``Or.inr]
  | "produces" =>
    -- Only what is about this generator's combinator is tried: unifying two different generators
    -- unfolds them, and a worker unfolds without end.
    let genHead (ty : Expr) : MetaM (Option Name) := do
      let ty ← whnfR (← instantiateMVars ty)
      unless ty.isAppOf ``Specimen.Correctness.Produces do return none
      return (ty.getArg! (ty.getAppNumArgs - 2)).getAppFn.constName?
    let some head ← genHead (← g.getType) | return none
    let concl (e : Expr) : MetaM (Option Name) := do
      forallTelescope (← instantiateMVars (← inferType e)) fun _ b => genHead b
    let lctx ← getLCtx
    let mut cands : Array (TacticM (List MVarId)) := #[]
    if head == ``Specimen.SizeSplit.drawEven then cands := cands.push (applyC ``produces_drawEven_canon)
    -- A split with floors: each call its floor or its need, the needs left to the calls' bounds.
    if head == ``Specimen.SizeSplit.draw then
      cands := cands.push (do
        let ty ← whnfR (← instantiateMVars (← g.getType))
        let gen := ty.getArg! (ty.getAppNumArgs - 2)
        let fs := gen.getAppArgs[gen.getAppNumArgs - 2]!
        let s := gen.getAppArgs.back!
        let some fsl := fs.listLit? | throwError "the floors are not a list"
        let ts ← fsl.2.mapM fun _ => mkFreshExprMVar (mkConst ``Nat)
        let tsE ← mkListLit (mkConst ``Nat) ts
        let lem := mkAppN (← mkConstWithFreshMVarLevels `Specimen.Correctness.produces_draw_fill) #[fs, tsE, s]
        let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType lem) (some 3)
        -- The lists' shapes are given, not unified: unifying their lengths would match them entry by
        -- entry, fixing every need to its floor.
        let k := fsl.2.length
        mvs[0]!.mvarId!.assign (← mkAppOptM ``List.cons_ne_nil #[none, fsl.2[0]!, ← mkListLit fsl.1 fsl.2.tail])
        mvs[1]!.mvarId!.assign (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit k))
        let pf := mkAppN lem mvs
        unless ← isDefEq (← inferType pf) (← g.getType) do
          throwError "draw: {← inferType pf} vs {← g.getType}"
        g.assign pf
        return [mvs[2]!.mvarId!])
    if head == ``BacktrackGenFor.gen then
      cands := cands ++ #[applyC ``reach_gen_eqRight, applyC ``reach_gen_eqLeft,
        applyC ``BacktrackGenForComplete.produces]
    if head == ``Basalt.ArbitrarySized.arbitrarySized then
      cands := cands.push (applyC ``ArbitrarySizedComplete.produces)
    for h in facts do
      if (← concl h) == some head then cands := cands.push (g.apply h)
    for d in lctx do
      if d.isImplementationDetail then continue
      if (← concl d.toExpr) == some head then cands := cands.push (g.apply d.toExpr)
    trace[specimen.reach] "head {head}, {cands.size} candidates"
    firstOf cands.toList
  | "check" =>
    -- A premise checked on the way: its verdict, from the premise or its negation in context, by the
    -- check's `DecOptComplete` or `DecOptRefuteComplete` instance, which the `match` then reduces on.
    -- What it checks must be fixed first.
    if hasMV then
      if !waiting.contains g && rest.any (!waiting.contains ·) then
        return ← reachSolve facts (rest ++ [g]) deferred (depth + 1) (g :: waiting)
      return none
    let ty ← instantiateMVars (← g.getType)
    let some e := ty.find? (·.isAppOf ``DecOpt.decOpt) | return none
    let P := e.getArg! 0
    let lctx ← getLCtx
    let mut cands : Array (TacticM (List MVarId)) := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      for (lem, prop) in [(``DecOptComplete.ok, P), (``DecOptRefuteComplete.ok, mkNot P)] do
        cands := cands.push (do
          unless ← isDefEq d.type prop do throwError "no"
          let f ← mkAppOptM lem #[P, e.getArg! 1, none, d.toExpr, e.getArg! 2]
          let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType f) (some 1)
          let hs := mvs[0]!
          let eq := mkApp f hs
          let r ← g.rewrite ty eq
          let g' ← g.replaceTargetEq r.eNew r.eqProof
          let gs ← Lean.Elab.Tactic.run g' (evalTactic (← `(tactic| simp only [DecOpt.negOpt, Bool.not_true,
            Bool.not_false])))
          return gs ++ [hs.mvarId!] ++ r.mvarIds)
    firstOf cands.toList
  | _ =>
    -- A call's bound on its part of a floored split: the part is at least the call's need, which
    -- this fixes.
    if (← instantiateMVars (← g.getType)).find? (·.isAppOf `Specimen.Correctness.fillParts) |>.isSome then
      if let some d ← attempt (do
          let ty ← instantiateMVars (← g.getType)
          let rhs := ty.getArg! 3
          let i := rhs.getAppArgs.back!
          let some fp := rhs.find? (·.isAppOf `Specimen.Correctness.fillParts) | throwError "no"
          let lem := mkAppN (← mkConstWithFreshMVarLevels `Specimen.Correctness.le_sizeAt_fillParts)
            #[fp.getArg! 0, fp.getArg! 1, fp.getArg! 2, i]
          let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType lem) (some 1)
          let some fsl := (fp.getArg! 0).listLit? | throwError "the floors are not a list"
          mvs[0]!.mvarId!.assign (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit fsl.2.length))
          let pf := mkAppN lem mvs
          let pty ← whnfR (← inferType pf)
          -- `ts.getD i 0` fixes the need to the bound
          unless ← isDefEq (← whnf (pty.getArg! 2)) (ty.getArg! 2) do
            throwError "fill lhs: {← whnf (pty.getArg! 2)} vs {ty.getArg! 2}"
          unless ← isDefEq (pty.getArg! 3) rhs do throwError "fill rhs: {pty.getArg! 3} vs {rhs}"
          g.assign pf
          return []) then return some d
      -- Any other fact about a part (it is below the fuel, say) holds once the size bound is chosen.
      if !hasMV then return ← attempt (pure []) (g :: deferred)
    if ← deferredBound? g then
      return ← attempt (pure []) (g :: deferred)

    if hasMV then
      -- A premise a call needs, from a hypothesis, which fixes what it is about.
      let lctx ← getLCtx
      if let some d ← firstOf (lctx.foldl (fun acc d => if d.isImplementationDetail then acc else
        acc.push (do
          unless ← isDefEq (← g.getType) d.type do throwError "no"
          g.assign d.toExpr
          pure ([] : List MVarId) : TacticM (List MVarId))) #[]).toList then
        return some d
      -- Or it waits for the other choices to fix it.
      if !waiting.contains g && rest.any (!waiting.contains ·) then
        return ← reachSolve facts (rest ++ [g]) deferred (depth + 1) (g :: waiting)
      return none
    attempt (do
      let r ← Lean.Elab.Tactic.run g (evalTactic (← `(tactic|
        first | reach_bound | assumption | rfl | trivial | simp)))
      unless r.isEmpty do throwError "open"
      pure [])

/-- The largest number of parts a bound's expression divides its variable into. -/
partial def divisor (e : Expr) : Nat :=
  let here : Nat :=
    if e.isAppOfArity ``HDiv.hDiv 6 || e.isAppOfArity ``Nat.div 2 then
      (e.getAppArgs.back!.nat?).getD 1
    else if e.isAppOfArity ``Specimen.Correctness.canon 2 then
      ((e.getArg! 0).nat?.getD 0) + 1
    else 1
  e.getAppArgs.foldl (fun m a => max m (divisor a)) here

/-- Choose each `?M` that bounds a variable: the bounds left on it, summed, times the most parts any of
them divides the variable into; then close them. -/
def closeDeferred (ds : List MVarId) : TacticM Unit := do
  let mut groups : Array (Expr × List MVarId) := #[]
  for g in ds do
    if ← g.isAssigned then continue
    let some M ← boundGroup? g | continue
    match groups.findIdx? (·.1 == M) with
    | some i => groups := groups.modify i fun (m, gs) => (m, g :: gs)
    | none => groups := groups.push (M, [g])
  for (M, gs) in groups do
    if ← M.mvarId!.isAssigned then continue
    let mut sum : Expr := mkNatLit 0
    let mut d := 1
    for g in gs do
      let ty ← whnfR (← instantiateMVars (← g.getType))
      sum ← mkAppM ``HAdd.hAdd #[sum, ty.getArg! 2]
      d := max d (divisor (← instantiateMVars (ty.getArg! 3)))
    -- `?M` is the case's own goal (synthetic opaque), so it is assigned rather than unified.
    M.mvarId!.assign (← mkAppM ``HMul.hMul #[mkNatLit d, sum])
  for g in ds do
    if ← g.isAssigned then continue
    let r ← Lean.Elab.Tactic.run g (evalTactic (← `(tactic| reach_bound)))
    unless r.isEmpty do throwError "reach_close: a bound does not close{indentExpr (← g.getType)}"

/-- Make the choices the reach walk left (see the module docstring), with facts `t, …`. -/
syntax "reach_close" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| reach_close $[[$ts,*]]?) => withMainContext do
    let facts ← (ts.map (·.getElems) |>.getD #[]).mapM fun t => elabTerm t none
    -- The guards the walk could not evaluate, and the options of the guarded pools.
    let _ ← observing? (evalTactic (← `(tactic| simp only [ite_true, ite_false, ↓reduceIte,
      Option.some.injEq, exists_eq_left', exists_eq_left, true_and, and_true, reduceCtorEq, false_and,
      and_false, false_or, or_false, exists_false])))
    if (← getUnsolvedGoals).isEmpty then return
    let g ← getMainGoal
    let some ds ← reachSolve facts [g] [] | throwError "reach_close: no choice closes{indentExpr (← g.getType)}"
    closeDeferred ds
    replaceMainGoal []

/-! ## Basalt's unconstrained generators -/

theorem produces_chooseNat {lo hi k : Nat} (h : lo ≤ hi) (h1 : lo ≤ k) (h2 : k ≤ hi) :
    Produces (chooseNat lo hi h : SGen Nat) k := produces_of_reach (by
  show reachObs.spec (chooseNat lo hi h : SGen Nat) _
  walk
  exact ⟨h1, h2⟩)

instance : ArbitrarySizedComplete Nat where
  complete x := ⟨x, fun _ hs => produces_chooseNat _ (Nat.zero_le _) hs⟩

theorem produces_vectorOf {α : Type} {g : SGen α} : ∀ (l : List α), (∀ x ∈ l, Produces g x) →
    Produces (vectorOf l.length g) l
  | [], _ => produces_pure_iff.mpr rfl
  | x :: l, h => by
    rw [List.length_cons, vectorOf_succ]
    exact produces_bind_of (h x List.mem_cons_self) (produces_bind_of
      (produces_vectorOf l fun y hy => h y (List.mem_cons_of_mem _ hy)) (produces_pure_iff.mpr rfl))

theorem le_sum_of_mem {f : α → Nat} : ∀ {l : List α} {x : α}, x ∈ l → f x ≤ (l.map f).sum
  | _ :: _, _, .head _ => by simp
  | _ :: l, _, .tail _ h => by simp only [List.map_cons, List.sum_cons]; have := le_sum_of_mem (f := f) h; omega

/-- A list is drawn when its length and each of its elements are. -/
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedComplete α] : ArbitrarySizedComplete (List α) where
  complete xs := ⟨xs.length + (xs.map ArbitrarySizedComplete.bound).sum, fun s hs => by
    show Produces (do
      let k ← chooseNat 0 s
      vectorOf k (Basalt.ArbitrarySized.arbitrarySized s) : SGen (List α)) xs
    refine produces_bind_of (produces_chooseNat (k := xs.length) _ (Nat.zero_le _) (by omega)) ?_
    exact produces_vectorOf xs fun x hx => ArbitrarySizedComplete.produces
      (Nat.le_trans (le_sum_of_mem hx) (by omega))⟩

end Specimen.Correctness
