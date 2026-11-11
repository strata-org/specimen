import Specimen.Correctness.ReachObs
import Specimen.WorkerRegistry
import Specimen.Correctness.LawClasses
import Specimen.Debug
import Specimen.Correctness.SoundOf
import Specimen.Correctness.CheckComplete

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
  -- a check's verdict, `… decOpt P n … = .ok b`: decided like a `match` on it
  if ty.isAppOfArity ``Eq 3 && ((ty.getArg! 1).isAppOf ``DecOpt.decOpt || (ty.getArg! 1).isAppOf ``DecOpt.negOpt) then
    return "check"
  -- a checker's acceptance, `W … = .ok true` of a checker worker or a search for a witness: from a
  -- hypothesis, a fact, or the search's law, never by unfolding (`refl` would run the checker)
  if ty.isAppOfArity ``Eq 3 && (ty.getArg! 2).isAppOf ``Except.ok then
    if let some h := (ty.getArg! 1).getAppFn.constName? then
      if h == ``Specimen.CheckerSearch.search || h == ``Specimen.searchWorker ||
          (h == ``Specimen.CheckerSearchAll.search && specimen.reachExtended.get (← getOptions)) ||
          Specimen.isDerivedWorker (← getEnv) h [.Checker] then
        return "accept"
  if ty.isAppOfArity ``Eq 3 then return "eq"
  if ty.isAppOfArity ``Or 2 then return "or"
  if ty.isAppOfArity ``And 2 then return "and"
  if ty.isAppOfArity ``Exists 2 then return "ex"
  if ty.isAppOfArity ``True 0 || ty.isConstOf ``True then return "true"
  if ty.isAppOf ``Specimen.Correctness.Produces then return "produces"
  -- a `match` on a check's verdict; one on anything else (a projection the choices fixed) is reduced
  -- as an "other" goal. A check under an alternative mentions the alternative's bound variables.
  if let some m ← matchMatcherApp? ty then
    -- a check's verdict, or a checker of the block's (its verdict from the induction hypothesis)
    let env ← getEnv
    let isCheckerCall (x : Expr) : Bool := match x.getAppFn.constName? with
      | some c => Specimen.isDerivedWorker env c [.Checker]
      | none => false
    if m.discrs.any (fun d => (d.find? fun x => x.isAppOf ``DecOpt.decOpt || isCheckerCall x).isSome) then
      return "check"
  return "other"

initialize registerTraceClass `specimen.reach

/-- The bound still to choose in `a`: `?M`, or `?M` applied to the values a case split of the walk put
in its place (`?M (.enum eids)`), chosen then as a constant function of them. -/
def openTail? (a : Expr) : MetaM (Option Expr) := do
  let a ← instantiateMVars a
  let f := a.getAppFn
  unless f.isMVar do return none
  -- A copy a case split of the walk made (`?M' xs`, delayed-assigned `?M`): the bound is `?M`'s.
  let mut m := f.mvarId!
  repeat
    match ← getDelayedMVarAssignment? m with
    | some d => m := d.mvarIdPending
    | none => break
  if ← m.isAssigned then return none
  return some (mkMVar m)

/-- A bound `t ≤ e` on an expression `e` of a variable `x` that a hypothesis `?M ≤ x` bounds, with
`?M` still to choose: it is left for `?M` to cover, once every choice is made. -/
def boundGroup? (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``LE.le 4 do return none
  let t := ty.getArg! 2
  let e := ty.getArg! 3
  for d in (← getLCtx) do
    let h ← instantiateMVars d.type
    unless h.isAppOfArity ``LE.le 4 && (h.getArg! 3).isFVar do continue
    -- The bound still open: `?M`, or the remainder `?R` an earlier branch of the case left in
    -- `… + ?R`.
    let some M ← openTail? (h.getArg! 2) | continue
    let x := (h.getArg! 3).fvarId!
    if e.containsFVar x && !t.containsFVar x && !t.hasExprMVar then return some M
  return none

def deferredBound? (g : MVarId) : MetaM Bool := return (← boundGroup? g).isSome

/-- Two terms that differ in a constructor or a literal at a position where both have one: never
equal, whatever their variables, bound or still to be chosen, stand for. -/
partial def ctorClash (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  match a, b with
  | .lit l₁, .lit l₂ => return l₁ != l₂
  | _, _ =>
    let env ← getEnv
    let some f := a.getAppFn.constName? | return false
    let some g := b.getAppFn.constName? | return false
    let some (.ctorInfo c₁) := env.find? f | return false
    let some (.ctorInfo c₂) := env.find? g | return false
    if f != g then return true
    let as := a.getAppArgs; let bs := b.getAppArgs
    unless as.size == bs.size do return false
    for i in [c₁.numParams:as.size] do
      if ← ctorClash as[i]! bs[i]! then return true
    let _ := c₂
    return false

/-- A goal no choice can close, seen syntactically: `False`, an equation of clashing closed terms, a
conjunction with such a part, a disjunction of such goals, or an `∃` or `match` all of whose bodies are
such goals. -/
partial def surelyFalse (e : Expr) : MetaM Bool := do
  let e := e.headBeta
  if e.isConstOf ``False then return true
  if let some (_, a, b) := e.eq? then return ← ctorClash a b
  if e.isAppOfArity ``And 2 then return (← surelyFalse (e.getArg! 0)) || (← surelyFalse (e.getArg! 1))
  if e.isAppOfArity ``Or 2 then return (← surelyFalse (e.getArg! 0)) && (← surelyFalse (e.getArg! 1))
  if e.isAppOfArity ``Exists 2 then
    match e.getArg! 1 with
    | .lam _ _ b _ => return ← surelyFalse b
    | _ => return false
  if let some m ← matchMatcherApp? e then
    let mut all := true
    for alt in m.alts do
      let rec body : Expr → Expr | .lam _ _ b _ => body b | b => b
      unless ← surelyFalse (body alt) do all := false; break
    return all
  return false

/-- Whether the search keeps its statistics (`SPECIMEN_REACH_STATS`): shared counters, which
parallel proofs would contend on. -/
initialize reachStatsOn : Bool ← return (← IO.getEnv "SPECIMEN_REACH_STATS").isSome

/-- A contradiction among `g`'s hypotheses, seen syntactically and in one pass: `False`, an equation
of clashing constructors, or `P` beside `¬ P`. `contradiction` compares every pair up to definitional
unfolding, seconds over large hypotheses, and in a branch the search reaches almost never finds one. -/
def syntacticContra (g : MVarId) : MetaM Bool := g.withContext do
  let mut seen : Std.HashMap Expr FVarId := {}
  let mut negs : Array (Expr × FVarId) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    if ty.isConstOf ``False then
      g.assign (← mkFalseElim (← g.getType) d.toExpr); return true
    if let some (_, a, b) := ty.eq? then
      if ← ctorClash a b then
        let s ← saveState
        try
          if (← g.cases d.fvarId).isEmpty then return true
        catch _ => pure ()
        s.restore
    if ty.isAppOfArity ``Not 1 then negs := negs.push (ty.appArg!, d.fvarId)
    else seen := seen.insert ty d.fvarId
  for (p, hn) in negs do
    if let some hp := seen[p]? then
      g.assign (← mkAbsurd (← g.getType) (mkFVar hp) (mkFVar hn)); return true
  return false

/-- `x`, or `false` with the state restored if it fails or runs out of its heartbeats (a runtime
exception, which `try` lets through). -/
def safeClose (x : TacticM Bool) : TacticM Bool := do
  let s ← saveState
  let msgs := (← getThe Core.State).messages
  tryCatchRuntimeEx x fun _ => do
    s.restore; modifyThe Core.State ({ · with messages := msgs }); pure false

/-- The goals with no metavariable that the search running on each thread found it cannot close:
such a goal's proof depends on no other choice, so a failure stands for the whole search. Cleared at
the start of each `reach_close`. -/
initialize closedFailures : IO.Ref (Std.HashMap UInt64 (Std.HashSet Expr)) ← IO.mkRef {}


/-- Attempts by the kind of goal they choose for (diagnostics, `SPECIMEN_REACH_STATS`). -/
initialize kindCountsByTid : IO.Ref (Std.HashMap UInt64 (Std.HashMap String Nat)) ← IO.mkRef {}

/-- Add `v` to counter `k` of this thread. -/
def bump (k : String) (v : Nat) : IO Unit := do
  let tid ← IO.getTID
  kindCountsByTid.modify fun m =>
    let c := m.getD tid {}
    m.insert tid (c.insert k (c.getD k 0 + v))

/-- `x`, its time added to counter `lbl` (with `SPECIMEN_REACH_STATS`), failing or not. -/
def timedT {α} (lbl : String) (x : TacticM α) : TacticM α := do
  unless reachStatsOn do return ← x
  let t0 ← IO.monoNanosNow
  try x finally bump lbl (((← IO.monoNanosNow) - t0) / 1000)

/-- This thread's counters. -/
def myCounts : IO (Std.HashMap String Nat) := do return (← kindCountsByTid.get).getD (← IO.getTID) {}

initialize childAcc : IO.Ref Nat ← IO.mkRef 0
initialize kindAt : IO.Ref (Std.HashMap Nat String) ← IO.mkRef {}

/-- A comparison of natural numbers, or its negation: what a bound's arithmetic can use. -/
partial def isNatArith (t : Expr) : Bool :=
  if t.isAppOfArity ``Not 1 then isNatArith t.appArg! else
  let isNat (e : Expr) := e.isConstOf ``Nat
  (t.isAppOfArity ``LE.le 4 && isNat (t.getArg! 0)) || (t.isAppOfArity ``LT.lt 4 && isNat (t.getArg! 0)) ||
  (t.isAppOfArity ``GE.ge 4 && isNat (t.getArg! 0)) || (t.isAppOfArity ``GT.gt 4 && isNat (t.getArg! 0)) ||
  (t.isAppOfArity ``Eq 3 && isNat (t.getArg! 0)) || (t.isAppOfArity ``Ne 3 && isNat (t.getArg! 0)) ||
  t.isAppOfArity ``Nat.le 2 || t.isAppOfArity ``Nat.lt 2

/-- A proof of `t ≤ S`, `t` a summand of the sum `S` (as `+` builds it, any nesting), found by
position: `none` when `t` is not one. -/
partial def leOfSummand? (t S : Expr) : MetaM (Option Expr) := do
  if S == t then return some (← mkAppM ``Nat.le_refl #[t])
  unless S.isAppOfArity ``HAdd.hAdd 6 do return none
  let A := S.getArg! 4
  let B := S.getArg! 5
  if let some p ← leOfSummand? t B then
    -- `t ≤ B ≤ A + B`
    return some (← mkAppM ``Nat.le_trans #[p, ← mkAppM ``Nat.le_add_left #[B, A]])
  if let some p ← leOfSummand? t A then
    return some (← mkAppM ``Nat.le_trans #[p, ← mkAppM ``Nat.le_add_right #[A, B]])
  return none

/-- Close a bound `t ≤ x` from a hypothesis `d * S ≤ x` (or `S ≤ x`) with `t` a summand of `S`,
by a proof built from the summand's position: the common case, which `simp` and `omega` take a
long time over when the sum is long and its terms are large. -/
def fastBound (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LE.le 4 && (ty.getArg! 0).isConstOf ``Nat do return false
  let t := ty.getArg! 2
  let x := ty.getArg! 3
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let h ← instantiateMVars d.type
    unless h.isAppOfArity ``LE.le 4 && (h.getArg! 0).isConstOf ``Nat && h.getArg! 3 == x do continue
    let l := h.getArg! 2
    -- `d * S`, `d` a positive literal, or `S`
    let (S, mulPf?) ← do
      if l.isAppOfArity ``HMul.hMul 6 then
        let k := l.getArg! 4
        match k.nat? with
        | some (n + 1) =>
          -- `S ≤ k * S`
          let S := l.getArg! 5
          let pos ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, k])
          pure (S, some (← mkAppM ``Nat.le_mul_of_pos_left #[S, pos]))
        | _ => pure (l, none)
      else pure (l, none)
    let some p ← leOfSummand? t S | continue
    let p ← match mulPf? with
      | some m => mkAppM ``Nat.le_trans #[p, m]
      | none => pure p
    let pf ← mkAppM ``Nat.le_trans #[p, d.toExpr]
    unless ← isDefEq (← inferType pf) ty do continue
    g.assign pf
    return true
  return false

mutual
/-- Solve `gs` together, backtracking over the choices; the bounds left for an `?M` are returned. -/
partial def reachSolve (ctr : IO.Ref Nat) (headCache : IO.Ref (Std.HashMap Expr (Option Name)))
    (facts : Array Expr) (gs : List MVarId) (deferred : List MVarId)
    (depth : Nat := 0) (waiting : List MVarId := []) : TacticM (Option (List MVarId)) := do
  unless reachStatsOn do return ← reachSolveCore ctr headCache facts gs deferred depth waiting
  let t0 ← IO.monoNanosNow
  let saved ← (childAcc.get : IO Nat)
  (childAcc.set 0 : IO Unit)
  try reachSolveCore ctr headCache facts gs deferred depth waiting
  finally
    let incl := (← IO.monoNanosNow) - t0
    let ch ← (childAcc.get : IO Nat)
    let k := (← (kindAt.get : IO _))[depth]?.getD "?"
    (if reachStatsOn then bump ("x_" ++ k) ((incl - min ch incl) / 1000) else pure () : IO Unit)
    (childAcc.set (saved + incl) : IO Unit)

partial def reachSolveCore (ctr : IO.Ref Nat) (headCache : IO.Ref (Std.HashMap Expr (Option Name)))
    (facts : Array Expr) (gs : List MVarId) (deferred : List MVarId)
    (depth : Nat := 0) (waiting : List MVarId := []) : TacticM (Option (List MVarId)) := do
  (if reachStatsOn then kindAt.modify (·.insert depth "pre") else pure () : IO Unit)
  if depth > 400 then return none
  let tp ← IO.monoNanosNow
  let gs ← gs.filterM fun g => return !(← g.isAssigned)
  match gs with
  | [] => return some deferred
  | _ =>
  -- An equation waiting for the choices is taken up again only when nothing else is left.
  let active := gs.filter (!waiting.contains ·)
  let active := if active.isEmpty then gs else active
  -- A value still to choose (a witness, not a proposition) is fixed by the choices that mention it, so
  -- it is taken up only when nothing else is left.
  let props ← active.filterM fun g => do isProp (← instantiateMVars (← g.getType))
  let active := if props.isEmpty then active else props
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
  let tp' ← IO.monoNanosNow
  (if reachStatsOn then bump "prelude_us" ((tp' - tp) / 1000) else pure () : IO Unit)
  let some (g, kind, hasMV) := pick | return none
  -- A goal with no metavariable, among others, is closed on its own and committed to: no other
  -- choice changes it, so neither a failure of the others nor a second try can need another proof
  -- of it, and one it cannot have is a failure of the branch.
  if !hasMV && gs.length > 1 && kind != "other" then
    let gTy ← instantiateMVars (← g.getType)
    let tid ← IO.getTID
    if ((← closedFailures.get).getD tid {}).contains gTy then return none
    match ← reachSolveCore ctr headCache facts [g] deferred (depth + 1) [] with
    | none =>
      closedFailures.modify fun m => m.insert tid ((m.getD tid {}).insert gTy)
      return none
    | some d => return ← reachSolveCore ctr headCache facts (gs.filter (· != g)) d (depth + 1) waiting
  (if reachStatsOn then kindAt.modify (·.insert depth kind) else pure () : IO Unit)
  -- A goal left that no choice can close fails the branch at once.
  let tf ← IO.monoNanosNow
  let sf ← active.anyM fun g => do surelyFalse (← instantiateMVars (← g.getType))
  let tf' ← IO.monoNanosNow
  (if reachStatsOn then bump "surelyFalse_us" ((tf' - tf) / 1000) else pure () : IO Unit)
  if sf then return none
  let tt ← IO.monoNanosNow
  trace[specimen.reach] "{depth} {kind}: {← instantiateMVars (← g.getType)}"
  let tt' ← IO.monoNanosNow
  (if reachStatsOn then bump "trace_us" ((tt' - tt) / 1000) else pure () : IO Unit)
  let rest := gs.filter (· != g)
  -- A failed choice leaves nothing behind, not even the errors its tactics logged.
  let attempt (k : TacticM (List MVarId)) (defer : List MVarId := deferred) :
      TacticM (Option (List MVarId)) := do
    let ts ← IO.monoNanosNow
    let s ← saveState
    let msgs := (← getThe Core.State).messages
    let ts' ← IO.monoNanosNow
    (if reachStatsOn then bump "save_us" ((ts' - ts) / 1000) else pure () : IO Unit)
    (ctr.modify (· + 1) : IO Unit)
    (if reachStatsOn then bump kind (1) else pure () : IO Unit)
    -- a choice that runs out of its heartbeats (a budgeted `simp_all`, say) fails like any other:
    -- `try` would let the runtime exception through and fail the whole case
    tryCatchRuntimeEx (do
      let t0 ← IO.monoNanosNow
      let new ← k
      let dt ← IO.monoNanosNow
      (if reachStatsOn then bump (kind ++ "_us") ((dt - t0) / 1000) else pure () : IO Unit)
      if let some d ← reachSolve ctr headCache facts (new ++ rest) defer (depth + 1) waiting then return some d
      let tr ← IO.monoNanosNow
      s.restore; modifyThe Core.State ({ · with messages := msgs })
      let tr' ← IO.monoNanosNow
      (if reachStatsOn then bump "restore_us" ((tr' - tr) / 1000) else pure () : IO Unit)
      return none) fun ex => do
      trace[specimen.reach] "failed: {ex.toMessageData}"
      s.restore; modifyThe Core.State ({ · with messages := msgs }); return none
  let firstOf (ks : List (TacticM (List MVarId))) : TacticM (Option (List MVarId)) := do
    for k in ks do
      if let some d ← attempt k then return some d
    return none
  let timed (lbl : String) (k : TacticM (List MVarId)) : TacticM (List MVarId) := do
    let t0 ← IO.monoNanosNow
    try k finally
      let dt ← IO.monoNanosNow
      (if reachStatsOn then bump ("c_" ++ lbl) ((dt - t0) / 1000) else pure () : IO Unit)
  let applyC (c : Name) : TacticM (List MVarId) := timed c.toString do g.apply (← mkConstWithFreshMVarLevels c)
  match kind with
  | "true" => attempt (do g.assign (mkConst ``True.intro); pure [])
  | "eq" =>
    -- Witnesses still to fix (a value drawn and not returned, which the case only needs to exist): a
    -- premise of the case that unifies with it fixes them, tried before `rfl`, which would equate
    -- the witnesses and leave both unchosen (`specimen.reachExtended`).
    if hasMV && specimen.reachExtended.get (← getOptions) then
      let mut hyps : List (TacticM (List MVarId)) := []
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        unless (← instantiateMVars d.type).isAppOfArity ``Eq 3 do continue
        hyps := hyps ++ [do
          unless ← withDefault (isDefEq (← g.getType) d.type) do throwError "no"
          g.assign d.toExpr
          pure []]
      if let some d ← firstOf hyps then return some d
      -- Or no premise is about them (it was substituted away): a value of the witnesses' type the
      -- case has, then `rfl`; any value will do, since nothing else is told of them.
      let ms := ((← instantiateMVars (← g.getType)).collectMVars {}).result
      let mut picks : List (TacticM (List MVarId)) := []
      for m in ms do
        if ← m.isAssigned then continue
        let mTy ← instantiateMVars (← m.getType)
        if (← isProp mTy) || mTy.isSort then continue
        -- a pair: its components, each then chosen alike, as an `∃`'s witness of a product is
        if (← whnfR mTy).isAppOfArity ``Prod 2 then
          picks := picks ++ [do
            let pTy ← whnfR mTy
            let a ← mkFreshExprMVar pTy.appFn!.appArg!
            let b ← mkFreshExprMVar pTy.appArg!
            m.assign (← mkAppM ``Prod.mk #[a, b])
            pure [g]]
          continue
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          picks := picks ++ [do
            unless ← withDefault (isDefEq (← instantiateMVars d.type) mTy) do throwError "no"
            unless ← isDefEq (mkMVar m) d.toExpr do throwError "no"
            g.refl
            pure []]
      if let some d ← firstOf picks then return some d
    if let some d ← firstOf [
        (do g.refl; pure []),
        (Lean.Elab.Tactic.run g (evalTactic (← `(tactic|
          simp only [Prod.mk.injEq, List.cons.injEq, reduceCtorEq] <;> (try constructor)))))] then
      return some d
    -- An equation the choices have not fixed yet waits for them.
    if hasMV && !waiting.contains g && rest.any (!waiting.contains ·) then
      return ← reachSolve ctr headCache facts (rest ++ [g]) deferred (depth + 1) (g :: waiting)
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
    if head == ``EnumFor.enum then
      let ty ← whnfR (← instantiateMVars (← g.getType))
      let gen := ty.getArg! (ty.getAppNumArgs - 2)
      match (gen.getAppArgs[1]? : Option Expr) with
      | some (Expr.lam _ _ b _) =>
        match b.eq? with
        | some (_, Expr.bvar 0, r) => unless r.hasLooseBVars do cands := cands.push (applyC ``reach_enum_eqRight)
        | some (_, l, Expr.bvar 0) => unless l.hasLooseBVars do cands := cands.push (applyC ``reach_enum_eqLeft)
        | _ => pure ()
      | _ => pure ()
    if head == ``BacktrackGenFor.gen then
      let dbg := (← (IO.getEnv "SPECIMEN_REACH_DEBUG" : IO _)).isSome
      -- an equation's producer, only for a predicate that is one: unifying another predicate with
      -- `fun x => x = v` unfolds its generator
      let ty ← whnfR (← instantiateMVars (← g.getType))
      let gen := ty.getArg! (ty.getAppNumArgs - 2)
      let eqSide : Option Bool := match (gen.getAppArgs[1]? : Option Expr) with
        | some (Expr.lam _ _ b _) =>
          match b.eq? with
          | some (_, Expr.bvar 0, r) => if r.hasLooseBVars then none else some true
          | some (_, l, Expr.bvar 0) => if l.hasLooseBVars then none else some false
          | _ => none
        | _ => none
      if eqSide == some true then cands := cands.push (applyC ``reach_gen_eqRight)
      if eqSide == some false then cands := cands.push (applyC ``reach_gen_eqLeft)
      cands := cands ++ #[
        (do
          try applyC ``BacktrackGenForComplete.produces
          catch ex =>
            if dbg then
              timerLog s!"  GENCOMPLETE-FAIL {(← ex.toMessageData.toString).take 1500}"
            throw ex)]
    if head == ``Basalt.ArbitrarySized.arbitrarySized then
      cands := cands.push (applyC ``ArbitrarySizedComplete.produces)
    -- another enumerator's, at its instance (`specimen.completeAllSorts`)
    if head == ``EnumFor.enum then
      cands := cands.push (applyC ``EnumForComplete.produces)
    -- the facts' and hypotheses' conclusions, computed once for the whole search
    for h in facts do
      let c ← match (← headCache.get)[h]? with
        | some c => pure c
        | none => do
          let c ← concl h
          unless (← instantiateMVars (← inferType h)).hasMVar do headCache.modify (·.insert h c)
          pure c
      -- unifying two runs of the same worker at different arguments unfolds them; reducibly, it
      -- only compares the arguments
      if c == some head then cands := cands.push (timed "fact" (withReducible (g.apply h)))
    for d in lctx do
      if d.isImplementationDetail then continue
      let c ← match (← headCache.get)[d.toExpr]? with
        | some c => pure c
        | none => do
          let c ← concl d.toExpr
          unless (← instantiateMVars d.type).hasMVar do headCache.modify (·.insert d.toExpr c)
          pure c
      if c == some head then cands := cands.push (timed "hyp" (withReducible (g.apply d.toExpr)))
    trace[specimen.reach] "head {head}, {cands.size} candidates"
    firstOf cands.toList
  | "accept" =>
    let accHead (ty : Expr) : MetaM (Option Name) := do
      let ty ← whnfR (← instantiateMVars ty)
      unless ty.isAppOfArity ``Eq 3 do return none
      return (ty.getArg! 1).getAppFn.constName?
    let some head ← accHead (← g.getType) | return none
    let mut cands : Array (TacticM (List MVarId)) := #[]
    if head == ``Specimen.CheckerSearch.search then
      cands := cands.push (applyC ``CheckerSearchComplete.ok)
    -- a search over the unconstrained values of a type: a value, chosen by the rest of the check
    -- (its conjuncts taken apart, as a checker's case takes its own)
    if head == ``Specimen.CheckerSearchAll.search && specimen.reachExtended.get (← getOptions) then
      cands := cands.push (do
        let gs ← applyC ``checkerSearchAll_ok
        gs.flatMapM fun g' => do
          let ty ← instantiateMVars (← g'.getType)
          unless (ty.find? (·.isAppOf ``DecOpt.andOptList)).isSome do return [g']
          Lean.Elab.Tactic.run g' (evalTactic (← `(tactic| simp only [
            Specimen.Correctness.andOptList_ok_true, List.mem_cons, List.mem_nil_iff, or_false,
            forall_eq_or_imp, forall_eq, and_true, imp_false, not_false_eq_true]))))
    -- a search with an enumerator of the block: by its `searchHits`/`searchTotal`, what it produces left
    -- to the induction hypothesis
    if head == ``Specimen.searchWorker then
      cands := cands.push (do
        let ty ← whnfR (← instantiateMVars (← g.getType))
        let x := (ty.getArg! 1).getArg! 1
        let some w := x.getAppFn.constName? | throwError "searchWorker: no worker"
        unless (← getEnv).contains (w ++ `searchHits) do
          throwError "searchWorker: {w} has no searchHits"
        let xargs := x.getAppArgs.extract 7 x.getAppNumArgs
        let hh := mkAppN (← mkConstWithFreshMVarLevels (w ++ `searchHits)) xargs
        let lem ← mkAppM ``searchWorker_ok #[hh]
        timed "searchWorker" (g.apply lem))
    let concl (e : Expr) : MetaM (Option Name) := do
      forallTelescope (← instantiateMVars (← inferType e)) fun _ b => accHead b
    for h in facts do
      if (← concl h) == some head then cands := cands.push (timed "fact" (withReducible (g.apply h)))
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← concl d.toExpr) == some head then cands := cands.push (timed "hyp" (withReducible (g.apply d.toExpr)))
    trace[specimen.reach] "accept {head}, {cands.size} candidates"
    firstOf cands.toList
  | "check" =>
    -- A premise checked on the way: its verdict, from the premise or its negation in context, by the
    -- check's `DecOptComplete` or `DecOptRefuteComplete` instance, which the `match` then reduces on.
    -- What it checks must be fixed first.
    -- (a `match` on a checker of the block's verdict: the verdict assumed, and accepted by the
    -- induction hypothesis, whether or not something is still to choose)
    let onChecker ← do
      let ty ← whnfR (← instantiateMVars (← g.getType))
      match ← matchMatcherApp? ty with
      | some m =>
        let env ← getEnv
        pure (m.discrs.any fun d => match d.getAppFn.constName? with
          | some c => Specimen.isDerivedWorker env c [.Checker]
          | none => false)
      | none => pure false
    if hasMV || onChecker then
      -- What it checks is fixed only by the branch of a verdict (an equation under `.ok true`): the
      -- verdict assumed, as a goal of its own `d = v` decided once the branch has fixed it. Tried
      -- before waiting: the witnesses left would otherwise be chosen blind.
      -- as `headKind` saw it: a `match` on what the choices fixed reduced to the check under it
      let ty ← whnfR (← instantiateMVars (← g.getType))
      let assume := (← (IO.getEnv "SPECIMEN_NO_ASSUME_VERDICT" : IO _)).isNone
      if let some m ← (if assume then matchMatcherApp? ty else pure none) then
        if h : 0 < m.discrs.size then
          let d := m.discrs[0]
          let dTy ← whnfR (← inferType d)
          if dTy.isAppOfArity ``Except 2 && (dTy.getArg! 1).isConstOf ``Bool then
            let vals := [true, false].map fun b =>
              mkApp3 (mkConst ``Except.ok [levelZero, levelZero]) (dTy.getArg! 0) (mkConst ``Bool)
                (if b then mkConst ``Bool.true else mkConst ``Bool.false)
            if let some d ← firstOf (vals.map fun v => do
              let hd ← mkFreshExprMVar (← mkEq d v)
              let r ← g.rewrite ty hd
              let g' ← g.replaceTargetEq r.eNew r.eqProof
              let gs ← Lean.Elab.Tactic.run g' (evalTactic (← `(tactic| simp only [])))
              return gs ++ [hd.mvarId!] ++ r.mvarIds) then
              return some d
      -- What it checks fixed by a premise or its negation in context, by unifying with it (`a ≠ b`
      -- for a `b` no equation fixes): the check, fixed, is then decided as any other. Tried before
      -- waiting, which would leave the witness to be chosen blind.
      let unfixed? : TacticM (Option Expr) := do
        let ty ← whnfR (← instantiateMVars (← g.getType))
        let some e := ty.find? fun e => e.isAppOf ``DecOpt.decOpt && !e.hasLooseBVars | return none
        let P := e.getArg! 0
        return if (← instantiateMVars P).hasExprMVar then some P else none
      if !onChecker && specimen.reachExtended.get (← getOptions) then
        if let some P ← unfixed? then
          let mut hyps : List (TacticM (List MVarId)) := []
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            for prop in [P, mkNot P] do
              hyps := hyps ++ [do
                unless ← withDefault (isDefEq d.type prop) do throwError "no"
                if (← instantiateMVars P).hasExprMVar then throwError "no"
                pure [g]]
          if let some d ← firstOf hyps then return some d
      if !waiting.contains g && rest.any (!waiting.contains ·) then
        return ← reachSolve ctr headCache facts (rest ++ [g]) deferred (depth + 1) (g :: waiting)
      return none
    let ty ← whnfR (← instantiateMVars (← g.getType))
    let isCheck (e : Expr) := e.isAppOf ``DecOpt.decOpt && !e.hasLooseBVars
    let inDiscr : Option Expr := (← matchMatcherApp? ty).bind fun m => m.discrs.findSome? (·.find? isCheck)
    let some e := inDiscr <|> ty.find? isCheck | return none
    let P := e.getArg! 0
    let lctx ← getLCtx
    -- The verdict from a proof `pf` of `P` (by `DecOptComplete`) or of `¬ P` (by `DecOptRefuteComplete`).
    let useProof (lem : Name) (pf : Expr) : TacticM (List MVarId) := do
      let f ← mkAppOptM lem #[P, e.getArg! 1, none, pf, e.getArg! 2]
      let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType f) (some 1)
      let hs := mvs[0]!
      let eq := mkApp f hs
      let r ← g.rewrite ty eq
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      let gs ← Lean.Elab.Tactic.run g' (evalTactic (← `(tactic| simp only [DecOpt.negOpt, Bool.not_true,
        Bool.not_false])))
      return gs ++ [hs.mvarId!] ++ r.mvarIds
    -- With a check that answers alike at every size (`DecOptCompleteAll`), the verdict needs no bound.
    let useProofAll (lem : Name) (pf : Expr) : TacticM (List MVarId) := do
      let eq ← mkAppOptM lem #[P, e.getArg! 1, none, pf, e.getArg! 2]
      let r ← g.rewrite ty eq
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      let gs ← Lean.Elab.Tactic.run g' (evalTactic (← `(tactic| simp only [DecOpt.negOpt, Bool.not_true,
        Bool.not_false])))
      return gs ++ r.mvarIds
    let mut cands : Array (TacticM (List MVarId)) := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      for (lem, prop) in [(``DecOptCompleteAll.ok, P), (``DecOptRefuteCompleteAll.ok, mkNot P)] do
        cands := cands.push (do
          unless ← isDefEq d.type prop do throwError "no"
          useProofAll lem d.toExpr)
    -- A proof of `P` or `¬ P` by a closing tactic (a check of what the case already fixes, such as
    -- `b = b`, has no hypothesis), made once for each and only where a law could use it.
    let dec := e.getArg! 1
    let hasLaw (cls : Name) : TacticM Bool := do
      return (← synthInstance? (mkApp2 (mkConst cls) P dec)).isSome
    let tacMemo ← IO.mkRef (({} : Std.HashMap Bool (Option Expr)))
    let tacProve (neg : Bool) : TacticM (Option Expr) := do
      if let some r := (← tacMemo.get)[neg]? then return r
      let prop := if neg then mkNot P else P
      let r ← timedT "c_tacprove" <| observing? do
        let pv ← mkFreshExprMVar prop
        -- what a premise of a check cannot need, and what makes `contradiction` and `simp_all`
        -- slow: the induction hypotheses, the observations, and what a bound still to choose is in
        let pid ← pv.mvarId!.withContext do
          let mut drop : Array FVarId := #[]
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            let ty ← instantiateMVars d.type
            if ty.hasExprMVar || (ty.find? (·.isConstOf ``Specimen.Correctness.Produces)).isSome then
              drop := drop.push d.fvarId
          pv.mvarId!.tryClearMany drop
        let pv' := mkMVar pid
        -- the closing tactics in order of cost, each timed (`SPECIMEN_REACH_STATS`)
        let tacs : List (String × TSyntax `tactic) := [
          ("rfl", ← `(tactic| rfl)), ("assumption", ← `(tactic| assumption)),
          ("decide", ← `(tactic| (set_option maxHeartbeats 20000 in decide))),
          ("true", ← `(tactic| exact True.intro)),
          ("simp_all", ← `(tactic| (set_option maxHeartbeats 20000 in simp_all)))]
        -- (`specimen.reachSimpAll` false: without the last resort, which costs the most and rarely
        -- closes one)
        let tacs := if specimen.reachSimpAll.get (← getOptions) then tacs else tacs.filter (·.1 != "simp_all")
        let mut done ← timedT "c_tp_contra" (do
          let s ← saveState
          if ← syntacticContra pv'.mvarId! then pure true else s.restore; pure false)
        for (lbl, t) in (if done then [] else tacs) do
          let s ← saveState
          let ok ← timedT s!"c_tp_{lbl}" <| tryCatchRuntimeEx (do
            let rest ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run pv'.mvarId! (Tactic.withoutRecover (evalTactic t))
            pure rest.isEmpty) fun _ => pure false
          if ok then
            if reachStatsOn then
              bump s!"c_tpok_{lbl}" 1

            done := true; break
          s.restore
        unless done do throwError "no"
        instantiateMVars pv
      tacMemo.modify (·.insert neg r)
      return r
    for (lem, cls, neg) in [(``DecOptCompleteAll.ok, ``DecOptCompleteAll, false),
        (``DecOptRefuteCompleteAll.ok, ``DecOptRefuteCompleteAll, true)] do
      if ← hasLaw cls then
        cands := cands.push (do
          let some pf ← tacProve neg | throwError "no"
          useProofAll lem pf)
    for d in lctx do
      if d.isImplementationDetail then continue
      for (lem, prop) in [(``DecOptComplete.ok, P), (``DecOptRefuteComplete.ok, mkNot P)] do
        cands := cands.push (do
          unless ← isDefEq d.type prop do throwError "no"
          useProof lem d.toExpr)
    for (lem, cls, neg) in [(``DecOptComplete.ok, ``DecOptComplete, false),
        (``DecOptRefuteComplete.ok, ``DecOptRefuteComplete, true)] do
      if ← hasLaw cls then
        cands := cands.push (do
          let some pf ← tacProve neg | throwError "no"
          useProof lem pf)
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
      -- only the hypotheses about the same relation: unifying the rest fails, after a state saved
      let gTy ← instantiateMVars (← g.getType)
      let gHead := gTy.getAppFn.constName?
      let mut hs : Array LocalDecl := #[]
      for d in lctx do
        if d.isImplementationDetail then continue
        if let some h := gHead then
          let dHead := (← instantiateMVars d.type).getAppFn.constName?
          if dHead.isSome && dHead != some h then continue
        hs := hs.push d
      if let some d ← firstOf (hs.toList.map fun d => (do
          unless ← isDefEq (← g.getType) d.type do throwError "no"
          g.assign d.toExpr
          pure ([] : List MVarId) : TacticM (List MVarId))) then
        return some d
      -- Or it waits for the other choices to fix it.
      if !waiting.contains g && rest.any (!waiting.contains ·) then
        return ← reachSolve ctr headCache facts (rest ++ [g]) deferred (depth + 1) (g :: waiting)
      return none
    attempt (do
      -- the cheap closers first; the bound's arithmetic only for a comparison of numbers, on the
      -- arithmetic hypotheses (`reach_bound` simplifies at every hypothesis, the large ones included)
      let ty ← instantiateMVars (← g.getType)
      if isNatArith ty then
        if ← fastBound g then return []
        let g' ← g.withContext do
          let mut drop : Array FVarId := #[]
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            unless ← isProp d.type do continue
            unless isNatArith (← instantiateMVars d.type) do drop := drop.push d.fvarId
          g.tryClearMany drop
        let r ← timedT "c_othertac" <| Lean.Elab.Tactic.run g' (evalTactic (← `(tactic|
          first | assumption | reach_bound)))
        unless r.isEmpty do throwError "open"
        return []
      -- a `match` on what the choices fixed (a projection of a tuple, a constructor): reduced, it goes
      -- back to the search, which takes its `∃` and `∧` apart (a `simp` reaches the same, slowly)
      if let some m ← matchMatcherApp? ty then
        -- a discriminant a hypothesis equates to a value (`ip s = some ip`, a premise of the case):
        -- rewritten, so that the match reduces
        let mut g := g
        let extended := specimen.reachExtended.get (← getOptions)
        for d in m.discrs do
          if d.hasLooseBVars || d.hasExprMVar then continue
          for h in ← getLCtx do
            if h.isImplementationDetail then continue
            let hty ← instantiateMVars h.type
            let some (_, l, r) := hty.eq? | continue
            -- either way round (`some s' = removeBucket n s`, a premise as the relation states it)
            unless l == d || (r == d && extended) do continue
            try
              let rw ← g.rewrite (← g.getType) h.toExpr (symm := r == d && l != d)
              g ← g.replaceTargetEq rw.eNew rw.eqProof
              break
            catch _ => pure ()
        let r ← try Lean.Elab.Tactic.run g (evalTactic (← `(tactic| dsimp only))) catch _ => pure [g]
        if let [g'] := r then
          if (← instantiateMVars (← g'.getType)) != ty then return [g']
        else if r.isEmpty then return []
      let t0 ← IO.monoMsNow
      let r ← try
          if reachStatsOn then
            -- (the same closers one at a time, each timed and its successes counted)
            let tacs : List (String × TSyntax `tactic) := [("assumption", ← `(tactic| assumption)),
              ("rfl", ← `(tactic| rfl)), ("true", ← `(tactic| exact True.intro)),
              ("simp", ← `(tactic| (set_option maxHeartbeats 20000 in simp)))]
            let mut res : Option (List MVarId) := none
            for (lbl, t) in tacs do
              let s ← saveState
              let ok ← timedT s!"c_ot_{lbl}" <| try
                  let rest ← Lean.Elab.Tactic.run g (evalTactic t); pure (some rest)
                catch _ => pure none
              if let some rest := ok then
                bump s!"c_otok_{lbl}" 1; res := some rest; break
              s.restore
            match res with
            | some rest => pure rest
            | none => throwError "open"
          else
          timedT "c_othertac" <| Lean.Elab.Tactic.run g (evalTactic (← `(tactic|
            first | assumption | rfl | exact True.intro | (set_option maxHeartbeats 20000 in simp))))
        finally
          let dt := (← IO.monoMsNow) - t0
          if reachStatsOn && dt > 300 then
            timerLog s!"  OTHERTAC {dt} ms: {((← Meta.ppExpr ty).pretty).take 1500}"
      unless r.isEmpty do throwError "open"
      pure [])

end

/-- The largest number of parts a bound's expression divides its variable into. -/
partial def divisor (e : Expr) : Nat :=
  let here : Nat :=
    if e.isAppOfArity ``HDiv.hDiv 6 || e.isAppOfArity ``Nat.div 2 then
      (e.getAppArgs.back!.nat?).getD 1
    else if e.isAppOfArity ``Specimen.Correctness.canon 2 then
      ((e.getArg! 0).nat?.getD 0) + 1
    else 1
  e.getAppArgs.foldl (fun m a => max m (divisor a)) here

/-- `v`, a bound written in the context of the branch `g`, taken into the context of the bound `?M` it
is for. A case split stands values for some of `?M`'s variables (`?M' args`, delayed-assigned `?M`);
each is taken back to its variable, so that `?M`'s value, the case's values put back, is `v`. `none`
when the result is not well typed there (a value that a type of the bound depends on cannot always be
taken back). -/
def toBoundContext? (M : Expr) (g : MVarId) (v : Expr) : MetaM (Option Expr) := do
  let v ← instantiateMVars v
  let inCtx (w : Expr) : MetaM Bool := M.mvarId!.withContext do
    let mctx ← getLCtx
    if w.hasAnyFVar (fun fv => !mctx.contains fv) then return false
    try Meta.check w; pure true catch _ => pure false
  if ← inCtx v then return some v
  let cands ← g.withContext do
    let mut out : Array Expr := #[]
    for d in ← getLCtx do
      let h ← instantiateMVars d.type
      unless h.isAppOfArity ``LE.le 4 do continue
      let a := h.getArg! 2
      let f := a.getAppFn
      unless f.isMVar do continue
      let some da ← getDelayedMVarAssignment? f.mvarId! | continue
      unless da.mvarIdPending == M.mvarId! do continue
      let args := a.getAppArgs
      if args.size < da.fvars.size then continue
      let mut w := v
      -- the values first, while every variable they mention is in scope, then the variables
      for i in [0:da.fvars.size] do
        let arg ← instantiateMVars args[i]!
        unless arg.isFVar do w := (← kabstract w arg).instantiate1 da.fvars[i]!
      for i in [0:da.fvars.size] do
        let arg ← instantiateMVars args[i]!
        if arg.isFVar then w := w.replaceFVar arg da.fvars[i]!
      out := out.push w
    return out
  for w in cands do
    if ← inCtx w then return some w
  return none

/-- Choose each `?M` that bounds a variable: the bounds left on it, summed, times the most parts any of
them divides the variable into; then close them. -/
def closeDeferred (ds : List MVarId) : TacticM (List MVarId) := do
  let mut groups : Array (Expr × List MVarId) := #[]
  for g in ds do
    if ← g.isAssigned then continue
    let some M ← boundGroup? g | continue
    match groups.findIdx? (·.1 == M) with
    | some i => groups := groups.modify i fun (m, gs) => (m, g :: gs)
    | none => groups := groups.push (M, [g])
  let tg ← IO.monoMsNow
  for (M, gs) in groups do
    if ← M.mvarId!.isAssigned then continue
    let mut sum : Expr := mkNatLit 0
    let mut d := 1
    for g in gs do
      let ty ← whnfR (← instantiateMVars (← g.getType))
      let t ← g.withContext do pure ((← toBoundContext? M g (ty.getArg! 2)).getD (ty.getArg! 2))
      sum ← mkAppM ``HAdd.hAdd #[sum, t]
      d := max d (divisor (← instantiateMVars (ty.getArg! 3)))
    -- `?M` is the case's own goal (synthetic opaque), so it is assigned rather than unified; a
    -- function of the values a case split put in its place, it is constant.
    let v ← mkAppM ``HMul.hMul #[mkNatLit d, sum]
    let v ← forallTelescope (← inferType M) fun xs _ => mkLambdaFVars xs v
    M.mvarId!.assign v
  let ta ← IO.monoMsNow
  let mut nb := 0
  for g in ds do
    if ← g.isAssigned then continue
    nb := nb + 1
    -- the bound is arithmetic: `simp … at *` and `omega` would go through every hypothesis, the
    -- induction hypotheses and the relations' among them, so only the arithmetic ones are kept
    let g ← g.withContext do
      let mut drop : Array FVarId := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        unless ← isProp d.type do continue
        unless isNatArith (← instantiateMVars d.type) do drop := drop.push d.fvarId
      g.tryClearMany drop
    if ← fastBound g then continue
    let r ← Lean.Elab.Tactic.run g (evalTactic (← `(tactic| reach_bound)))
    unless r.isEmpty do throwError "reach_close: a bound does not close{indentExpr (← g.getType)}"
  if reachStatsOn then
    timerLog s!"  CLOSEDEFERRED groups {groups.size} group {ta - tg} ms, {nb} bounds {(← IO.monoMsNow) - ta} ms"
  return []

/-- Close `g` from a hypothesis `¬ P` and a `@[specimen_check]` law `(test) = true → P` whose test
the branch passed (a hypothesis `test = true`, or `(!test) = false`). -/
def closeByCheckLaw (g : MVarId) : TacticM Bool := g.withContext do
  let laws := (specimenCheckExt.getState (← getEnv)).toArray
  if laws.isEmpty then return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Not 1 do continue
    let P := ty.appArg!
    let some head := P.getAppFn.constName? | continue
    for l in laws do
      let concl ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels l)) fun _ b => pure b
      unless concl.getAppFn.constName? == some head do continue
      let saved ← saveState
      let ok ← try
          let pv ← mkFreshExprMVar P
          let rest ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run pv.mvarId! (Tactic.withoutRecover (evalTactic (← `(tactic|
            (apply $(mkIdent l):ident <;> first | assumption | (set_option maxHeartbeats 5000 in simp_all only [Bool.not_eq_false', Bool.not_eq_true']))))))
          if rest.isEmpty then
            g.assign (← mkAbsurd (← g.getType) (← instantiateMVars pv) d.toExpr)
            pure true
          else pure false
        catch _ => pure false
      if ok then return true
      saved.restore
  return false

/-- Close `g` when it is the `error` case of a `match` on a check's verdict, `decOpt P n` neither
`.ok true` nor `.ok false` (two hypotheses `decOpt P n = .ok b → False`), for a check that unfolds to
`.ok t` for some test `t`: by cases on `t`. -/
def closeErrorBranch (g : MVarId) : MetaM Bool := g.withContext do
  let lctx ← getLCtx
  let mut negs : Array (Expr × Bool × Expr) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let .forallE _ dom (.const ``False _) _ := ty | continue
    let some (_, lhs, rhs) := dom.eq? | continue
    unless lhs.isAppOf ``DecOpt.decOpt && rhs.isAppOfArity ``Except.ok 3 do continue
    let v := rhs.getArg! 2
    let b := if v.isConstOf ``Bool.true then some true else if v.isConstOf ``Bool.false then some false else none
    let some b := b | continue
    negs := negs.push (lhs, b, d.toExpr)
  for (lhs, b, hT) in negs do
    unless b do continue
    let some (_, _, hF) := negs.find? fun (l, b', _) => !b' && l == lhs | continue
    let r ← whnfD lhs
    unless r.isAppOfArity ``Except.ok 3 do continue
    let t := r.getArg! 2
    let some pf ← observing? do
      -- `lhs = .ok t`, by unfolding; then on `t`
      let e ← mkEqRefl lhs
      let e ← mkExpectedTypeHint e (← mkEq lhs r)
      let motive ← withLocalDeclD `x (mkConst ``Bool) fun x => do
        mkLambdaFVars #[x] (← mkArrow (← mkEq t x) (mkConst ``False))
      let caseFor (val : Bool) (h : Expr) : MetaM Expr := do
        let bv := if val then mkConst ``Bool.true else mkConst ``Bool.false
        withLocalDeclD `hb (← mkEq t bv) fun hb => do
          let okFn := r.appFn!
          let e2 ← mkCongrArg okFn hb
          mkLambdaFVars #[hb] (mkApp h (← mkEqTrans e e2))
      let pf := mkApp4 (mkConst ``Bool.casesOn [levelZero]) motive t (← caseFor false hF) (← caseFor true hT)
      let pf := mkApp pf (← mkEqRefl t)
      let pf ← mkFalseElim (← g.getType) pf
      Meta.check pf
      return pf
    | continue
    g.assign pf
    return true
  return false

/-- Close `g` from contradictory hypotheses: directly, by simplification (a `Decidable` check's verdict
is `decide`), or by cases on one inductive hypothesis, each case then contradictory. -/
def closeByContradiction (g : MVarId) (cheap : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ← closeByContradictionCore g
  unless ok do saved.restore
  return ok
where closeByContradictionCore (g : MVarId) : TacticM Bool := do
  -- A premise `h : P` in context whose check is complete (`DecOptCompleteAll`) runs a test `t` that
  -- answers `true`; a branch the walk took on `t = false` cannot be.
  let byVerdict ← g.withContext do
    let lctx ← getLCtx
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.hasExprMVar || !(← isProp ty) then continue
      let some n := ty.getAppFn.constName? | continue
      unless ((← getEnv).find? n).any (·.isInductive) do continue
      let some dec ← synthInstance? (← mkAppM ``DecOpt #[ty]) | continue
      let some inst ← synthInstance? (mkApp2 (mkConst ``DecOptCompleteAll) ty dec) | continue
      let pf ← mkAppOptM ``DecOptCompleteAll.ok #[ty, dec, inst, d.toExpr, mkNatLit 0]
      -- `decOpt P 0 = .ok t`, by unfolding the check
      let lhs ← whnfD (← mkAppOptM ``DecOpt.decOpt #[ty, dec, mkNatLit 0])
      unless lhs.isAppOfArity ``Except.ok 3 do continue
      let t := lhs.getArg! 2
      for d' in lctx do
        if d'.isImplementationDetail then continue
        let ty' ← instantiateMVars d'.type
        unless ty'.isAppOfArity ``Eq 3 && (ty'.getArg! 2).isConstOf ``Bool.false do continue
        unless ← withNewMCtxDepth (isDefEq (ty'.getArg! 1) t) do continue
        -- `t = true` from the check, `t = false` from the branch
        let some r ← observing? (do
            let tTrue ← mkEq t (mkConst ``Bool.true)
            let ok ← mkEq lhs ((← inferType pf).getArg! 2)
            let pf' ← mkExpectedTypeHint pf ok
            let ht ← mkExpectedTypeHint (← mkAppM ``Except.ok.inj #[pf']) tTrue
            let ft ← mkExpectedTypeHint d'.toExpr (← mkEq t (mkConst ``Bool.false))
            let e ← mkEqTrans (← mkEqSymm ht) ft
            let f ← mkNoConfusion (← g.getType) e
            Meta.check f
            pure f) | continue
        return some r
    return none
  if let some f := byVerdict then
    g.assign f
    return true
  if cheap then
    -- a clash in the branch's own hypotheses (a check's verdict against what the case has), on a
    -- small budget: a branch that is not contradictory is left to the search. The induction
    -- hypotheses and what mentions a bound still to choose cannot clash, and are large: cleared.
    let r ← observing? (do
      let g ← g.withContext do
        let mut drop : Array FVarId := #[]
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let ty ← instantiateMVars d.type
          if ty.hasExprMVar || (ty.find? (·.isConstOf ``Specimen.Correctness.Produces)).isSome then
            drop := drop.push d.fvarId
        g.tryClearMany drop
      let r ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run g (Tactic.withoutRecover (evalTactic (← `(tactic|
        (exfalso; first | contradiction | (set_option maxHeartbeats 5000 in simp_all [DecOpt.decOpt, DecOpt.negOpt]))))))
      unless r.isEmpty do throwError "open")
    return r.isSome
  let direct ← observing? (do
    let r ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run g (Tactic.withoutRecover (evalTactic (← `(tactic|
      (exfalso; first | contradiction | simp_all [DecOpt.decOpt, DecOpt.negOpt])))))
    unless r.isEmpty do throwError "open")
  if direct.isSome then
    if reachStatsOn then timerLog "  CONTRA-BY direct"
    return true
  -- The bounds still to be chosen are not needed for a contradiction, and `cases` cannot revert them.
  let g ← g.withContext do
    let mut mvHyps : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).hasExprMVar then mvHyps := mvHyps.push d.fvarId
    g.tryClearMany mvHyps
  let hyps ← g.withContext do
    let mut hs : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if !(← isProp ty) then continue
      let some n := ty.getAppFn.constName? | continue
      if n == ``Eq || n == ``Ne || n == ``Not then continue
      if ((← getEnv).find? n).any (·.isInductive) then hs := hs.push d.fvarId
    pure hs
  for h in hyps do
    let ok ← observing? (do
      let gs ← g.cases h
      for sg in gs do
        let r ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run sg.mvarId (Tactic.withoutRecover (evalTactic (← `(tactic|
          (exfalso; first | contradiction | simp_all [DecOpt.decOpt, DecOpt.negOpt])))))
        unless r.isEmpty do throwError "open")
    if ok.isSome then
      if reachStatsOn then
        let ty ← g.withContext do instantiateMVars (← h.getType)
        timerLog s!"  CONTRA-BY cases {ty.getAppFn.constName?}"
      return true
  return false

/-- A premise `P` the case has whose check the branch took `false` (`decOpt P s = .ok false`), with no
`DecOptComplete` law for the check. -/
def doomedVerdict? (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isAppOf ``DecOpt.decOpt && rhs.isAppOfArity ``Except.ok 3 && (rhs.getArg! 2).isConstOf ``Bool.false do
      continue
    let P := lhs.getArg! 0
    if P.hasExprMVar then continue
    let some dec := lhs.getArg? 1 | continue
    let has ← lctx.anyM fun d' => do
      if d'.isImplementationDetail then return false
      withNewMCtxDepth (isDefEq d'.type P)
    unless has do continue
    if (← synthInstance? (mkApp2 (mkConst ``DecOptCompleteAll) P dec)).isSome then continue
    if (← synthInstance? (mkApp2 (mkConst ``DecOptComplete) P dec)).isSome then continue
    return some P
  return none

/-- Make the choices the reach walk left (see the module docstring), with facts `t, …`. -/
syntax "reach_close" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| reach_close $[[$ts,*]]?) => withMainContext do
    -- a fact named is taken as its constant, not elaborated: a polymorphic one's instance arguments
    -- (`[DecidableEq α]`) have nothing to be synthesized from until it is applied
    let facts ← (ts.map (·.getElems) |>.getD #[]).filterMapM fun t => do
      if t.isIdent then
        if let some c ← (try some <$> realizeGlobalConstNoOverload t catch _ => pure none) then
          return some (← mkConstWithFreshMVarLevels c)
      try some <$> elabTerm t none catch _ => pure none
    -- The guards the walk could not evaluate, and the options of the guarded pools.
    let _ ← observing? (evalTactic (← `(tactic| simp only [ite_true, ite_false, ↓reduceIte,
      Option.some.injEq, exists_eq_left', exists_eq_left, true_and, and_true, reduceCtorEq, false_and,
      and_false, false_or, or_false, exists_false])))
    if (← getUnsolvedGoals).isEmpty then return
    let g ← getMainGoal
    let t0 ← IO.monoMsNow
    if reachStatsOn then (do let tid ← IO.getTID; kindCountsByTid.modify (·.insert tid {}) : IO Unit)
    let ctr ← IO.mkRef 0
    let headCache ← IO.mkRef {}
    (do let tid ← IO.getTID; closedFailures.modify (·.insert tid {}) : IO Unit)
    -- A branch the case cannot be in, seen at once (a check's verdict against its premise, a
    -- constructor clash), before any choice is searched for it.
    let tc ← IO.monoNanosNow
    let eb ← safeClose (closeErrorBranch g)
    let tc1 ← IO.monoNanosNow
    (if reachStatsOn then bump "errBranch_us" ((tc1 - tc) / 1000) else pure () : IO Unit)
    if eb then
      if reachStatsOn then timerLog s!"  RC errorbranch {(← IO.monoMsNow) - t0}"
      replaceMainGoal []; return
    let cl ← safeClose (closeByCheckLaw g)
    let tc2 ← IO.monoNanosNow
    (if reachStatsOn then bump "checkLaw_us" ((tc2 - tc1) / 1000) else pure () : IO Unit)
    if cl then
      if reachStatsOn then timerLog s!"  RC checklaw {(← IO.monoMsNow) - t0}"
      replaceMainGoal []; return
    -- With the verdicts decided by the search rather than split on, a branch is rarely
    -- contradictory, and the clash check costs more than the search it would save: it waits for the
    -- search to fail (`SPECIMEN_CONTRA_FIRST` restores it here).
    let cheapOk ← if (← IO.getEnv "SPECIMEN_CONTRA_FIRST").isSome then safeClose (closeByContradiction g (cheap := true))
      else do
        -- the clashes that cost nothing to find: a check's verdict against its premise, two
        -- hypotheses `P` and `¬ P`, a constructor clash
        let s ← saveState
        let ok ← (do
            let g' ← g.withContext do
              let mut drop : Array FVarId := #[]
              for d in ← getLCtx do
                if d.isImplementationDetail then continue
                let ty ← instantiateMVars d.type
                if ty.hasExprMVar || (ty.find? (·.isConstOf ``Specimen.Correctness.Produces)).isSome then
                  drop := drop.push d.fvarId
              g.tryClearMany drop
            syntacticContra g') <|> pure false
        unless ok do s.restore
        pure ok
    let tc' ← IO.monoNanosNow
    (if reachStatsOn then bump "cheapContra_us" ((tc' - tc) / 1000) else pure () : IO Unit)
    if cheapOk then
      if reachStatsOn then
        timerLog s!"  RC cheapcontra {(← IO.monoMsNow) - t0}"
        if (← IO.getEnv "SPECIMEN_CONTRA_GOALS").isSome then
          timerLog s!"  CONTRAGOAL\n{((← Meta.ppGoal g).pretty).take 5000}\n  ENDCONTRA"
      replaceMainGoal []; return
    -- A branch on a check's `false` verdict for a premise the case has, of a check with no
    -- completeness law: no choice closes it, and only that law could rule it out.
    let td ← IO.monoNanosNow
    let doomed ← doomedVerdict? g
    let td' ← IO.monoNanosNow
    (if reachStatsOn then bump "doomed_us" ((td' - td) / 1000) else pure () : IO Unit)
    if let some P := doomed then
      if ← safeClose (closeByContradiction g) then replaceMainGoal []; return
      throwError "reach_close: the branch's check of{indentExpr P}\nanswers false, and the check has no \
        completeness law (`DecOptComplete`) to rule the branch out"
    let saved ← saveState
    let res ← reachSolve ctr headCache facts [g] []
    -- A bound the case's `?M` is to cover must be stated in `?M`'s own context: one that mentions a
    -- variable of this branch alone (a value it split out) cannot be covered, and the choices that
    -- left it are no proof. The branch then falls to the contradictions, as if no choice closed it.
    let res ← match res with
      | none => pure none
      | some ds => do
        let ok ← ds.allM fun d => d.withContext do
          let some M ← boundGroup? d | return true
          let ty ← whnfR (← instantiateMVars (← d.getType))
          return (← toBoundContext? M d (ty.getArg! 2)).isSome
        if ok then pure (some ds) else do saved.restore; pure none
    let dt := (← IO.monoMsNow) - t0
    if reachStatsOn then timerLog s!"  RC search {dt} {res.isSome}"
    if dt > (((← IO.getEnv "SPECIMEN_LOG_MS").bind String.toNat?).getD 1000) then
      let hd := ((← instantiateMVars (← g.getType)).getAppFn.constName?).getD `_
      timerLog s!"  reach_close {dt} ms attempts {← ctr.get} {if res.isSome then "ok" else "none"} {hd}"
      let slowMs := ((← IO.getEnv "SPECIMEN_SLOW_MS").bind String.toNat?).getD 20000
      if reachStatsOn && (dt > slowMs || (← IO.getEnv "SPECIMEN_KINDS").isSome) then
        timerLog s!"  SLOWKINDS tid {← IO.getTID} {(← myCounts).toList}"
      if dt > slowMs && reachStatsOn then
        timerLog s!"  SLOWGOAL {((← Meta.ppGoal g).pretty).take 12000}\n  ENDSLOW"
    let some ds := res | do
      -- No choice reaches the output: the branch of the walk is one the case cannot be in, its
      -- hypotheses contradictory (a check's verdict against the premise it checks, say).
      let t1 ← IO.monoMsNow
      -- The branch may be contradictory after all: the clash check on its own hypotheses, then the
      -- case splits on a budget (a branch they do not refute quickly is a failure).
      let ok ← do
        if ← safeClose (closeByContradiction g (cheap := true)) then pure true
        else timedT "c_contraFull" (withTheReader Core.Context
          (fun c => { c with maxHeartbeats := 20000 * 1000 }) (safeClose (closeByContradiction g)))
      timerLog s!"  reach_close contra {ok} {(← IO.monoMsNow) - t1} ms after {dt} ms search"
      trace[specimen.reach] "contradiction: {ok} for{indentD (MessageData.ofGoal g)}"
      if ok then replaceMainGoal []; return
      if (← IO.getEnv "SPECIMEN_REACH_FAILS").isSome then
        let tgt ← instantiateMVars (← g.getType)
        let mut insts : Array String := #[]
        let found ← IO.mkRef (#[] : Array Expr)
        Meta.forEachExpr tgt fun e => do if e.isAppOf ``BacktrackGenFor.gen then found.modify (·.push e)
        for e in ← found.get do
          let args := e.getAppArgs
          let ps ← args.filterMapM fun a => do
            let ty ← whnfR (← inferType a)
            return if ty.isAppOf ``BacktrackGenFor then a.getAppFn.constName? else none
          insts := insts ++ ps.map toString
        timerLog s!"  REACHFAIL in {(← Term.getDeclName?).getD `_} insts {insts}\n{((← Meta.ppGoal g).pretty).take 6000}\n  ENDFAIL"
      -- the unconstrained draws in the goal whose type has no completeness instance: their values
      -- cannot be chosen, which is the likely cause
      let draws ← IO.mkRef (#[] : Array (Expr × Expr))
      Meta.forEachExpr (← instantiateMVars (← g.getType)) fun e => do
        if e.isAppOf ``Basalt.ArbitrarySized.arbitrarySized && e.getAppNumArgs ≥ 2 then
          let d := (e.getArg! 0, e.getArg! 1)
          unless (← draws.get).contains d do draws.modify (·.push d)
      let mut missing : Array MessageData := #[]
      for (α, inst) in ← draws.get do
        let ok ← try pure (← synthInstance? (mkApp2 (mkConst ``ArbitrarySizedComplete) α inst)).isSome
          catch _ => pure false
        unless ok do missing := missing.push m!"`ArbitrarySizedComplete {α}` (for the instance `{inst}`)"
      unless missing.isEmpty do
        throwError "reach_close: no choice closes{indentExpr (← g.getType)}\nIt draws values with no \
          completeness instance, which it needs to choose them: {MessageData.joinSep missing.toList ", "}"
      throwError "reach_close: no choice closes{indentExpr (← g.getType)}"
    -- The bounds wait for the case's other branches, which share the case's `?M`: they are closed
    -- together, by `reach_close_bounds`, once every branch has made its choices.
    replaceMainGoal ds

/-- Close the bounds every branch of a case left (`reach_close`), each case's `?M` the sum of what
all of them need. -/
syntax "reach_close_bounds" : tactic

elab_rules : tactic
  | `(tactic| reach_close_bounds) => do
    let t0 ← IO.monoMsNow
    let gs ← getUnsolvedGoals
    let ds ← gs.filterM fun g => deferredBound? g
    let t1 ← IO.monoMsNow
    let _ ← closeDeferred ds
    -- The facts about a split's parts deferred until the bounds were chosen (a part below the fuel):
    -- arithmetic on the parts, now that the bounds are fixed.
    for g in gs do
      if ← g.isAssigned then continue
      let ty ← instantiateMVars (← g.getType)
      unless (ty.find? (·.isAppOf ``fillParts)).isSome && !ty.hasExprMVar do continue
      let saved ← saveState
      try
        let rest ← Lean.Elab.Tactic.run g (evalTactic (← `(tactic| reach_bound)))
        unless rest.isEmpty do saved.restore
      catch _ => saved.restore
    let t2 ← IO.monoMsNow
    setGoals (← gs.filterM fun g => return !(← g.isAssigned))
    if reachStatsOn then
      timerLog s!"  BOUNDS goals {gs.length} deferred {ds.length} filter {t1 - t0} close {t2 - t1} ms"

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
