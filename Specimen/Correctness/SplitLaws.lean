import Specimen.Correctness.ReachClose
import Specimen.Debug

/-!
# What a size split draws

Every split the drawing can produce has one part per call and adds up to at most the size: exactly
the size where the floors fit, each part then at least its floor.
-/

namespace Specimen.Correctness

open Specimen.SizeSplit Basalt

theorem produces_of_frequency {α : Type} {gs : List (Nat × (Unit → SGen α))} {h} {x : α}
    (hx : Produces (frequency gs h) x) : ∃ p ∈ gs, 0 < p.1 ∧ Produces (p.2 ()) x := by
  obtain ⟨p, hp, hw, hr⟩ := (reach_frequency h).mp (reach_of_produces hx)
  exact ⟨p, hp, hw, produces_of_reach hr⟩

theorem uniform_parts : ∀ (k r : Nat) (ps : List Nat), Produces (uniform (k + 1) r : SGen (List Nat)) ps →
    ps.length = k + 1 ∧ ps.sum = r
  | 0, r, ps, h => by
    have := produces_pure_iff.mp h; subst this; simp
  | k + 1, r, ps, h => by
    obtain ⟨j, hj, h⟩ := produces_bind_iff.mp h
    obtain ⟨rest, hrest, h⟩ := produces_bind_iff.mp h
    have := produces_pure_iff.mp h; subst this
    obtain ⟨p, hp, -, hpj⟩ := produces_of_frequency hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := produces_pure_iff.mp hpj; subst this
    have hi := List.mem_range.mp hi
    obtain ⟨h1, h2⟩ := uniform_parts k (r - j) rest hrest
    exact ⟨by simp [h1], by simp only [List.sum_cons, h2]; omega⟩

theorem greedy_parts : ∀ (fs : List Nat) (t : Nat), (greedy fs t).length = fs.length ∧ (greedy fs t).sum ≤ t
  | [], _ => by simp [greedy]
  | f :: fs, t => by
    obtain ⟨h1, h2⟩ := greedy_parts fs (t - min f t)
    simp only [greedy, List.length_cons, h1, List.sum_cons, true_and]
    omega

theorem zipWith_add_parts : ∀ (ps fs : List Nat), ps.length = fs.length →
    (List.zipWith (· + ·) ps fs).length = fs.length ∧
      (List.zipWith (· + ·) ps fs).sum = ps.sum + fs.sum ∧
      List.Forall₂ (· ≤ ·) fs (List.zipWith (· + ·) ps fs)
  | [], [], _ => by simp
  | p :: ps, f :: fs, h => by
    obtain ⟨h1, h2, h3⟩ := zipWith_add_parts ps fs (by simpa using h)
    refine ⟨by simp [h1], by simp only [List.zipWith_cons_cons, List.sum_cons, h2]; omega,
      .cons (Nat.le_add_left _ _) h3⟩

/-- **What a split draws.** One part per call, adding up to at most the size; where the floors fit,
exactly the size, each part at least its floor. -/
theorem draw_parts {fs : List Nat} {total : Nat} {ps : List Nat}
    (h : Produces (draw fs total : SGen (List Nat)) ps) :
    ps.length = fs.length ∧ ps.sum ≤ total ∧ (fs.sum ≤ total → List.Forall₂ (· ≤ ·) fs ps) := by
  unfold draw at h
  split at h
  · rename_i hle
    obtain ⟨us, hus, h⟩ := produces_bind_iff.mp h
    have := produces_pure_iff.mp h; subst this
    cases hk : fs.length with
    | zero =>
      have : fs = [] := List.eq_nil_of_length_eq_zero hk
      subst this
      exact ⟨by simp, by simp, fun _ => by simp⟩
    | succ k =>
      rw [hk] at hus
      obtain ⟨hl, hs⟩ := uniform_parts k _ us hus
      obtain ⟨h1, h2, h3⟩ := zipWith_add_parts us fs (hl.trans hk.symm)
      exact ⟨h1.trans hk, by omega, fun _ => h3⟩
  · rename_i hgt
    have := produces_pure_iff.mp h; subst this
    obtain ⟨h1, h2⟩ := greedy_parts fs total
    exact ⟨h1, h2, fun h => absurd h hgt⟩

/-- The split, for the soundness walk: what it draws, as `draw_parts` says. -/
@[gen_rule]
theorem le_succ_draw {fs : List Nat} {total : Nat} {post : List Nat → Prop} :
    (∀ ps, ps.length = fs.length → ps.sum ≤ total → (fs.sum ≤ total → List.Forall₂ (· ≤ ·) fs ps) →
      post ps) ≤ succObs.spec (draw fs total : SGen (List Nat)) post := fun h ps hps =>
  let ⟨h1, h2, h3⟩ := draw_parts hps
  h ps h1 h2 h3

end Specimen.Correctness

namespace Specimen.Correctness

open Specimen.SizeSplit

theorem minFloorAux_le : ∀ {cs : List (Option Nat)} {c : Nat}, some c ∈ cs →
    ∃ m, minFloor.minFloorAux cs = some m ∧ m ≤ c
  | [], _, h => by simp at h
  | none :: cs, c, h => by
    simp only [List.mem_cons, reduceCtorEq, false_or] at h
    simpa [minFloor.minFloorAux] using minFloorAux_le h
  | some d :: cs, c, h => by
    simp only [minFloor.minFloorAux]
    rcases List.mem_cons.mp h with h | h
    · cases h; split <;> simp_all
    · obtain ⟨m, hm, hle⟩ := minFloorAux_le h
      simp only [hm, Option.some.injEq, exists_eq_left']; omega

/-- **A rule's cost bounds the floor**: the floor is the least cost of the rules that apply. -/
theorem minFloor_le {cs : List (Option Nat)} {c : Nat} (h : some c ∈ cs) : minFloor cs ≤ c := by
  induction cs with
  | nil => simp at h
  | cons d cs ih =>
    rcases d with _ | d
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact ih h
    · simp only [minFloor]
      rcases List.mem_cons.mp h with h | h
      · cases h; split <;> simp_all
      · obtain ⟨m, hm, hle⟩ := minFloorAux_le h
        simp only [hm]; omega

end Specimen.Correctness

namespace Specimen.Correctness

open Specimen.SizeSplit Lean Meta Elab Tactic

theorem minFloor_le_of_exists {cs : List (Option Nat)} {n : Nat} (h : ∃ c, some c ∈ cs ∧ c ≤ n) :
    minFloor cs ≤ n := let ⟨_, hc, hle⟩ := h; Nat.le_trans (minFloor_le hc) hle

/-- The parts at the first `k` positions add up to at most the whole. -/
theorem sizeAt_range_sum_le : ∀ (ps : List Nat) (k : Nat), ((List.range k).map (sizeAt ps)).sum ≤ ps.sum
  | [], k => by
    have : (List.range k).map (sizeAt []) = (List.range k).map (fun _ => 0) :=
      List.map_congr_left fun _ _ => rfl
    rw [this]; simp
  | a :: ps, 0 => by simp
  | a :: ps, k + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, List.sum_cons]
    have h := sizeAt_range_sum_le ps k
    have : (List.map (sizeAt (a :: ps) ∘ Nat.succ) (List.range k)) = (List.range k).map (sizeAt ps) := by
      simp [Function.comp_def, sizeAt]
    rw [this]
    simp only [sizeAt, List.getD_cons_zero]
    omega

open Lean Meta Elab Tactic in
/-- Each floor application in a hypothesis, in the goal's form of it where the two are definitionally
equal: a callee's floor at inputs a branch matched apart and built back (`{ ets := Map.mk c.1.1, … }`)
and at the inputs themselves are one quantity, of which `omega` would see two. -/
def alignFloorAtoms : TacticM Unit := withMainContext do
  let isFloor (e : Expr) : Bool := match e.getAppFn.constName? with
    | some (.str _ "floor") => true
    | _ => false
  -- Only those outside binders: under one, an application mentions the bound variable.
  let tgt ← instantiateMVars (← getMainTarget)
  let tgts := Id.run do
      let mut out : Array Expr := #[]
      let mut todo : List Expr := [tgt]
      while !todo.isEmpty do
        let e := todo.head!
        todo := todo.tail!
        if e.hasLooseBVars then continue
        if isFloor e then out := out.push e
        match e with
        | .app f a => todo := f :: a :: todo
        | .mdata _ b => todo := b :: todo
        | _ => pure ()
      return out
  if tgts.isEmpty then return
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless ← isProp t do continue
    let t' ← Meta.transform t (pre := fun e => do
      unless isFloor e do return .continue
      for tg in tgts do
        if e != tg && e.getAppFn == tg.getAppFn then
          if ← withNewMCtxDepth (isDefEq e tg) then return .done tg
      return .continue)
    -- A copy at the end of the context: the goal's form may mention what was introduced after `d`.
    if t' != t then
      let (_, g') ← (← g.assert (← mkFreshUserName `haligned) t' (mkFVar d.fvarId)).intro1
      g := g'
  replaceMainGoal [g]

/-- A leaf of a floor's lower bound, `W.floor ins ≤ n`: some rule that applies costs at most `n`, given
the floors of the calls the branch made and what its split drew. -/
elab "floor_close" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``LE.le 4 do throwError "floor_close: not a bound"
  let some fl := (ty.getArg! 2).getAppFn.constName? | throwError "floor_close: no floor"
  -- the split's parts add up to at most the whole
  let mut m := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``LE.le 4 && (t.getArg! 2).isAppOf ``List.sum && (t.getArg! 2).getAppArgs.back!.isFVar then
      let ps := (t.getArg! 2).getAppArgs.back!
      let pf ← m.withContext (mkAppM ``sizeAt_range_sum_le #[ps, mkNatLit 8])
      let (_, m') ← (← m.assert `hps (← m.withContext (inferType pf)) pf).intro1P
      m := m'
  -- `omega` alone; else unfold the floor, and `omega` or the rule `minFloor_le_of_exists` picks
  let closes (label : String) (tac : TSyntax `tactic) : TacticM Bool := timeIn label do
    let saved ← saveState
    try
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return true
      saved.restore; return false
    catch _ => saved.restore; return false
  let r ← Lean.Elab.Tactic.run m do
    -- the parts' sum, term by term, for `omega`
    evalTactic (← `(tactic| try simp only [List.range_succ, List.range_zero, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, List.nil_append,
      List.singleton_append, Nat.add_zero, Nat.zero_add] at $(mkIdent `hps):ident))
    if ← closes "floor_close.omega" (← `(tactic| omega)) then return
    -- A guard the branch passed (`decide (x = c) = true`), as the equation it decided, substituted:
    -- the floor's guard on it then reduces.
    evalTactic (← `(tactic| try simp only [decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.not_eq_eq_eq_not, Bool.not_true] at *))
    evalTactic (← `(tactic| try subst_vars))
    -- The floor's unfolding equation holds at any inputs, where its equation lemmas need each input
    -- in the form of some rule's pattern; the rules' matches that the inputs decide are then reduced.
    timeIn "floor_close.unfold" (evalTactic (← `(tactic|
      first
        | (unfold $(mkIdent fl):ident; try dsimp only; try simp only [↓reduceIte])
        | simp only [$(mkIdent fl):ident]
        | skip)))
    timeIn "floor_close.align" alignFloorAtoms
    -- The guards the branch refuted (`¬ x = y`): the floor's guard on each reduces.
    withMainContext do
      let mut ids : Array Term := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if t.isAppOfArity ``Not 1 && t.appArg!.isAppOfArity ``Eq 3 then ids := ids.push (← Term.exprToSyntax (mkFVar d.fvarId))
      unless ids.isEmpty do
        evalTactic (← `(tactic| try simp only [$[$ids:term],*, ↓reduceIte, if_false] at ⊢))
    if ← closes "floor_close.omega2" (← `(tactic| omega)) then return
    -- One rule's cost, a literal `some c`, at most the size: the others, even unreduced, need not be.
    let tgt ← whnfR (← instantiateMVars (← getMainTarget))
    if tgt.isAppOfArity ``LE.le 4 then
      let lhs := tgt.getArg! 2
      if lhs.isAppOfArity ``minFloor 1 then
        if let some (_, elems) := lhs.appArg!.listLit? then
          for e in elems do
            unless e.isAppOfArity ``Option.some 2 do continue
            let c ← Term.exprToSyntax e.appArg!
            if ← closes "floor_close.pick" (← `(tactic|
                -- Its obligations as goals, not nested `by` blocks: in a proof elaborated in
                -- parallel, a nested block is a task of its own, whose failure this would not see.
                (refine Nat.le_trans (minFloor_le (c := $c) ?_) ?_
                 all_goals first | (simp; done) | omega))) then return
    let g ← getMainGoal
    try timeIn "floor_close.exists" (evalTactic (← `(tactic| (
      apply minFloor_le_of_exists
      simp only [List.mem_cons, List.mem_nil_iff, or_false, reduceCtorEq, false_or,
        Option.some.injEq, exists_eq_or_imp, exists_eq_left, exists_false, List.range_succ,
        List.range_zero, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, List.nil_append, List.singleton_append] at *
      omega))))
    catch e =>
      -- The goal and the leaf's own hypotheses: the induction hypotheses and callee laws (`∀ …`)
      -- would fill the log.
      let shown ← g.withContext do
        let mut out := ""
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          if (← instantiateMVars d.type).isForall then continue
          out := out ++ s!"{d.userName} : {← Meta.ppExpr d.type}\n"
        return out ++ s!"⊢ {← Meta.ppExpr (← g.getType)}"
      timerLog s!"  floor_close FAILED:\n{shown.take 6000}"
      throw e
  replaceMainGoal r

end Specimen.Correctness

/-! ## A split that meets every call's need -/

namespace Specimen.Correctness

open Specimen.SizeSplit

theorem fill_sum : ∀ (ps : List Nat) (r : Nat), ps ≠ [] → (fill ps r).sum = ps.sum + r
  | [], _, h => absurd rfl h
  | [p], r, _ => by simp [fill]
  | p :: q :: ps, r, _ => by
    simp only [fill, List.sum_cons]
    have := fill_sum (q :: ps) r (by simp)
    simp only [List.sum_cons] at this
    omega

theorem fill_ge : ∀ (ps : List Nat) (r : Nat), List.Forall₂ (· ≤ ·) ps (fill ps r)
  | [], _ => .nil
  | [p], r => .cons (Nat.le_add_right _ _) .nil
  | p :: q :: ps, r => .cons (Nat.le_refl _) (fill_ge (q :: ps) r)

theorem forall₂_le_trans : ∀ {as bs cs : List Nat}, List.Forall₂ (· ≤ ·) as bs →
    List.Forall₂ (· ≤ ·) bs cs → List.Forall₂ (· ≤ ·) as cs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => .cons (Nat.le_trans h₁ h₂) (forall₂_le_trans t₁ t₂)

theorem forall₂_le_max_left : ∀ (fs ts : List Nat), fs.length = ts.length →
    List.Forall₂ (· ≤ ·) fs (List.zipWith max fs ts)
  | [], [], _ => .nil
  | f :: fs, t :: ts, h => .cons (Nat.le_max_left _ _) (forall₂_le_max_left fs ts (by simpa using h))

theorem zipWith_ne_nil {fs ts : List Nat} (hf : fs ≠ []) (h : fs.length = ts.length) :
    List.zipWith max fs ts ≠ [] := by
  cases fs with
  | nil => exact absurd rfl hf
  | cons f fs => cases ts with
    | nil => simp at h
    | cons t ts => simp

/-- **The split can give every call its floor and its need.** -/
theorem produces_draw_fill {fs ts : List Nat} {s : Nat} (hf : fs ≠ []) (hl : fs.length = ts.length)
    (hs : (List.zipWith max fs ts).sum ≤ s) :
    Produces (draw fs s : SGen (List Nat)) (fillParts fs ts s) := by
  refine produces_draw (forall₂_le_trans (forall₂_le_max_left fs ts hl) (fill_ge _ _)) ?_
  rw [fillParts, fill_sum _ _ (zipWith_ne_nil hf hl)]
  omega

theorem le_getD_fill : ∀ (ps : List Nat) (r i : Nat), ps.getD i 0 ≤ (fill ps r).getD i 0
  | [], _, _ => by simp [fill]
  | [p], r, 0 => by simp [fill]
  | [p], r, i + 1 => by simp [fill]
  | p :: q :: ps, r, 0 => by simp [fill]
  | p :: q :: ps, r, i + 1 => by simpa [fill] using le_getD_fill (q :: ps) r i

theorem le_getD_zipWith_max : ∀ (fs ts : List Nat) (i : Nat), fs.length = ts.length →
    ts.getD i 0 ≤ (List.zipWith max fs ts).getD i 0
  | [], [], _, _ => by simp
  | f :: fs, t :: ts, 0, _ => by simp
  | f :: fs, t :: ts, i + 1, h => by simpa using le_getD_zipWith_max fs ts i (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- Each call gets at least its need. -/
theorem le_sizeAt_fillParts {fs ts : List Nat} {s : Nat} (i : Nat) (hl : fs.length = ts.length) :
    ts.getD i 0 ≤ sizeAt (fillParts fs ts s) i :=
  Nat.le_trans (le_getD_zipWith_max fs ts i hl) (le_getD_fill _ _ i)

end Specimen.Correctness
