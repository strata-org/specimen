import Specimen.Correctness.SizeMeasure
import Specimen.WorkerRegistry
import Basalt.Walk.Sound
import Basalt.Walk.Entry

/-!
# Teaching Basalt's walk the sampler's combinators

A derived generator read at `SGen` is an `SPMF` of outcomes: a success, a refutation (`none`) or a
labelled failure. Basalt's `walk` already goes through its binds, the transformer layers and its
`match`es; what it does not know are Specimen's own combinators. These rules teach it the soundness
observation (`SPMF.alwaysObs`) of each:

* `backtrack` over a branch list, literal or as the emitter writes it, `filterMap` of guarded options;
* the failures `Fail.fail`, `FailWith.failWith` and `truncations`.

A soundness goal about a derived generator is then `walk`, with one goal per path left over.
-/

open Basalt Basalt.Walk

namespace Specimen.Correctness

variable {α : Type}

/-- An outcome that is not a success. -/
def IsFailure (o : Option (Except Exhaustion α)) : Prop := ∀ x, o ≠ some (.ok x)

/-- A guarded branch as a generator: the branch's body, or a refutation where the guard dropped it. -/
noncomputable def optGen : Option (Nat × (Unit → SGen α)) → SGen α
  | some q => q.2 ()
  | none => Specimen.refute

theorem mem_filterMap_id {os : List (Option β)} {q : β} :
    q ∈ os.filterMap (fun o => o) ↔ some q ∈ os := by
  simp [List.mem_filterMap]

/-- What `backtrack` can return: a failure, or a success of one of its branches. -/
theorem always_backtrack_of {gs : List (Nat × (Unit → SGen α))}
    {post : Option (Except Exhaustion α) → Prop}
    (hfail : ∀ o, IsFailure o → post o) (hbr : ∀ p ∈ gs, SPMF.alwaysObs.spec (p.2 ()).run.run post) :
    SPMF.alwaysObs.spec (Specimen.Backtrack.backtrack gs : SGen α) post := by
  intro o ho
  by_cases hf : IsFailure o
  · exact hfail o hf
  · simp only [IsFailure, not_forall, not_not] at hf
    obtain ⟨x, rfl⟩ := hf
    obtain ⟨p, hp, -, hx⟩ := produces_backtrack_ok gs x ho
    exact hbr p hp _ hx

theorem forall_of_forall₂ {cs : List Prop} {l : List β} {F : β → Prop}
    (h : List.Forall₂ (fun c g => c ≤ F g) cs l) (hcs : cs.foldr And True) : ∀ g ∈ l, F g := by
  induction h with
  | nil => simp
  | cons hc _ ih => exact List.forall_mem_cons.mpr ⟨hc hcs.1, ih hcs.2⟩

/-- `backtrack` over the emitter's branch list, `filterMap` of guarded options: walked one option at a
time, each as `optGen`. -/
@[gen_rule]
theorem le_always_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen α)))}
    {post : Option (Except Exhaustion α) → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c o => c ≤ SPMF.alwaysObs.spec (optGen o : SGen α) post) cs os) :
    ((∀ o, IsFailure o → post o) ∧ cs.foldr And True) ≤
      SPMF.alwaysObs.spec
        (Specimen.Backtrack.backtrack (os.filterMap (fun o => o)) : SGen α) post := by
  rintro ⟨hfail, hcs⟩
  refine always_backtrack_of hfail fun p hp => ?_
  exact forall_of_forall₂ h hcs (some p) (mem_filterMap_id.mp hp)

/-- `backtrack` over a literal branch list: every branch, and every failure. -/
@[gen_rule]
theorem le_always_backtrack {gs : List (Nat × (Unit → SGen α))}
    {post : Option (Except Exhaustion α) → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c p => c ≤ SPMF.alwaysObs.spec (p.2 () : SGen α) post) cs gs) :
    ((∀ o, IsFailure o → post o) ∧ cs.foldr And True) ≤
      SPMF.alwaysObs.spec (Specimen.Backtrack.backtrack gs : SGen α) post :=
  fun ⟨hfail, hcs⟩ => always_backtrack_of hfail (forall_of_forall₂ h hcs)

theorem support_refute {o : Option (Except Exhaustion α)}
    (ho : o ∈ (Specimen.refute : SGen α).run.run.support) : o = none := by
  simpa [Specimen.refute, Fail.fail, ExceptT.lift, OptionT.run_failure,
    SPMF.mem_support_pure_iff] using ho

theorem support_failWith {e : Exhaustion} {o : Option (Except Exhaustion α)}
    (ho : o ∈ (FailWith.failWith e : SGen α).run.run.support) : o = some (.error e) := by
  simpa [FailWith.failWith, OptionT.run_pure, SPMF.mem_support_pure_iff] using ho

@[gen_rule]
theorem le_always_optGen_some {q : Nat × (Unit → SGen α)}
    {post : Option (Except Exhaustion α) → Prop} {c : Prop}
    (h : c ≤ SPMF.alwaysObs.spec (q.2 () : SGen α) post) :
    c ≤ SPMF.alwaysObs.spec (optGen (some q) : SGen α) post := h

/-- A dropped branch refutes; the failure premise of the enclosing `backtrack` covers it. -/
@[gen_rule]
theorem le_always_optGen_ite {b : Prop} [Decidable b] {q : Nat × (Unit → SGen α)}
    {post : Option (Except Exhaustion α) → Prop} {c : Prop}
    (h : b → c ≤ SPMF.alwaysObs.spec (q.2 () : SGen α) post) :
    ((b → c) ∧ post none) ≤ SPMF.alwaysObs.spec (optGen (if b then some q else none) : SGen α) post := by
  rintro ⟨hc, hnone⟩
  by_cases hb : b
  · simp only [hb, ite_true, optGen]; exact h hb (hc hb)
  · simp only [hb, ite_false, optGen]
    intro o ho
    exact (support_refute (α := α) ho) ▸ hnone

/-! ## Failures -/

@[gen_rule]
theorem le_always_fail {post : Option (Except Exhaustion α) → Prop} :
    post none ≤ SPMF.alwaysObs.spec (Specimen.Fail.fail : SGen α) post :=
  fun h o ho => (support_refute ho) ▸ h

@[gen_rule]
theorem le_always_failWith {e : Exhaustion} {post : Option (Except Exhaustion α) → Prop} :
    post (some (.error e)) ≤
      SPMF.alwaysObs.spec (Specimen.FailWith.failWith e : SGen α) post := by
  intro h o ho
  exact (support_failWith (α := α) ho) ▸ h

@[gen_rule]
theorem le_always_truncations {ls : List (Specimen.Label α)}
    {post : Option (Except Exhaustion α) → Prop} :
    (∀ o, IsFailure o → post o) ≤
      SPMF.alwaysObs.spec (Specimen.truncations ls : SGen α) post := by
  intro h
  unfold Specimen.truncations
  split
  · exact le_always_fail (h none fun x hx => nomatch hx)
  · exact le_always_failWith (h _ fun x hx => nomatch hx)

/-! ## The step obligations, on observations

Specimen's obligations about a step, restated on Basalt's observations so that `walk` discharges them:
the previous level's law is a fact, and the walk leaves one goal per path of the step. -/

/-- The soundness postcondition: a success is related to the input. -/
abbrev SoundPost {I A : Type} (P : I → A → Prop) (i : I) : Option (Except Exhaustion A) → Prop :=
  fun o => ∀ x, o = some (.ok x) → P i x

theorem stepGenSoundB_of_obs {I A : Type} {step : SGenStep I A} {P : I → A → Prop}
    (h : ∀ prev : Nat → I → SGen A, (∀ sz i, SPMF.alwaysObs.spec (prev sz i) (SoundPost P i)) →
      ∀ sz i, SPMF.alwaysObs.spec (step prev sz i) (SoundPost P i)) :
    StepGenSoundB step P :=
  fun prev hprev sz i x hx =>
    h prev (fun sz' i' o ho x' hx' => by subst hx'; exact hprev sz' i' x' ho) sz i _ hx x rfl

/-! ## Completeness: the may observation

`backtrack` can return a success of any branch of positive weight, so its may observation holds where
some live branch's does, at a postcondition that only successes satisfy. -/

/-- Some branch of positive weight has its bound. -/
def AnyLive {β : Type} : List (Nat × β) → List Prop → Prop
  | p :: gs, c :: cs => (0 < p.1 ∧ c) ∨ AnyLive gs cs
  | _, _ => False

/-- Some guard holds, its branch has positive weight, and it has its bound. -/
def AnyLiveOpt {β : Type} : List (Option (Nat × β)) → List Prop → Prop
  | o :: os, c :: cs => (∃ q, o = some q ∧ 0 < q.1 ∧ c) ∨ AnyLiveOpt os cs
  | _, _ => False

/-- Only successes satisfy `post`. -/
def OkOnly (post : Option (Except Exhaustion α) → Prop) : Prop := ∀ o, post o → ∃ x, o = some (.ok x)

theorem may_backtrack_of {gs : List (Nat × (Unit → SGen α))}
    {post : Option (Except Exhaustion α) → Prop} (hok : OkOnly post)
    {p : Nat × (Unit → SGen α)} (hp : p ∈ gs) (hw : 0 < p.1)
    (h : SPMF.mayObs.spec (p.2 () : SGen α) post) :
    SPMF.mayObs.spec (Specimen.Backtrack.backtrack gs : SGen α) post := by
  obtain ⟨o, ho, hpo⟩ := h
  obtain ⟨x, rfl⟩ := hok o hpo
  exact ⟨_, (produces_backtrack_iff gs x).mpr ⟨p, hp, hw, ho⟩, hpo⟩

theorem anyLive_elim {β : Type} {gs : List (Nat × β)} {cs : List Prop} {F : β → Prop}
    (h : List.Forall₂ (fun c p => c ≤ F p.2) cs gs) (hl : AnyLive gs cs) :
    ∃ p ∈ gs, 0 < p.1 ∧ F p.2 := by
  induction h with
  | nil => exact hl.elim
  | cons hc _ ih =>
    rcases hl with ⟨hw, hcx⟩ | hl
    · exact ⟨_, List.mem_cons_self, hw, hc hcx⟩
    · obtain ⟨p, hp, hw, hF⟩ := ih hl
      exact ⟨p, List.mem_cons_of_mem _ hp, hw, hF⟩

theorem anyLiveOpt_elim {β : Type} {os : List (Option (Nat × β))} {cs : List Prop} {F : β → Prop}
    (h : List.Forall₂ (fun c o => ∀ q, o = some q → c ≤ F q.2) cs os) (hl : AnyLiveOpt os cs) :
    ∃ q, some q ∈ os ∧ 0 < q.1 ∧ F q.2 := by
  induction h with
  | nil => exact hl.elim
  | cons hc _ ih =>
    rcases hl with ⟨q, rfl, hw, hcx⟩ | hl
    · exact ⟨q, List.mem_cons_self, hw, hc q rfl hcx⟩
    · obtain ⟨q, hq, hw, hF⟩ := ih hl
      exact ⟨q, List.mem_cons_of_mem _ hq, hw, hF⟩

@[gen_rule]
theorem le_may_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen α)))}
    {post : Option (Except Exhaustion α) → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c o => c ≤ SPMF.mayObs.spec (optGen o : SGen α) post) cs os) :
    (OkOnly post ∧ AnyLiveOpt os cs) ≤
      SPMF.mayObs.spec
        (Specimen.Backtrack.backtrack (os.filterMap (fun o => o)) : SGen α) post := by
  rintro ⟨hok, hl⟩
  have h' : List.Forall₂ (fun c o => ∀ q, o = some q →
      c ≤ (fun g : Unit → SGen α => SPMF.mayObs.spec (g () : SGen α) post) q.2) cs os :=
    h.imp fun {c o} hc q hq => by subst hq; exact hc
  obtain ⟨q, hq, hw, hF⟩ :=
    anyLiveOpt_elim (F := fun g : Unit → SGen α => SPMF.mayObs.spec (g () : SGen α) post) h' hl
  exact may_backtrack_of hok (mem_filterMap_id.mpr hq) hw hF

@[gen_rule]
theorem le_may_backtrack {gs : List (Nat × (Unit → SGen α))}
    {post : Option (Except Exhaustion α) → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c p => c ≤ SPMF.mayObs.spec (p.2 () : SGen α) post) cs gs) :
    (OkOnly post ∧ AnyLive gs cs) ≤
      SPMF.mayObs.spec (Specimen.Backtrack.backtrack gs : SGen α) post := by
  rintro ⟨hok, hl⟩
  obtain ⟨p, hp, hw, hF⟩ := anyLive_elim (F := fun g => SPMF.mayObs.spec (g () : SGen α) post) h hl
  exact may_backtrack_of hok hp hw hF

@[gen_rule]
theorem le_may_optGen_some {q : Nat × (Unit → SGen α)}
    {post : Option (Except Exhaustion α) → Prop} {c : Prop}
    (h : c ≤ SPMF.mayObs.spec (q.2 () : SGen α) post) :
    c ≤ SPMF.mayObs.spec (optGen (some q) : SGen α) post := h

@[gen_rule]
theorem le_may_optGen_ite {b : Prop} [Decidable b] {q : Nat × (Unit → SGen α)}
    {post : Option (Except Exhaustion α) → Prop} {c : Prop}
    (h : b → c ≤ SPMF.mayObs.spec (q.2 () : SGen α) post) :
    (b ∧ c) ≤ SPMF.mayObs.spec (optGen (if b then some q else none) : SGen α) post := by
  rintro ⟨hb, hc⟩
  simp only [hb, ite_true, optGen]; exact h hb hc

@[gen_rule]
theorem le_may_fail {post : Option (Except Exhaustion α) → Prop} :
    False ≤ SPMF.mayObs.spec (Specimen.Fail.fail : SGen α) post := False.elim

@[gen_rule]
theorem le_may_failWith {e : Exhaustion} {post : Option (Except Exhaustion α) → Prop} :
    False ≤ SPMF.mayObs.spec (Specimen.FailWith.failWith e : SGen α) post := False.elim

@[gen_rule]
theorem le_may_truncations {ls : List (Specimen.Label α)}
    {post : Option (Except Exhaustion α) → Prop} :
    False ≤ SPMF.mayObs.spec (Specimen.truncations ls : SGen α) post := False.elim

/-- Specimen's size-measured completeness obligation, on the may observation. -/
theorem stepGenCompleteS_of_obs {I A : Type} {step : SGenStep I A} {P : I → A → Prop}
    {σ : I → A → Nat}
    (h : ∀ (prev : Nat → I → SGen A) (sz : Nat) (i : I) (a : A), P i a → σ i a ≤ sz →
      (∀ sz' < sz, ∀ j b, P j b → σ j b ≤ sz' → SPMF.mayObs.spec (prev sz' j) (· = some (.ok b))) →
      SPMF.mayObs.spec (step prev sz i) (· = some (.ok a))) :
    StepGenCompleteS step P σ := fun prev sz i a hPa hσ hrec =>
  SPMF.mem_support_iff_may.mpr (h prev sz i a hPa hσ fun sz' hlt j b hPb hσ' =>
    SPMF.mem_support_iff_may.mp (hrec sz' hlt j b hPb hσ'))

/-! ## Calls through derived instances

A derived generator calls another relation's generator through its `BacktrackGenFor` instance, whose
`gen` is that relation's worker at a fixed fuel. The walk uses a fact only when it mentions the
generator's head constant, so these calls are rewritten into the worker calls they denote. -/

open Lean Meta Elab Tactic in
/-- Rewrite the `BacktrackGenFor.gen …` calls in the goal into the workers their instances run: every
call, or with facts given, only those whose worker a fact is about (the rest keep their head, for a
fact about `BacktrackGenFor.gen` itself, such as `always_gen_true`). -/
elab "unfold_gen_instances" fs:(" [" term,* "]")? : tactic => withMainContext do
  let goal ← getMainGoal
  let heads? : Option (Std.HashSet Name) ← match fs with
    | none => pure none
    | some fs => do
      let terms := match fs with
        | `( [$ts,*]) => ts.getElems
        | _ => #[]
      let mut hs : Std.HashSet Name := {}
      for f in terms do
        let ty ← instantiateMVars (← inferType (← Term.elabTerm f none))
        for c in ty.getUsedConstants do hs := hs.insert c
      pure (some hs)
  let ty ← instantiateMVars (← goal.getType)
  let ty' ← Meta.transform ty (pre := fun e => do
    unless e.isAppOf ``BacktrackGenFor.gen || e.isAppOf ``EnumFor.enum do return .continue
    match ← unfoldProjInst? e with
    | some e' =>
      let e' := e'.headBeta
      -- Only a derived instance, whose `gen` (or `enum`) is a call to a derived worker: a hand-written
      -- one keeps its head, for a fact stated on it.
      -- A pair constrained equal (`Specimen.BasaltBridge`'s instance) too: its predicate is stated
      -- through a `match` on the pair, whose matcher is each file's own, so a fact about it would
      -- not unify with the calls; its body, a draw duplicated, walks as it is.
      let inst := if e.getAppNumArgs > 2 then (e.getArg! 2).getAppFn.constName? else none
      if inst == some `instBacktrackGenForEqPair || inst == some `instEnumForEqPair then return .visit e'
      let some n := e'.getAppFn.constName? | return .continue
      unless Specimen.isDerivedWorker (← getEnv) n [.Generator, .Enumerator] do
        return .continue
      match heads? with
      | some hs => if hs.contains n then return .visit e' else return .continue
      | none => return .visit e'
    | none => return .continue)
  replaceMainGoal [← goal.replaceTargetDefEq ty']

/-- Nothing is known of what a sub-generator produces: the leaf asks for its postcondition everywhere. -/
theorem always_gen_true {α : Type} (P : α → Prop) [BacktrackGenFor α P] (s l : Nat) :
    SPMF.alwaysObs.spec (BacktrackGenFor.gen (P := P) (G := SGen) s l) (fun _ => True) :=
  fun _ _ => trivial

theorem always_true {α : Type} (g : SGen α) :
    SPMF.alwaysObs.spec (g : SGen α) (fun _ => True) := fun _ _ => trivial

open Lean Meta Elab Tactic in
/-- Put into context, for every derived worker the goal calls, the fact that nothing is known of what
it produces. The walk tries a hypothesis only after the facts passed to it, so these are fallbacks: a
call whose result does not matter to the goal goes through, where otherwise the walk would stop at it
for want of a fact. (One fact about every generator would do the same, but the walk would try it on
every call.) -/
elab "add_trivial_gen_facts" : tactic => withMainContext do
  let sgen := mkConst ``Specimen.Correctness.SGen
  let env ← getEnv
  let mut goal ← getMainGoal
  for n in (← instantiateMVars (← getMainTarget)).getUsedConstants do
    unless Specimen.isDerivedWorker env n do continue
    let r ← observing? do
      let f ← mkAppOptM n #[some sgen, none, none, none, none, none, none]
      forallTelescopeReducing (← inferType f) fun xs body => do
        unless body.isAppOf ``Specimen.Correctness.SGen do failure
        let pf ← mkLambdaFVars xs (← mkAppM ``always_true #[mkAppN f xs])
        return (pf, ← inferType pf)
    let some (pf, pty) := r | continue
    let (_, g) ← (← goal.assert (← mkFreshUserName `htriv) pty pf).intro1P
    goal := g
  replaceMainGoal [goal]

open Lean Meta Elab Tactic in
/-- Clear the fallbacks `add_trivial_gen_facts` added. -/
elab "clear_trivial_gen_facts" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    let g ← g.withContext do
      let mut g := g
      for d in ← getLCtx do
        if (d.userName.toString.splitOn "htriv").length > 1 then
          g ← g.clear d.fvarId
      pure g
    out := out ++ [g]
  setGoals out

end Specimen.Correctness
