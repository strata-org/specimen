import Specimen.Correctness.GenInterpSPMF
import Specimen.WorkerRegistry
import Specimen.Correctness.SuccObs
import Specimen.Enum.Search
import Specimen.Enum.Laws.Search

/-!
# A search's `yes` is found by the generator

`SearchFinds x g`: whenever the search `x` answers a continuation `yes`, the generator `g` (the same
derived code, read at `SGen`) produces a value the continuation answers `yes` of. It is what a checker
that searches for a witness (`Specimen.CheckerSearch`) needs of its enumerator to be sound: with the
enumerator's soundness at `SGen`, a `yes` gives a witness of the premise.

Unlike `SearchesAs`, it needs no definedness: a search that has not finished answers `undef`, never
`yes`. It is a `GenRel` with rules for `fail`, `failWith`, `backtrack` and `pick`, so `walk` proves it
of a derived enumerator, by induction on its fuel.
-/

open Lean.Order Basalt Specimen

namespace Specimen.Correctness

variable {α β : Type}

/-- Every `yes` of the search is a value the generator produces. -/
def SearchFinds (x : Search α) (g : SGen α) : Prop :=
  ∀ k, x.run k = .yes → ∃ a, Produces g a ∧ k a = .yes

namespace Verdict'

theorem orElse_yes {a : Verdict} {b : Unit → Verdict} (h : Verdict.orElse a b = .yes) :
    a = .yes ∨ b () = .yes := by
  cases a <;> simp only [Verdict.orElse] at h
  · revert h; cases b () <;> simp
  · exact .inl rfl
  · exact .inr h
  · revert h; cases b () <;> simp

theorem any_yes : ∀ {l : List (Unit → Verdict)}, Verdict.any l = .yes → ∃ t ∈ l, t () = .yes
  | [], h => by cases h
  | t :: ts, h => by
    rcases orElse_yes h with h | h
    · exact ⟨t, List.mem_cons_self, h⟩
    · obtain ⟨t', ht', h'⟩ := any_yes h
      exact ⟨t', List.mem_cons_of_mem _ ht', h'⟩

/-- In the flat order, `yes` is below only `yes`. -/
theorem eq_yes_of_le {v : Verdict} (h : (Verdict.yes : Verdict) ⊑ v) : v = .yes := by
  rcases Verdict.eq_undef_or_eq h with h | h
  · cases h
  · exact h.symm

end Verdict'

namespace SearchFinds

theorem pure (a : α) : SearchFinds (Pure.pure a : Search α) (Pure.pure a : SGen α) :=
  fun _ h => ⟨a, produces_pure_iff.mpr rfl, h⟩

theorem bind {x : Search α} {g : SGen α} {k : α → Search β} {k' : α → SGen β}
    (hk : ∀ a, SearchFinds (k a) (k' a)) (hx : SearchFinds x g) :
    SearchFinds (x >>= k) (g >>= k') := fun c h => by
  obtain ⟨a, ha, h⟩ := hx (fun a => (k a).run c) h
  obtain ⟨b, hb, h⟩ := hk a c h
  exact ⟨b, produces_bind_of ha hb, h⟩

theorem map {x : Search α} {g : SGen α} (f : α → β) (hx : SearchFinds x g) :
    SearchFinds (f <$> x) (f <$> g) := by
  have e : (f <$> g : SGen β) = g >>= fun a => Pure.pure (f a) := by
    rw [← bind_pure_comp]
  rw [e]
  exact bind (k := fun a => Pure.pure (f a)) (fun a => pure (f a)) hx

theorem default (g : SGen α) : SearchFinds (Inhabited.default : Search α) g :=
  fun _ h => by cases h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    SearchFinds (RandomChoice.choose lo hi h : Search _) (RandomChoice.choose lo hi h : SGen _) :=
  fun k hk => by
    obtain ⟨t, ht, hy⟩ := Verdict'.any_yes hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨_, produces_choose lo hi h _, hy⟩

/-- The supremum of a chain of searches is below the pointwise supremum, which in a flat order is a
value of the chain: so a `yes` of the supremum is a `yes` of one of them. -/
theorem admissible (g : SGen α) : admissible fun x : Search α => SearchFinds x g := by
  intro c hc hall k hk
  -- the pointwise supremum is an upper bound, so the supremum is below it
  let hc' := Search.chain_underlying hc
  let U : Search α := ⟨CCPO.csup hc', Search.csup_monotone hc' (by rintro _ ⟨s, _, rfl⟩; exact s.2)⟩
  have hle : CCPO.csup hc ⊑ U := csup_le hc fun s hs => le_csup hc' ⟨s, hs, rfl⟩
  have hU : (CCPO.csup hc') k = Verdict.yes := by
    have := hle k
    rw [show (CCPO.csup hc).run k = (CCPO.csup hc).1 k from rfl] at hk
    rw [hk] at this
    exact Verdict'.eq_yes_of_le this
  rw [← fun_csup_eq _ hc'] at hU
  unfold fun_csup at hU
  -- at the flat order of verdicts, a supremum that is `yes` is a value of the chain
  have hchain : chain (fun y : Verdict => ∃ f, Search.underlying c f ∧ f k = y) := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
    rcases hc' f f' hf hf' with h | h
    · exact .inl (h k)
    · exact .inr (h k)
  have hmem : ∃ f, Search.underlying c f ∧ f k = .yes := by
    have hU' : flat_csup (b := Verdict.undef) (fun y : Verdict => ∃ f, Search.underlying c f ∧ f k = y)
        = Verdict.yes := by
      rw [flat_csup_eq _ hchain]; exact hU
    unfold flat_csup at hU'
    split at hU'
    · rename_i hex
      obtain ⟨hcx, _⟩ := Classical.choose_spec hex
      exact (by rw [hU'] at hcx; exact hcx)
    · cases hU'
  obtain ⟨f, ⟨s, hs, rfl⟩, hsk⟩ := hmem
  exact hall s hs k hsk

theorem fail : SearchFinds (Fail.fail : Search α) (Fail.fail : SGen α) := fun _ h => by cases h

theorem failWith (e : Exhaustion) :
    SearchFinds (FailWith.failWith e : Search α) (FailWith.failWith e : SGen α) := fun _ h => by cases h

theorem seq {f : Search (α → β)} {f' : SGen (α → β)} {x : Search α} {g : SGen α}
    (hf : SearchFinds f f') (hx : SearchFinds x g) : SearchFinds (f <*> x) (f' <*> g) := by
  have e₁ : (f <*> x : Search β) = f >>= fun h => h <$> x := rfl
  have e₂ : (f' <*> g : SGen β) = f' >>= fun h => h <$> g := by rw [seq_eq_bind_map]
  rw [e₁, e₂]
  exact bind (fun h => map h hx) hf

end SearchFinds

@[walk_rel]
theorem genRel_searchFinds : GenRel Search SGen @SearchFinds where
  pure := SearchFinds.pure
  bind := SearchFinds.bind
  map := SearchFinds.map
  default := SearchFinds.default
  choose := SearchFinds.choose
  admissible := SearchFinds.admissible

attribute [gen_rule] SearchFinds.fail SearchFinds.failWith SearchFinds.seq

namespace SearchFinds

theorem branches_yes {gs : List (Nat × (Unit → Search α))} {k : α → Verdict}
    (h : (Search.branches gs).run k = .yes) : ∃ p ∈ gs, p.1 ≠ 0 ∧ (p.2 ()).run k = .yes := by
  obtain ⟨t, ht, hy⟩ := Verdict'.any_yes h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hp, hw⟩ := List.mem_filter.mp hp
  exact ⟨p, hp, by simpa using hw, hy⟩

/-- A branch of positive weight of the search, and its partner at the generator. -/
theorem weighted_mem {gs : List (Nat × (Unit → Search α))} {gs' : List (Nat × (Unit → SGen α))}
    (hs : GenRel.Weighted @SearchFinds gs gs') {p : Nat × (Unit → Search α)} (hp : p ∈ gs) :
    ∃ p' ∈ gs', p'.1 = p.1 ∧ SearchFinds (p.2 ()) (p'.2 ()) := by
  induction hs with
  | nil => simp at hp
  | @cons w g g' gs gs' hg _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨(w, g'), List.mem_cons_self, rfl, hg⟩
    · obtain ⟨p', hp', hw, h⟩ := ih hp
      exact ⟨p', List.mem_cons_of_mem _ hp', hw, h⟩

/-- A `yes` of the search is a `yes` of a branch of positive weight, which the generator's search
can draw. -/
@[gen_rule]
theorem backtrack {gs : List (Nat × (Unit → Search α))} {gs' : List (Nat × (Unit → SGen α))}
    (hs : GenRel.Weighted @SearchFinds gs gs') :
    SearchFinds (Backtrack.backtrack gs : Search α) (Backtrack.backtrack gs' : SGen α) := fun k h => by
  obtain ⟨p, hp, hw, hy⟩ := branches_yes h
  obtain ⟨p', hp', hw', hf⟩ := weighted_mem hs hp
  obtain ⟨a, ha, hka⟩ := hf k hy
  exact ⟨a, produces_backtrack_of_branch _ p' hp' (by omega) a ha, hka⟩

/-- The draw: a `yes` of a branch of positive weight, which one draw can take. -/
@[gen_rule]
theorem pick {gs : List (Nat × (Unit → Search α))} {gs' : List (Nat × (Unit → SGen α))}
    (hs : GenRel.Weighted @SearchFinds gs gs') {h : 0 < Backtrack.sumWeights gs}
    {h' : 0 < Backtrack.sumWeights gs'} :
    SearchFinds (Pick.pick gs h : Search α) (Pick.pick gs' h' : SGen α) := fun k hk => by
  obtain ⟨p, hp, hw, hy⟩ := branches_yes hk
  obtain ⟨p', hp', hw', hf⟩ := weighted_mem hs hp
  obtain ⟨a, ha, hka⟩ := hf k hy
  exact ⟨a, Specimen.Backtrack.mem_support_searchWith_ok_of_branch 1 gs' none p' hp' (by omega)
    Nat.one_pos a ha, hka⟩

end SearchFinds


/-! ## What a checker's search for a witness establishes -/

theorem toCheck_ok_true {v : Verdict} (h : v.toCheck = .ok true) : v = .yes := by
  cases v <;> first | rfl | cases h

theorem ofCheck_yes {r : Except Plausible.GenError Bool} (h : Verdict.ofCheck r = .yes) : r = .ok true := by
  unfold Verdict.ofCheck at h; split at h <;> first | rfl | cases h

/-- A search that accepted found a value its generator produces, and so, by the generator's
soundness, a witness of the premise, of which the continuation accepted. -/
theorem search_accepts {x : Search α} {g : SGen α} {P : α → Prop} (hf : SearchFinds x g)
    (hs : succObs.spec g P) {k : α → Except Plausible.GenError Bool}
    (h : (x.run (Verdict.ofCheck ∘ k)).toCheck = .ok true) : ∃ a, P a ∧ k a = .ok true := by
  obtain ⟨a, ha, hk⟩ := hf _ (toCheck_ok_true h)
  exact ⟨a, hs a ha, ofCheck_yes hk⟩


/-! ## Unconstrained draws -/

open Lean Meta Elab Tactic in
/-- Unfold each `ArbitrarySized.arbitrarySized` to its instance's body, so that `walk` relates an
unconstrained draw at the two readings by the combinators it is built from; and each derived
enumerator's `EnumFor.enum` to the worker it calls, which the callee's `searchFinds` is about. -/
def unfoldArbitrary (all : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ty' ← Meta.transform ty (pre := fun e => do
    if e.isAppOf ``Basalt.ArbitrarySized.arbitrarySized then
      match ← unfoldProjInst? e with
      | some e' =>
        let e' := e'.headBeta
        -- a derived instance whose generator is recursive keeps its class form, which its laws
        -- (`ArbitrarySizedSearch`, `ArbitrarySizedHits`) are about: its body would be a call of the
        -- recursive generator, which nothing relates (`all`, for those laws' own proofs, unfolds it)
        if !all then
          if let some c := e'.getAppFn.constName? then
            let env ← getEnv
            if (Lean.Elab.Structural.eqnInfoExt.find? env c).isSome ||
                (Lean.Elab.WF.eqnInfoExt.find? env c).isSome then
              return .continue
        return .visit e'
      | none => return .continue
    -- a derived enumerator's instance, to the worker it calls, which a fact is about
    if e.isAppOf ``EnumFor.enum then
      match ← unfoldProjInst? e with
      | some e' =>
        let e' := e'.headBeta
        if let some n := e'.getAppFn.constName? then
          if Specimen.isDerivedWorker (← getEnv) n [.Enumerator] then return .visit e'
        -- an equation's enumerator, `pure` of its one solution (or a draw, for a pair), to its body
        if let some i := (e.getArg! 2).getAppFn.constName? then
          if [`instEnumForEqRight, `instEnumForEqLeft, `instEnumForEqPair, `instEnumForNatGe,
              `instEnumForNatGt, `instEnumForNatLe, `instEnumForNatLt].contains i then
            return .visit e'
        return .continue
      | none => return .continue
    return .continue)
  if ty' == ty then throwError "unfold_arbitrary: nothing to unfold"
  replaceMainGoal [← goal.replaceTargetDefEq ty']

open Lean Elab Tactic in
/-- Unfold each `ArbitrarySized.arbitrarySized` to its instance's body (see `unfoldArbitrary`), a
derived recursive generator's kept in its class form for its laws. -/
elab "unfold_arbitrary" : tactic => unfoldArbitrary false

open Lean Elab Tactic in
/-- `unfold_arbitrary`, a derived recursive generator's unfolded too: for the proofs of its own laws
(`arbitrary_complete`, `arbitrary_search_derived`, `arbitrary_hits_derived`). -/
elab "unfold_arbitrary_all" : tactic => unfoldArbitrary true


/-- An unconstrained draw's search finds only what the draw produces. A derived enumerator over a
relation with type parameters draws its parameters' values through instances it is given, and needs
this of them; each instance has it by `walk` over its body. -/
class ArbitrarySizedSearch (α : Type) [Basalt.ArbitrarySized α] : Prop where
  searchFinds : ∀ n, SearchFinds (Basalt.ArbitrarySized.arbitrarySized (G := Search) n : Search α)
    (Basalt.ArbitrarySized.arbitrarySized (G := SGen) n : SGen α)

attribute [gen_rule] ArbitrarySizedSearch.searchFinds

/-- The law of an instance whose body `walk` relates: by its combinators and its components' laws. -/
macro "arbitrary_search" : tactic => `(tactic| (intro n; unfold_arbitrary; walk))

instance : ArbitrarySizedSearch Nat := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Bool := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Unit := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Int := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Char := ⟨by arbitrary_search⟩
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedSearch α] : ArbitrarySizedSearch (Option α) :=
  ⟨by arbitrary_search⟩
instance {α β : Type} [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [ArbitrarySizedSearch α]
    [ArbitrarySizedSearch β] : ArbitrarySizedSearch (α × β) := ⟨by arbitrary_search⟩
instance {α β : Type} [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [ArbitrarySizedSearch α]
    [ArbitrarySizedSearch β] : ArbitrarySizedSearch (α ⊕ β) := ⟨by arbitrary_search⟩
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedSearch α] : ArbitrarySizedSearch (List α) :=
  ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch String := ⟨by arbitrary_search⟩

/-- A checker's search over the unconstrained values of `α` (`CheckerSearchAll`, for a premise's
witness its inputs do not fix) accepts only when the rest of the check accepts one of them. Read by
`check_hyps` in a checker's soundness. -/
theorem checkerSearchAll_accepts {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedSearch α]
    {l : Nat} {k : α → Except Plausible.GenError Bool}
    (h : Specimen.CheckerSearchAll.search (α := α) l k = .ok true) : ∃ a, True ∧ k a = .ok true :=
  search_accepts (ArbitrarySizedSearch.searchFinds l) (P := fun _ => True)
    (succObs_iff.mpr fun _ _ => trivial) h

end Specimen.Correctness
