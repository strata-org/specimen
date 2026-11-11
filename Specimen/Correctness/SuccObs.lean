import Specimen.Correctness.WalkSGen
import Specimen.Correctness.LeafSPMF
import Specimen.BasaltBridge

/-!
# The success observation

A derived generator's soundness is about its successes: `∀ x, Produces g x → P x`. Read on `SGen`'s
`SPMF` run with `SPMF.alwaysObs`, every bind goes through the transformers' `bindCont`, and the walk
splits at each one on a success, a refutation and every labelled failure. Most of the paths it leaves
are a failure passed along.

`succObs` is the observation on `SGen` itself: a monad morphism into Basalt's demonic specifications
that sees only successes. Basalt's own rules for `pure`, `bind`, `map` and `if` apply to it as they are,
a refutation or a labelled failure has nothing to bound, and what is left after a walk is one goal per
path to a success.
-/

open Basalt Basalt.Walk RandomChoice

namespace Specimen.Correctness

variable {α : Type}

theorem produces_choose (lo hi : Nat) (h : lo ≤ hi) (x : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}) :
    Produces (RandomChoice.choose lo hi h : SGen _) x :=
  ReachesAll.choose lo hi h x (SPMF.mem_support_choose_iff.mpr trivial)

/-- Every success satisfies the postcondition. -/
def succObs : Obs SGen (WP Mix.demonic) where
  spec g := fun Q => ∀ x, Produces g x → Q x
  map_pure a := by
    funext Q; apply propext
    exact ⟨fun h => h a (produces_pure_iff.mpr rfl), fun h b hb => produces_pure_iff.mp hb ▸ h⟩
  map_bind x k := by
    funext Q; apply propext
    show (∀ b, Produces (x >>= k) b → Q b) ↔ ∀ a, Produces x a → ∀ b, Produces (k a) b → Q b
    simp only [produces_bind_iff]
    exact ⟨fun h a ha b hb => h b ⟨a, ha, hb⟩, fun h b ⟨a, ha, hb⟩ => h a ha b hb⟩
  map_choose lo hi h := by
    funext Q; apply propext
    exact ⟨fun hq x => hq x (produces_choose lo hi h x), fun hq a _ => hq a⟩

instance : succObs.Monotone := ⟨fun _ _ _ h hp a ha => h a (hp a ha)⟩

/-- The success observation is soundness. -/
theorem succObs_iff {g : SGen α} {P : α → Prop} : succObs.spec g P ↔ ∀ x, Produces g x → P x :=
  Iff.rfl

/-- …and soundness is Basalt's law of the run. -/
theorem succObs_isSoundFor {g : SGen α} {P : α → Prop} (h : succObs.spec g P) :
    IsSoundFor g.run.run (fun o => ∀ x, o = some (.ok x) → P x) :=
  produces_sound_iff_isSoundFor.mp h

/-- A fact about a sub-generator, used under the postcondition the walk arrives with. -/
@[obs_leaf]
theorem le_succ_of_succ {x : SGen α} {R p : α → Prop} (hx : succObs.spec x R) :
    (∀ a, R a → p a) ≤ succObs.spec x p := fun h a ha => h a (hx a ha)

/-! ## The sampler's combinators -/

theorem succ_forall_of_forall₂ {cs : List Prop} {l : List β} {F : β → Prop}
    (h : List.Forall₂ (fun c g => c ≤ F g) cs l) (hcs : cs.foldr And True) : ∀ g ∈ l, F g :=
  forall_of_forall₂ h hcs

@[gen_rule]
theorem le_succ_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen α)))}
    {post : α → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c o => c ≤ succObs.spec (optGen o) post) cs os) :
    cs.foldr And True ≤ succObs.spec (Specimen.Backtrack.backtrack (os.filterMap fun o => o)) post := by
  intro hcs x hx
  obtain ⟨p, hp, -, hx⟩ := produces_backtrack_ok _ x hx
  exact succ_forall_of_forall₂ h hcs (some p) (mem_filterMap_id.mp hp) x hx

@[gen_rule]
theorem le_succ_backtrack {gs : List (Nat × (Unit → SGen α))} {post : α → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c p => c ≤ succObs.spec (p.2 ()) post) cs gs) :
    cs.foldr And True ≤ succObs.spec (Specimen.Backtrack.backtrack gs) post := by
  intro hcs x hx
  obtain ⟨p, hp, -, hx⟩ := produces_backtrack_ok gs x hx
  exact succ_forall_of_forall₂ h hcs p hp x hx

theorem forall_mem_of_foldr_map {β : Type _} {P : β → Prop} :
    ∀ {gs : List β}, (gs.map P).foldr And True → ∀ q ∈ gs, P q
  | [], _, _, hq => absurd hq List.not_mem_nil
  | _ :: _, h, q, hq => by
    simp only [List.map_cons, List.foldr_cons] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact forall_mem_of_foldr_map h.2 q hq

/-- A backtrack is sound when each of its alternatives is: the step of a derived worker, split by
alternative (`proveBlockParallel`). -/
theorem succ_spec_backtrack_of_all {gs : List (Nat × (Unit → SGen α))} {post : α → Prop}
    (h : (gs.map fun p => succObs.spec (p.2 ()) post).foldr And True) :
    succObs.spec (Specimen.Backtrack.backtrack gs) post := by
  intro x hx
  obtain ⟨p, hp, -, hx⟩ := produces_backtrack_ok gs x hx
  exact forall_mem_of_foldr_map (P := fun p => succObs.spec (p.2 ()) post) h p hp x hx

@[gen_rule]
theorem le_succ_optGen_some {q : Nat × (Unit → SGen α)} {post : α → Prop} {c : Prop}
    (h : c ≤ succObs.spec (q.2 ()) post) : c ≤ succObs.spec (optGen (some q)) post := h

@[gen_rule]
theorem le_succ_optGen_ite {b : Prop} [Decidable b] {q : Nat × (Unit → SGen α)} {post : α → Prop}
    {c : Prop} (h : b → c ≤ succObs.spec (q.2 ()) post) :
    (b → c) ≤ succObs.spec (optGen (if b then some q else none)) post := by
  intro hc x hx
  by_cases hb : b
  · simp only [hb, ite_true, optGen] at hx; exact h hb (hc hb) x hx
  · simp only [hb, ite_false, optGen] at hx; exact absurd hx (not_produces_refute x)

@[gen_rule]
theorem le_succ_fail {post : α → Prop} : True ≤ succObs.spec (Specimen.Fail.fail : SGen α) post :=
  fun _ x hx => absurd hx (not_produces_refute x)

@[gen_rule]
theorem le_succ_failWith {e : Exhaustion} {post : α → Prop} :
    True ≤ succObs.spec (Specimen.FailWith.failWith e : SGen α) post := by
  intro _ x hx; exfalso
  simp [Produces, FailWith.failWith, OptionT.run_pure, SPMF.mem_support_pure_iff] at hx

@[gen_rule]
theorem le_succ_truncations {ls : List (Specimen.Label α)} {post : α → Prop} :
    True ≤ succObs.spec (Specimen.truncations ls : SGen α) post :=
  fun _ x hx => by simp at hx

/-- A size budget's split: whatever it is, the calls it sizes are sound at every size. -/
@[gen_rule]
theorem le_succ_drawEven {k floor total : Nat} {post : List Nat → Prop} :
    (∀ parts, post parts) ≤ succObs.spec (Specimen.SizeSplit.drawEven k floor total : SGen (List Nat)) post :=
  fun h a _ => h a

/-- The last resort, opted into with `WalkSGenSelf`'s import: an unknown generator, where the
postcondition holds of every value. -/
@[obs_leaf self]
theorem le_succ_self {x : SGen α} {p : α → Prop} : (∀ a, p a) ≤ succObs.spec x p :=
  fun h a _ => h a

/-! ## Outputs determined by an equation -/

/-- The equality instance produces the value it is given. -/
theorem succ_gen_eqRight {α : Type} (val : α) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun x => x = val) (G := SGen) s l) (· = val) :=
  fun x hx => (produces_pure_iff (a := val)).mp hx

theorem succ_gen_eqLeft {α : Type} (val : α) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun x => val = x) (G := SGen) s l) (val = ·) :=
  fun x hx => ((produces_pure_iff (a := val)).mp hx).symm

/-- An equation's enumerator, read at `SGen` as a derived enumerator's soundness proof reads it:
the one solution. -/
theorem succ_enum_eqRight {α : Type} (val : α) (s l : Nat) :
    succObs.spec (EnumFor.enum (P := fun x => x = val) (G := SGen) s l) (· = val) :=
  fun x hx => (produces_pure_iff (a := val)).mp hx

theorem succ_enum_eqLeft {α : Type} (val : α) (s l : Nat) :
    succObs.spec (EnumFor.enum (P := fun x => val = x) (G := SGen) s l) (val = ·) :=
  fun x hx => ((produces_pure_iff (a := val)).mp hx).symm


open Lean Meta in
/-- `@w SGen _ _ _ _ _ _`: a derived worker at `SGen`, its instances synthesized, its universe levels
left as metavariables for the relation it is stated against to fix. (A worker over a relation with
type parameters is universe-polymorphic in them, where the relation may not be.) -/
def workerAtSGen (wN : Name) : MetaM Expr := do
  atSGen wN (← mkConstWithFreshMVarLevels wN)
where
  atSGen (wN : Name) (c : Expr) (G : Expr := mkConst ``SGen) : MetaM Expr := do
    let mut e := mkApp c G
    for _ in [:6] do
      let .forallE _ d _ _ ← whnfD (← inferType e) | throwError "worker {wN}: expected an instance argument"
      e := mkApp e (← synthInstance d)
    return e

open Lean Meta in
/-- `@w.{us} SGen _ _ _ _ _ _` at the worker's own universe parameters `us`, and those. -/
def workerAtSGenParams (wN : Name) : MetaM (Expr × List Name) := do
  let lps := (← getConstInfo wN).levelParams
  return (← workerAtSGen.atSGen wN (mkConst wN (lps.map mkLevelParam)), lps)

end Specimen.Correctness
