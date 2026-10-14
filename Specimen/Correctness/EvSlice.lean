import Specimen.Correctness.Combinators
import Specimen.Correctness.Semantics
import Specimen.Correctness.LazyListLemmas
import Specimen.Correctness.GenAxioms
import Specimen.Correctness.Reflect
import Specimen.Correctness.CheckerInterp

/-!
# Vertical slice: evenness (`Ev`), all three producers proved correct

This is the first end-to-end correctness proof for a *concrete* inductive relation. It deliberately
uses the **real** relation `Ev` rather than a reflected copy: for a fixed relation the constructors
`Ev.z`/`Ev.ss` and the recursor `Ev.rec` are first-class, so no reflection is needed yet.

The slice's purpose is to (a) validate the `Semantics` targets and the combinator lemmas on real
producers, and (b) pinpoint the *only* two places that a generic proof cannot reach without
reflection, so the later `RelSpec`/`Provable` layer knows exactly what to generalize:

* **soundness** ends by *applying a constructor* (`exact Ev.z` / `exact Ev.ss …`)  ⟶ `Provable.intro`;
* **completeness** proceeds by *induction on the derivation* (`induction h`)          ⟶ induction on `Provable`.

Everything else — the combinator reasoning, the fuel recursion — is already relation-independent.

The file proves, in order: the checker sound, complete and monotone (directly, then again through the
generic checker interpreter); the enumerator sound and complete, over a `List` core reached through
`fromList`; the generator sound and complete at the real `Plausible.Gen`, which uses `GenAxioms`; and
`Ev` as a `RelSpec`, with the adequacy proof that its `Provable` is `Ev`.
-/

open Plausible DecOpt Specimen.Correctness

namespace Specimen.Correctness.EvSlice

/-- The evenness relation — our concrete example inductive relation. -/
inductive Ev : Nat → Prop
  | z : Ev 0
  | ss {n : Nat} : Ev n → Ev (n + 2)

/-! ### Checker

`decEvAux` is built from `checkerBacktrack` exactly as specimen emits a `DecOpt` instance: one
thunked sub-checker per constructor, recursion guarded by fuel.
* constructor `z` concludes `Ev 0`      → the sub-checker verifies `n = 0`;
* constructor `ss` concludes `Ev (m+2)` from `Ev m` → match `n = m+2`, then check `Ev m` recursively.
-/

/-- Fuel-driven checker for `Ev n`. -/
def decEvAux : Nat → Nat → Except GenError Bool
  | 0, _ => .error (.genError "out of fuel")
  | fuel + 1, n =>
    checkerBacktrack
      [ (fun _ => .ok (decide (n = 0))),
        (fun _ => match n with
          | m + 2 => decEvAux fuel m
          | _ => .ok false) ]

/-- Top-level checker: run `decEvAux` with the supplied fuel budget. -/
def decEv (n : Nat) : Nat → Except GenError Bool := fun fuel => decEvAux fuel n

-- Operational sanity checks: validate that the definition actually decides evenness.
#guard (decEvAux 5 4).toOption = some true
#guard (decEvAux 5 6).toOption = some true
#guard (decEvAux 5 5).toOption = some false
#guard (decEvAux 5 7).toOption = some false
#guard (decEvAux 1 100).toOption = none

/-- One-step unfolding of the fueled checker: at nonzero fuel it is the backtracking checker over
    the two constructor sub-checkers. It holds definitionally, so it keeps the inner `match` and
    recursive call intact — unlike `rw [decEvAux]`, which would split the `match` on `n`. -/
private theorem decEvAux_succ (fuel n : Nat) :
    decEvAux (fuel + 1) n = checkerBacktrack
      [ (fun _ => .ok (decide (n = 0))),
        (fun _ => match n with
          | m + 2 => decEvAux fuel m
          | _ => .ok false) ] := rfl

/-- **Checker soundness (core).** If the fueled checker answers "yes", `n` is even.
    Ends by applying `Ev.z` / `Ev.ss` — the step reflection will replace with `Provable.intro`. -/
theorem decEvAux_sound (fuel n : Nat) : decEvAux fuel n = .ok true → Ev n := by
  induction fuel generalizing n with
  | zero => intro h; simp [decEvAux] at h
  | succ fuel ih =>
    intro h
    rw [decEvAux_succ, checkerBacktrack_ok_true] at h
    obtain ⟨c, hmem, hc⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · have hn : n = 0 := by simpa using hc
      subst hn; exact Ev.z
    · rcases n with _ | _ | k
      · simp at hc
      · simp at hc
      · exact Ev.ss (ih k (by simpa using hc))

/-- **Checker soundness** against the `Semantics` target. -/
theorem decEv_sound (n : Nat) : CheckerSound (decEv n) (Ev n) :=
  fun fuel h => decEvAux_sound fuel n h

/-- **Checker completeness (core).** If `n` is even, some fuel makes the checker answer "yes".
    Proceeds by induction on the derivation `h : Ev n` — the step reflection will replace with
    induction on `Provable`. -/
theorem decEvAux_complete {n : Nat} (h : Ev n) : ∃ fuel, decEvAux fuel n = .ok true := by
  induction h with
  | z => exact ⟨1, rfl⟩
  | ss hk ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    rw [decEvAux_succ, checkerBacktrack_ok_true]
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simpa using hfuel⟩

/-- **Checker completeness** against the `Semantics` target. -/
theorem decEv_complete (n : Nat) : CheckerComplete (decEv n) (Ev n) :=
  fun h => decEvAux_complete h

/-- If two backtracking-checker branch lists agree on which branches can yield `ok true` (positive
    direction) and, when *all* branches of the first definitively fail, so do all of the second
    (negative direction), the overall verdict is preserved. Both cases reduce to the combinator
    specs `checkerBacktrack_ok_true`/`checkerBacktrack_ok_false`. -/
private theorem cb_mono
    {l₁ l₂ : List (Unit → Except GenError Bool)} {b : Bool}
    (htrue : (∃ c ∈ l₁, c () = Except.ok true) → (∃ c ∈ l₂, c () = Except.ok true))
    (hfalse : (∀ c ∈ l₁, c () = Except.ok false) → (∀ c ∈ l₂, c () = Except.ok false)) :
    checkerBacktrack l₁ = .ok b → checkerBacktrack l₂ = .ok b := by
  intro h
  cases b with
  | true => rw [checkerBacktrack_ok_true] at h ⊢; exact htrue h
  | false => rw [checkerBacktrack_ok_false] at h ⊢; exact hfalse h

/-- The `ss` constructor's sub-checker is itself fuel-monotone: on `n = m + 2` it is the recursive
    call, handled by the induction hypothesis; otherwise it is the constant `ok false`. -/
private theorem ssBranch_mono (fuel : Nat)
    (ih : ∀ m b, decEvAux fuel m = .ok b → decEvAux (fuel + 1) m = .ok b)
    (n : Nat) (β : Bool)
    (h : (match n with | m + 2 => decEvAux fuel m | _ => .ok false) = .ok β) :
    (match n with | m + 2 => decEvAux (fuel + 1) m | _ => .ok false) = .ok β := by
  match n, h with
  | 0, h => exact h
  | 1, h => exact h
  | k + 2, h => exact ih k β h

/-- **Checker fuel-monotonicity (core).** A definite verdict is preserved when fuel increases —
    the gluing lemma that lets sub-checkers at different fuels be combined. -/
theorem decEvAux_monotone (fuel n : Nat) (b : Bool) :
    decEvAux fuel n = .ok b → decEvAux (fuel + 1) n = .ok b := by
  induction fuel generalizing n b with
  | zero => intro h; simp [decEvAux] at h
  | succ fuel ih =>
    intro h
    rw [decEvAux_succ] at h
    rw [decEvAux_succ]
    refine cb_mono ?_ ?_ h
    · rintro ⟨c, hmem, hc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨_, List.mem_cons_self, hc⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ssBranch_mono fuel ih n true hc⟩
    · intro hall c hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hall _ List.mem_cons_self
      · exact ssBranch_mono fuel ih n false (hall _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **Checker monotonicity** against the `Semantics` target. -/
theorem decEv_monotone (n : Nat) : DecOptMonotone (decEv n) :=
  fun fuel b h => decEvAux_monotone fuel n b h

/-- **Refutation-soundness**: a definite `ok false` verdict means `n` is odd. Induction on fuel. -/
theorem decEvAux_refute : ∀ (fuel n : Nat), decEvAux fuel n = .ok false → ¬ Ev n
  | 0, n => by intro h; simp [decEvAux] at h
  | fuel + 1, n => by
    intro h hEv
    rw [decEvAux_succ, checkerBacktrack_ok_false] at h
    have hz := h _ List.mem_cons_self
    have hss := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    cases hEv with
    | z => simp at hz
    | ss hk => exact decEvAux_refute fuel _ hss hk

/-- **Decisiveness** at bound `n + 1`: with that fuel the derived checker commits to a definite
    verdict — the `ss` recursion strictly decreases `n`, so the search exhausts. Uses the generic
    `checkerBacktrack_isOk`. This earns bounded refutation for a *derived* checker (no `Decidable`). -/
theorem decEvAux_decisive : ∀ (fuel n : Nat), n < fuel → ∃ b, decEvAux fuel n = .ok b
  | 0, n, h => absurd h (Nat.not_lt_zero n)
  | fuel + 1, n, h => by
    rw [decEvAux_succ]
    apply checkerBacktrack_isOk
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, rfl⟩
    · rcases n with _ | _ | m
      · exact ⟨false, rfl⟩
      · exact ⟨false, rfl⟩
      · exact decEvAux_decisive fuel m (by omega)

/-- **Bounded refutation for the derived `Ev` checker** — earned through decreasing recursion, not a
    `Decidable` instance. This is precisely the obligation a negated `¬ Ev …` premise would need. -/
theorem decEv_refutesBounded (n : Nat) : RefutesBounded (decEv n) (Ev n) :=
  refutesBounded_of_decisive (bound := n + 1)
    (fun _ h => decEvAux_decisive _ n (by omega))
    (decEv_sound n)
    (fun fuel h => decEvAux_refute fuel n h)

/-! ### `Ev` as an instance of the generic checker interpreter

Validates `CheckerInterp`: `Ev`'s one-level step + three *single-level* obligations (no fuel
induction — the interpreter supplies the recursion) feed the generic theorems to yield bounded
refutation for free. This is the shape the metaprogram would emit per relation. -/

/-- `Ev`'s one-level checker step: the two constructor branches, recursion abstracted into `rec`. -/
def evStep : CheckerStep Nat := fun rec n =>
  checkerBacktrack [ (fun _ => .ok (decide (n = 0))),
                     (fun _ => match n with | m + 2 => rec m | _ => .ok false) ]

theorem evStep_sound : StepSound evStep Ev := by
  intro rec n hrec h
  simp only [evStep, checkerBacktrack_ok_true] at h
  obtain ⟨c, hc, hcv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · have hn : n = 0 := by simpa using hcv
    subst hn; exact Ev.z
  · rcases n with _ | _ | m
    · simp at hcv
    · simp at hcv
    · exact Ev.ss (hrec m hcv)

theorem evStep_refute : StepRefute evStep Ev := by
  intro rec n hrec h hEv
  simp only [evStep, checkerBacktrack_ok_false] at h
  have hz := h _ List.mem_cons_self
  have hss := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  cases hEv with
  | z => simp at hz
  | ss hk => exact hrec _ hss hk

theorem evStep_decisive : StepDecisive evStep id := by
  intro rec n hrec
  simp only [evStep]
  apply checkerBacktrack_isOk
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨_, rfl⟩
  · rcases n with _ | _ | m
    · exact ⟨false, rfl⟩
    · exact ⟨false, rfl⟩
    · exact hrec m (by simp only [id_eq]; omega)

/-- Bounded refutation for `Ev`, derived through the **generic** interpreter (no fuel induction in
    the per-relation obligations). -/
theorem ev_refutesBounded_generic (n : Nat) :
    RefutesBounded (fun fuel => decRel evStep fuel n) (Ev n) :=
  decRel_refutesBounded evStep_sound evStep_refute evStep_decisive n

theorem evStep_complete : StepComplete evStep Ev id := by
  intro rec n hrec hEv
  simp only [evStep]
  rw [checkerBacktrack_ok_true]
  cases hEv with
  | z => exact ⟨_, List.mem_cons_self, by simp⟩
  | ss hk =>
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    exact hrec _ (by simp only [id_eq]; omega) hk

/-- Positive completeness for `Ev`, derived through the **generic** interpreter. -/
theorem ev_complete_generic (n : Nat) (h : Ev n) :
    ∃ fuel, decRel evStep fuel n = .ok true :=
  decRel_complete evStep_complete n h

/-! ### Enumerator

The `Ev` enumerator mirrors the checker's constructor structure:
* constructor `z`  contributes `0`;
* constructor `ss` contributes `m + 2` for every `m` enumerated at the smaller budget.

The core `enumEvL` is an ordinary `List` (clean recursor + core `List.mem_*` API); `enumEv` adapts
it to the `EnumSizedSuchThat` shape `Nat → ExceptT GenError Enumerator Nat` by tagging outputs with
`Except.ok` (this enumerator never fails) and exposing them as a `LazyList` via `fromList` — see
`LazyListLemmas`, which bridges membership so no proof fights `LazyList`'s `Thunk` recursion or the
`partial` `bindLazyList`. The inner size is unused; the budget drives recursion. -/

/-- Core enumerator: all evens reachable within `budget` `ss`-steps, as a finite list. -/
def enumEvL : Nat → List Nat
  | 0 => [0]
  | budget + 1 => 0 :: (enumEvL budget).map (· + 2)

/-- The constrained enumerator in `EnumSizedSuchThat` shape. -/
def enumEv : Nat → ExceptT GenError Enumerator Nat :=
  fun budget _size => LazyList.fromList ((enumEvL budget).map Except.ok)

-- Operational sanity checks: the core enumerates exactly the evens up to the budget bound.
#guard enumEvL 0 = [0]
#guard enumEvL 3 = [0, 2, 4, 6]
#guard enumEvL 5 = [0, 2, 4, 6, 8, 10]

/-- The enumerator's outcome set at a budget reduces to `List` membership in `enumEvL`. -/
theorem mem_enumEv {budget size x : Nat} :
    enumSupportAt (enumEv budget) size x ↔ x ∈ enumEvL budget := by
  simp only [enumSupportAt, enumEv, ExceptT.run, LazyList.mem_fromList, List.mem_map,
    Except.ok.injEq]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro h; exact ⟨x, h, rfl⟩

/-- Core soundness: everything `enumEvL` produces is even. Structural recursion on the budget. -/
theorem enumEvL_sound : ∀ (budget x : Nat), x ∈ enumEvL budget → Ev x
  | 0, x, hb => by simp only [enumEvL, List.mem_singleton] at hb; subst hb; exact Ev.z
  | budget + 1, x, hb => by
    simp only [enumEvL, List.mem_cons, List.mem_map] at hb
    rcases hb with rfl | ⟨m, hm, rfl⟩
    · exact Ev.z
    · exact Ev.ss (enumEvL_sound budget m hm)

/-- Core completeness: every even number appears in `enumEvL` at some budget. Induction on the
    derivation `Ev x` — the step reflection will replace with induction on `Provable`. -/
theorem enumEvL_complete {x : Nat} (h : Ev x) : ∃ budget, x ∈ enumEvL budget := by
  induction h with
  | z => exact ⟨0, by simp [enumEvL]⟩
  | ss _ ih =>
    obtain ⟨budget, hb⟩ := ih
    exact ⟨budget + 1, by
      simp only [enumEvL, List.mem_cons, List.mem_map]; exact Or.inr ⟨_, hb, rfl⟩⟩

/-- **Enumerator soundness** against the `Semantics` target: every enumerated value is even. -/
theorem enumEv_sound : EnumSound enumEv (fun n => Ev n) := by
  intro x hx
  obtain ⟨budget, hb⟩ := hx
  exact enumEvL_sound budget x (mem_enumEv.mp hb)

/-- **Enumerator completeness** against the `Semantics` target: every even number is enumerated. -/
theorem enumEv_complete : EnumComplete enumEv (fun n => Ev n) := by
  intro x hx
  obtain ⟨budget, hb⟩ := enumEvL_complete hx
  exact ⟨budget, mem_enumEv.mpr hb⟩

/-! ### Generator (real `Plausible.Gen`, QuickChick support axioms)

Same constructor structure over the *executed* `Plausible.Gen`. Completeness is not provable about
the opaque `StdGen`, so we use the documented QuickChick support laws (`GenAxioms.lean`):
* `z`  → `pure 0`;
* `ss` → `pure (m + 2)` for a recursively-generated even `m`, sequenced with `>>=`;
* branch choice via `GeneratorCombinators.backtrack`. -/

/-- The `Ev` generator over the real generator monad. -/
def genEvG : Nat → Gen Nat
  | 0 => pure 0
  | budget + 1 =>
    GeneratorCombinators.backtrack [(1, pure 0), (1, genEvG budget >>= fun m => pure (m + 2))]

/-- One-step unfolding (definitional), keeping the branch list intact. -/
private theorem genEvG_succ (budget : Nat) :
    genEvG (budget + 1) =
      GeneratorCombinators.backtrack
        [(1, pure 0), (1, genEvG budget >>= fun m => pure (m + 2))] := rfl

/-- The branch weights are positive — required by the backtrack support law. -/
private theorem genEvG_hpos (budget : Nat) :
    ∀ p ∈ ([(1, pure 0), (1, genEvG budget >>= fun m => pure (m + 2))] : List (Nat × Gen Nat)),
      0 < p.1 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact Nat.one_pos

/-- Soundness at a fixed budget, with the size argument kept universally quantified (the budget, not
    the `Gen`-size, drives the recursion). Induction on the budget. -/
private theorem genEvG_supportAt_sound (budget : Nat) :
    ∀ (sz x : Nat), genSupportAt (genEvG budget) sz x → Ev x := by
  induction budget with
  | zero =>
    intro sz x h
    rw [show genEvG 0 = pure 0 from rfl, genSupportAt_pure] at h
    subst h; exact Ev.z
  | succ budget ih =>
    intro sz x h
    rw [genEvG_succ] at h
    obtain ⟨p, hpmem, hp⟩ := (genSupportAt_backtrack _ (genEvG_hpos budget) sz x).mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
    rcases hpmem with rfl | rfl
    · simp only [genSupportAt_pure] at hp; subst hp; exact Ev.z
    · simp only [genSupportAt_bind, genSupportAt_pure] at hp
      obtain ⟨a, ha, rfl⟩ := hp
      exact Ev.ss (ih sz a ha)

/-- **Generator soundness** against the `Semantics` target (real `Gen`). -/
theorem genEvG_sound : GenSound genEvG (fun n => Ev n) := by
  intro x hx
  obtain ⟨sz, hs⟩ := hx
  exact genEvG_supportAt_sound sz sz x hs

/-- Completeness: some budget makes an even `x` producible at every size. Induction on `Ev x`;
    `backtrack`'s union support (the QuickChick axiom) lets the `ss` branch fire. -/
private theorem genEvG_supportAt_complete {x : Nat} (h : Ev x) :
    ∃ budget, ∀ sz, genSupportAt (genEvG budget) sz x := by
  induction h with
  | z =>
    refine ⟨0, fun sz => ?_⟩
    rw [show genEvG 0 = pure 0 from rfl, genSupportAt_pure]
  | @ss n hm ih =>
    obtain ⟨budget, hb⟩ := ih
    refine ⟨budget + 1, fun sz => ?_⟩
    rw [genEvG_succ]
    refine (genSupportAt_backtrack _ (genEvG_hpos budget) sz _).mpr ?_
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [genSupportAt_bind]
    exact ⟨n, hb sz, (genSupportAt_pure _ _ _).mpr rfl⟩

/-- **Generator completeness** against the `Semantics` target (real `Gen`), via the QuickChick axiom. -/
theorem genEvG_complete : GenComplete genEvG (fun n => Ev n) := by
  intro x hx
  obtain ⟨budget, hb⟩ := genEvG_supportAt_complete hx
  exact ⟨budget, hb budget⟩

/-! ### Reflection: `Ev` as a `RelSpec`, and adequacy

Milestone 2's foundation: reflect `Ev` into `RelSpec` data and bridge it to the real relation. The
two generic-proof hooks appear here concretely — soundness (⟸ below) uses `Provable.intro`,
completeness (⟹) inducts on `Provable`. -/

/-- Reflected `z` constructor: concludes `Ev 0`, no premises. -/
def evZCtor : RelCtor Nat :=
  { Vars := Unit, recs := fun _ => [], side := fun _ => True, concl := fun _ => 0 }

/-- Reflected `ss` constructor: concludes `Ev (n+2)` from the recursive premise `Ev n`. -/
def evSSCtor : RelCtor Nat :=
  { Vars := Nat, recs := fun n => [n], side := fun _ => True, concl := fun n => n + 2 }

/-- `Ev` reflected as a `RelSpec`. -/
def evSpec : RelSpec Nat := { ctors := [evZCtor, evSSCtor] }

/-- **Adequacy**: the reflected `evSpec` denotes exactly `Ev`. This is the only per-relation bridge
    the generic theorems need (the metaprogram will emit it). -/
theorem provable_evSpec_iff (n : Nat) : Provable evSpec n ↔ Ev n := by
  constructor
  · intro h
    induction h with
    | intro c hc vs hrec hside ih =>
      simp only [evSpec, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Ev.z
      · exact Ev.ss (ih vs (by simp only [evSSCtor]; exact List.mem_singleton_self vs))
  · intro h
    induction h with
    | z => exact Provable.intro evZCtor (by simp [evSpec]) () (by simp [evZCtor]) trivial
    | ss _ ih =>
      refine Provable.intro evSSCtor (by simp [evSpec]) _ ?_ trivial
      intro a ha; simp only [evSSCtor, List.mem_singleton] at ha; subst ha; exact ih

end Specimen.Correctness.EvSlice
