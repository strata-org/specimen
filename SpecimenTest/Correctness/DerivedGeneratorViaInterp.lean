import SpecimenTest.CommonDefinitions.STLCDefinitions
import SpecimenTest.CommonDefinitions.STLCBasaltGenerators
import Specimen
import Specimen.Basalt
import Specimen.Correctness.GenInterpSPMF

/-!
# A *derived* generator proved correct through the generic interpreter

`StlcCompleteness.lean` and `StlcGeneratorSoundness.lean` prove things about emitted code by reasoning
about it directly. That works, but it does not scale: every relation would need its own `backtrack`
bookkeeping. This file does the same job the intended way — via `Specimen.Correctness.GenInterpSPMF`
— and so answers the question that generic development exists to answer: **does the interpreter
actually model what the emitter emits?**

It does, and the evidence is `lk_bridge`:

```
theorem lk_bridge (iS : Nat) : ∀ fuel sz Γ τ,
    specimen_gen_lookup_1__… fuel iS sz Γ τ = genRelB (lkStep iS) fuel sz (Γ, τ)
```

The emitted generator is *literally* the generic interpreter at a particular step — proved by
induction on fuel, where every case is `rfl` except the successor, which closes by rewriting with the
induction hypothesis. Given that, soundness and completeness of the emitted definition follow by
`rw [lk_bridge]` and an appeal to `genRelB_produces_sound` / `genRelB_complete`. No reasoning about
`backtrack`, weights, or the support monad appears at the emitted level at all; it is confined to the
per-branch obligations `lkStep_sound` and `lkStep_complete`.

## The step models the *dispatched* pool

`specimen.dispatchInputs` is on by default, so `lkStep` reproduces the emitted shape verbatim: each
branch sits behind `if (match i.1 with | _ :: _ => true | _ => false) then some … else none` and the
pool is `List.filterMap id` over those options. A bridge against the undispatched pool does not
typecheck — the guard terms are syntactically present in the emitted definition.

## What the emitted code demands of `GenInterpSPMF`

Three features of `GenInterpSPMF` exist *because* real emitted code needs them, and this file is
where each earns its keep:

1. **The input index.** `lookup` recurses on `Γ`'s tail, so the step's `prev` has to be a family over
   inputs as well as size. An interpreter that closed over its arguments could not state the bridge
   at all.
2. **The `size = 0` truncation branches.** The emitted `size = 0` case keeps each recursive
   constructor as its conclusion, cut off with `Specimen.truncated` where it matches. Those branches
   produce nothing (`produces_truncated_iff`), but they are syntactically present, so the bridge has
   to state them and every case split over the pool has to dismiss them.
3. **The measure pair.** `lkPhi`/`lkSigma` unfold to exactly `x < fuel` and `x < sz` — the same two
   side conditions the hand-rolled `lookup_gen_complete` in `StlcCompleteness.lean` arrived at
   independently. That agreement is the cross-check that the generic route computes the right budgets
   rather than merely a sufficient one.
-/

open Plausible Basalt Specimen.Correctness

set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true
-- The pool-membership simp set below is shared across guard configurations; which guard-reduction
-- lemmas fire depends on how the guards evaluate.
set_option linter.unusedSimpArgs false

-- Namespaced so the derived `BacktrackGenFor` instances cannot collide with another module's
-- derivation of the same producers when the whole library is built under `specimen.emitBasalt`.
namespace DerivedGeneratorViaInterp

#guard_msgs(drop info) in
derive_mutual generator (fun Γ τ => ∃ x, lookup Γ x τ)

-- Reconstruct the emitted step, verbatim from the emitted code: input-dispatch guards, `filterMap`
-- pool, weight literals, `Unit`-function branches.
noncomputable def lkStep (iS : Nat) : SGenStep (List type × type) Nat :=
  fun prev sz i =>
    match sz with
    | 0 =>
      Basalt.Backtrack.backtrack
        (List.filterMap (fun o => o)
          [if (match i.1 with | List.cons _ _ => true | _ => false) then
              some (1, fun (_ : Unit) =>
                match i.1 with
                | List.cons τ_1 _ =>
                  match @DecOpt.decOpt (@Eq (@type) τ_1 i.2) _ iS with
                  | Except.ok Bool.true => (return Nat.zero : SGen Nat)
                  | Except.ok Bool.false => Specimen.refute
                  | _ => Specimen.inconclusive
                | _ => Specimen.refute)
            else none,
            if (match i.1 with | List.cons _ _ => true | _ => false) then
              some (1, fun (_ : Unit) =>
                match i.1 with
                | List.cons _ _ => Specimen.truncated
                | _ => Specimen.refute)
            else none])
    | Nat.succ size' =>
      Basalt.Backtrack.backtrack
        (List.filterMap (fun o => o)
          [if (match i.1 with | List.cons _ _ => true | _ => false) then
              some (1, fun (_ : Unit) =>
                match i.1 with
                | List.cons τ_1 _ =>
                  match @DecOpt.decOpt (@Eq (@type) τ_1 i.2) _ iS with
                  | Except.ok Bool.true => (return Nat.zero : SGen Nat)
                  | Except.ok Bool.false => Specimen.refute
                  | _ => Specimen.inconclusive
                | _ => Specimen.refute)
            else none,
            if (match i.1 with | List.cons _ _ => true | _ => false) then
              some (3, fun (_ : Unit) =>
                match i.1 with
                | List.cons _ Γ => do
                  let n ← prev size' (Γ, i.2)
                  return Nat.succ n
                | _ => Specimen.refute)
            else none])

/-- **Adequacy bridge**: the emitted generator IS the generic interpreter at `lkStep`. -/
theorem lk_bridge (iS : Nat) :
    ∀ (fuel sz : Nat) (Γ : List type) (τ : type),
      (specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp
          (G := SGen) fuel iS sz Γ τ)
        = genRelB (lkStep iS) fuel sz (Γ, τ) := by
  intro fuel
  induction fuel with
  | zero => intro sz Γ τ; rfl
  | succ fuel ih =>
    intro sz Γ τ
    cases sz with
    | zero => rfl
    | succ sz =>
      simp only
        [specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp,
         genRelB, lkStep, ih]

def lkSpec : (List type × type) → Nat → Prop := fun i x => lookup i.1 x i.2
def lkPhi : (List type × type) → Nat → Nat := fun _ x => x
def lkSigma : (List type × type) → Nat → Nat := fun _ x => x + 1

/-- The `Now` branch, shared by both size cases, is sound on its own. -/
theorem lkNow_sound (iS : Nat) (Γ : List type) (τ : type) (x : Nat)
    (hx : Produces
      (match Γ with
       | List.cons τ_1 _ =>
         match @DecOpt.decOpt (@Eq (@type) τ_1 τ) _ iS with
         | Except.ok Bool.true => (return Nat.zero : SGen Nat)
         | Except.ok Bool.false => Specimen.refute
         | _ => Specimen.inconclusive
       | _ => Specimen.refute) x) :
    lookup Γ x τ := by
  cases Γ with
  | nil => exact absurd hx (not_produces_refute x)
  | cons τ_1 Γ' =>
    simp only [DecOpt.decOpt] at hx
    by_cases h : τ_1 = τ
    · subst h
      simp only [decide_true] at hx
      cases produces_pure_iff.mp hx
      exact lookup.Now _ _
    · simp only [decide_eq_false h] at hx
      exact absurd hx (not_produces_refute x)

theorem lkStep_sound (iS : Nat) : StepGenSoundB (lkStep iS) lkSpec := by
  intro prev hprev sz i x hx
  obtain ⟨Γ, τ⟩ := i
  -- Case on the dispatching input first, so the guards and the `filterMap` reduce.
  cases Γ with
  | nil =>
    cases sz with
    | zero =>
      simp only [lkStep] at hx
      obtain ⟨p, hp, _, _⟩ := produces_backtrack_ok _ _ hx
      simp at hp
    | succ sz =>
      simp only [lkStep] at hx
      obtain ⟨p, hp, _, _⟩ := produces_backtrack_ok _ _ hx
      simp at hp
  | cons τ_1 Γ' =>
    cases sz with
    | zero =>
      simp only [lkStep] at hx
      obtain ⟨p, hp, _, hpx⟩ := produces_backtrack_ok _ _ hx
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
        ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact lkNow_sound iS _ τ x hpx
      · simp at hpx
    | succ sz =>
      simp only [lkStep] at hx
      obtain ⟨p, hp, _, hpx⟩ := produces_backtrack_ok _ _ hx
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
        ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact lkNow_sound iS _ τ x hpx
      · -- the `Later` branch: `prev` gave a `lookup` in the tail, so prepend
        obtain ⟨n, hn, he⟩ := produces_bind_iff.mp hpx
        cases produces_pure_iff.mp he
        exact lookup.Later _ _ _ _ (hprev sz (Γ', τ) n hn)

theorem lkStep_complete (iS : Nat) : StepGenCompleteB (lkStep iS) lkSpec lkPhi lkSigma := by
  intro prev sz i a hP hsz hrec
  obtain ⟨Γ, τ⟩ := i
  simp only [lkSpec] at hP
  cases sz with
  | zero => exact absurd hsz (by simp only [lkSigma]; omega)
  | succ sz =>
    cases hP with
    | Now τ' Γ' =>
      simp only [lkStep]
      refine produces_backtrack_of_branch _ _ (List.Mem.head _)
        (by dsimp only; decide) _ ?_
      simp only [DecOpt.decOpt, decide_true]
      exact produces_pure_iff.mpr rfl
    | Later τ' τ'' n Γ' hn =>
      simp only [lkStep]
      -- `lkSigma _ (n+1) = n+2 ≤ sz+1` gives `n+1 ≤ sz`, which the recursive appeal needs.
      refine produces_backtrack_of_branch _ _
        (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ ?_
      exact produces_bind_of
        (hrec (Γ', τ) n hn (by simp only [lkPhi]; omega) sz (by simp only [lkSigma] at hsz ⊢; omega))
        (produces_pure_iff.mpr rfl)

/-- **Soundness of the emitted generator, entirely through the generic interpreter.** -/
theorem lookup_emitted_sound (iS fuel sz : Nat) (Γ : List type) (τ : type) (x : Nat)
    (hx : Produces
      (specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp
        (G := SGen) fuel iS sz Γ τ) x) :
    lookup Γ x τ := by
  rw [Produces, lk_bridge] at hx
  exact genRelB_produces_sound (lkStep_sound iS) fuel sz (Γ, τ) x hx

/-- **Completeness of the emitted generator, entirely through the generic interpreter.** The side
    conditions `x < fuel` and `x < sz` are what the measure pair `(lkPhi, lkSigma)` unfolds to — and
    they match the hand-rolled proof in `StlcCompleteness.lean` exactly, which is the cross-check
    that the generic route computes the same budgets. -/
theorem lookup_emitted_complete (iS : Nat) (Γ : List type) (τ : type) (x : Nat)
    (h : lookup Γ x τ) (fuel sz : Nat) (hf : x < fuel) (hs : x < sz) :
    Produces
      (specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp
        (G := SGen) fuel iS sz Γ τ) x := by
  rw [Produces, lk_bridge]
  exact genRelB_complete (lkStep_complete iS) fuel (Γ, τ) x h
    (by simp only [lkPhi]; omega) sz (by simp only [lkSigma]; omega)

/-! ## Decisiveness: the generator does not merely *can* succeed, it *cannot* fail

Completeness says a success `x` is in the support — the generator **can** produce `x`. That is an `∃`
over executions and it is what the support interpretation gives cheaply. It leaves open whether some
other execution fails, which for a *randomized* producer is the question you actually care about: an
unlucky draw ending in a refutation would make the verdict uninformative.

`NeverFails` is the dual claim, a `∀` over the support, and it holds here for a
structural reason: `backtrack` retries, dropping failed branches, starting with `fuel = gs.length` —
so as long as *one* branch cannot fail, the disjunction cannot. For `lookup` that branch is `Now` when
the head matches (a deterministic `pure`), and `Later` otherwise (a `bind` of the recursive call,
which the induction hypothesis covers). -/

theorem lookup_emitted_neverFails (iS : Nat) :
    ∀ (Γ : List type) (x : Nat) (τ : type), lookup Γ x τ →
      ∀ (fuel sz : Nat), x < fuel → x < sz →
      NeverFails
        (specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp
          (G := SGen) fuel iS sz Γ τ) := by
  intro Γ x τ hlk
  induction hlk with
  | Now τ' Γ' =>
    intro fuel sz hf hs
    cases fuel with
    | zero => exact absurd hf (by omega)
    | succ fuel =>
      cases sz with
      | zero => exact absurd hs (by omega)
      | succ sz =>
        simp only
          [specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp]
        refine neverFails_backtrack _ _ (List.Mem.head _) (by dsimp only; decide) ?_
        -- the head matches, so `decOpt` is `ok true` and the branch is a bare `pure`
        simp only [DecOpt.decOpt, decide_true]
        exact neverFails_pure _
  | Later τ' τ'' n Γ' hn ih =>
    intro fuel sz hf hs
    cases fuel with
    | zero => exact absurd hf (by omega)
    | succ fuel =>
      cases sz with
      | zero => exact absurd hs (by omega)
      | succ sz =>
        simp only
          [specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp]
        refine neverFails_backtrack _ _ (List.Mem.tail _ (List.Mem.head _))
          (by dsimp only; decide) ?_
        exact neverFails_bind (ih fuel sz (by omega) (by omega))
          (fun _ _ => neverFails_pure _)

/-! ## Refutation-soundness: a refutation is a proof of uninhabitedness

The fourth direction: a refutation is not just a failed attempt, it is a proof that no value
satisfies the relation. That makes the generator usable as a refutation procedure.

Two things are worth being precise about.

First, why randomness does not weaken it. `backtrack` ends refuted only when **every** branch of
positive weight can (`refutes_backtrack`), so a *possible* refutation is already a statement about all branches
at once — the `∃`-over-executions reading is strong enough here, unlike for `NeverFails`.

Second, the scope of the `MExp.lean` fix that keeps `DecOpt`'s inconclusive answer separate from its
definite `false`. This relation's premise is `τ_1 = τ`, whose `DecOpt` comes from `DecidableEq` and so
never answers `error` — the third arm is dead, and this theorem would survive even an emission that
collapsed `error` into `refute`. The distinction matters where a premise is discharged by a *derived
recursive* checker, which genuinely can run out of budget: an emission that collapsed the two would
turn "I could not tell" into a definite refutation, and the corresponding theorem would be false
(`VerdictFidelity.lean` is that case). So this proof does not exercise the distinction; it is the
shape a relation with a recursive premise would follow, and the `refute`/`inconclusive` split is what
makes the shape sound there.

One wrinkle input dispatch adds: at `Γ = []` the guards fail and the pool is **empty**, and
`backtrack []` refutes outright. That refutation is still sound — nothing is derivable from an empty
context — but it is established from the pool being empty, not from any branch refuting. -/

theorem lookup_emitted_refute (iS : Nat) :
    ∀ (fuel sz : Nat) (Γ : List type) (τ : type),
      Refutes (specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp
          (G := SGen) fuel iS sz Γ τ) →
      ∀ x, ¬ lookup Γ x τ := by
  intro fuel
  induction fuel with
  | zero =>
    -- out of fuel is a labelled failure, never a refutation
    intro sz Γ τ h
    simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp] at h
    exact absurd h not_refutes_outOfFuel
  | succ fuel ih =>
    intro sz Γ τ h
    cases sz with
    | zero =>
      -- at size 0 `Later` is cut off where `Γ` is a cons, which never refutes; at `Γ = []` no
      -- constructor applies, and the refutation is correct
      simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp] at h
      have hall := refutes_backtrack h
      cases Γ with
      | nil => intro x hx; cases hx
      | cons τ_1 Γ' =>
        have hLater := hall _ (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide)
        simp at hLater
    | succ sz =>
      simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_DerivedGeneratorViaInterp_DerivedGeneratorViaInterp] at h
      have hall := refutes_backtrack h
      cases Γ with
      | nil =>
        -- `lookup` needs a cons, so nothing is derivable and the refutation is correct
        intro x hx; cases hx
      | cons τ_1 Γ' =>
        have hNow := hall _ (List.Mem.head _) (by dsimp only; decide)
        have hLater := hall _ (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide)
        -- `Now` refuting tells us the head does not match ...
        simp only [DecOpt.decOpt] at hNow
        have hne : τ_1 ≠ τ := by
          intro heq
          subst heq
          simp only [decide_true] at hNow
          exact not_refutes_pure _ hNow
        -- ... and `Later` refuting hands the tail to the induction hypothesis
        rcases refutes_bind_iff.mp hLater with ho | ⟨_, _, hres⟩
        · have htail := ih sz Γ' τ ho
          intro x hx
          cases hx with
          | Now => exact hne rfl
          | Later => rename_i n hn; exact htail n hn
        · exact absurd hres (not_refutes_pure _)

-- Pinned: the generic route introduces no axioms beyond `SPMF`'s classicality.
/-- info: 'DerivedGeneratorViaInterp.lookup_emitted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_emitted_sound

/-- info: 'DerivedGeneratorViaInterp.lookup_emitted_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_emitted_complete

/-- info: 'DerivedGeneratorViaInterp.lookup_emitted_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_emitted_neverFails

/-- info: 'DerivedGeneratorViaInterp.lookup_emitted_refute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_emitted_refute

end DerivedGeneratorViaInterp
