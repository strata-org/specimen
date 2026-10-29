import Specimen.Correctness.Semantics
import Specimen.Correctness.Combinators

/-!
# Generic relation-level checker interpreter

A relation's checker is the fuel-iteration of a **one-level step**: `step rec a` decides `R a` using
`rec` for recursive premises (in practice a `checkerBacktrack` over the constructors). `decRel`
ties the recursive knot with fuel. The step is the per-relation datum the metaprogram produces; the
theorems here are about the *process* of iterating it — proved once, generically over any typed
relation `R : A → Prop`.

Everything stays intrinsically typed: `A` is a real type, `R` a real predicate, `step` a real
function. No untyped syntax. Delivers, generically:
* `decRel_sound`   — a relatively-sound step ⟹ sound checker;
* `decRel_refute`  — relatively-refutation-sound step ⟹ refutation-sound checker;
* `decRel_decisive` — a **measure-guarded** step ⟹ the checker is decisive at bounded fuel
  (the generic "structural decrease ⟹ bounded search");
* `decRel_refutesBounded` — hence **bounded refutation** for any structurally-decreasing relation
  (so it is admissible under negation), with no per-instance proof beyond the step obligations.
-/

open Plausible DecOpt

namespace Specimen.Correctness

variable {A : Type}

/-- One-level checker operator: decide `a` using `rec` for recursive premises. -/
abbrev CheckerStep (A : Type) := (A → Except GenError Bool) → A → Except GenError Bool

/-- Full checker: iterate the one-level `step`, bottoming at `error` when fuel is exhausted;
    recursive premises call the previous fuel-level's checker. -/
def decRel (step : CheckerStep A) : Nat → A → Except GenError Bool
  | 0, _ => .error (.genError "out of fuel")
  | fuel + 1, a => step (decRel step fuel) a

/-- `step` is sound relative to its recursive checker. -/
def StepSound (step : CheckerStep A) (R : A → Prop) : Prop :=
  ∀ (rec : A → Except GenError Bool) (a : A),
    (∀ a', rec a' = .ok true → R a') → step rec a = .ok true → R a

/-- `step` is refutation-sound relative to its recursive checker. -/
def StepRefute (step : CheckerStep A) (R : A → Prop) : Prop :=
  ∀ (rec : A → Except GenError Bool) (a : A),
    (∀ a', rec a' = .ok false → ¬ R a') → step rec a = .ok false → ¬ R a

/-- `step` is **decisive guarded by a measure `μ`**: if the recursive checker is definite on every
    strictly-`μ`-smaller argument, one level is definite on `a`. This is the generic form of
    "recursive premises structurally decrease `μ`, side-conditions decidable, no unbounded
    existentials." -/
def StepDecisive (step : CheckerStep A) (μ : A → Nat) : Prop :=
  ∀ (rec : A → Except GenError Bool) (a : A),
    (∀ a', μ a' < μ a → ∃ b, rec a' = .ok b) → ∃ b, step rec a = .ok b

/-- **Generic soundness**: iterate a relatively-sound step ⟹ sound checker. Induction on fuel. -/
theorem decRel_sound {step : CheckerStep A} {R : A → Prop} (hstep : StepSound step R) :
    ∀ (fuel : Nat) (a : A), decRel step fuel a = .ok true → R a
  | 0, a => by intro h; simp [decRel] at h
  | fuel + 1, a => fun h => hstep _ a (fun a' h' => decRel_sound hstep fuel a' h') h

/-- **Generic refutation-soundness**. -/
theorem decRel_refute {step : CheckerStep A} {R : A → Prop} (hstep : StepRefute step R) :
    ∀ (fuel : Nat) (a : A), decRel step fuel a = .ok false → ¬ R a
  | 0, a => by intro h; simp [decRel] at h
  | fuel + 1, a => fun h => hstep _ a (fun a' h' => decRel_refute hstep fuel a' h') h

/-- **Generic decisiveness** — structural decrease ⟹ bounded search: a measure-guarded step yields a
    checker that is decisive once fuel exceeds the measure. Induction on fuel; the recursive checker
    is definite on smaller-measure args by the IH. -/
theorem decRel_decisive {step : CheckerStep A} {μ : A → Nat} (hstep : StepDecisive step μ) :
    ∀ (fuel : Nat) (a : A), μ a < fuel → ∃ b, decRel step fuel a = .ok b
  | 0, a, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a, h =>
    hstep (decRel step fuel) a (fun a' ha' => decRel_decisive hstep fuel a' (by omega))

/-- **Generic bounded refutation** (milestone 2): any relation whose one-level step is sound,
    refutation-sound, and measure-guarded-decisive has a checker with bounded refutation — hence is
    admissible under negation. Generic over `A`, `R`, `μ`, `step`; no per-instance proof beyond the
    three step obligations. -/
theorem decRel_refutesBounded {step : CheckerStep A} {R : A → Prop} {μ : A → Nat}
    (hs : StepSound step R) (hr : StepRefute step R) (hd : StepDecisive step μ) (a : A) :
    RefutesBounded (fun fuel => decRel step fuel a) (R a) :=
  refutesBounded_of_decisive (bound := μ a + 1)
    (fun fuel hf => decRel_decisive hd fuel a (by omega))
    (fun fuel h => decRel_sound hs fuel a h)
    (fun fuel h => decRel_refute hr fuel a h)

/-- `step` is complete relative to its recursive checker, measure-guarded: given `R a` and a checker
    that succeeds on every strictly-`μ`-smaller `R`-argument, one level succeeds. Holds for
    structurally-decreasing relations (recursive premises drop `μ`). -/
def StepComplete (step : CheckerStep A) (R : A → Prop) (μ : A → Nat) : Prop :=
  ∀ (rec : A → Except GenError Bool) (a : A),
    (∀ a', μ a' < μ a → R a' → rec a' = .ok true) → R a → step rec a = .ok true

theorem decRel_complete_aux {step : CheckerStep A} {R : A → Prop} {μ : A → Nat}
    (hstep : StepComplete step R μ) :
    ∀ (fuel : Nat) (a : A), μ a < fuel → R a → decRel step fuel a = .ok true
  | 0, a, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a, hlt, hR =>
    hstep (decRel step fuel) a
      (fun a' ha' hR' => decRel_complete_aux hstep fuel a' (by omega) hR') hR

/-- **Generic positive completeness** for structurally-decreasing relations: `R a` ⟹ the checker
    answers yes at fuel `μ a + 1`. No monotonicity needed — all recursive premises share the outer
    fuel. Together with `decRel_sound`/`_refute`/`_decisive`, this is the full four-fold `DecOpt`
    correctness, generic over any measure-decreasing relation. -/
theorem decRel_complete {step : CheckerStep A} {R : A → Prop} {μ : A → Nat}
    (hstep : StepComplete step R μ) (a : A) (h : R a) :
    ∃ fuel, decRel step fuel a = .ok true :=
  ⟨μ a + 1, decRel_complete_aux hstep (μ a + 1) a (Nat.lt_succ_self _) h⟩

/-! ## Relation-level assembly: a `step` as `checkerBacktrack` over constructor branches

A relation's one-level step is `checkerBacktrack` over one branch per constructor. Each branch has a
`cond` ("this constructor's premises hold for `a`") and a checker `br`. The four `Step*` obligations
then decompose into **per-constructor** ones plus a single **adequacy** bridge
`R a ↔ ∃ ctor, its cond holds` — i.e. `R` is exactly the disjunction of its constructors' premises.
Proved generically via the `checkerBacktrack` combinator specs; this is where the metaprogram's
per-constructor obligations meet the real relation. -/

/-! ## Two-counter form, matching what the deriver actually emits

`decRel` above carries a single `fuel`. A *derived* checker's worker has signature
`Nat → Nat → Nat → A → Except GenError Bool` — `fuel`, `initSize`, `size` — and both `fuel` and `size`
are load-bearing. Measured on a derived checker for ascending-sortedness at fixed `fuel = 10000`:

| `size` | `[1,2,3]` | `[3,2]` |
|---|---|---|
| 0 | `error` | `error` |
| 1 | `error` | `ok false` |
| 5 | `ok true` | `ok false` |

and at `size = 9` it needs `fuel ≥ 9`. So neither counter collapses into the other. The step is
*size-indexed* because the emitted code offers only the non-recursive constructor branches at
`size = 0` (verified: `[]` and `[7]` are both `ok true` there).

The fuel-exhaustion error is a **parameter** `e`, not a fixed string. It carries no semantic content —
no theorem here inspects it — and pinning it would make the bridge to an emitted `aux_dec` fail at
fuel 0 for a purely cosmetic reason: the deriver throws `Gen.outOfFuelError`, while `decRel` and
`EvSlice`'s hand-written checker use `"out of fuel"`. Parameterising lets one model serve both.

`decRelS_const_eq_decRel` shows the one-counter theory is the size-ignoring special case, so nothing
already proven is lost. -/


/-- Emitted checkers carry **two** counters, not one: `fuel` (termination backstop) and `size` (the
    proof-depth budget), plus `initSize` threaded for sub-producers. Measured on a derived checker:
    at fixed `fuel` the verdict sharpens with `size`, and at fixed `size` it needs enough `fuel` —
    so neither collapses into the other, and `decRel`'s single counter cannot model them.

    The step is **size-indexed** because the emitted code offers only the non-recursive constructor
    branches at `size = 0`. -/
def decRelS (e : GenError) (step : Nat → CheckerStep A) :
    Nat → Nat → Nat → A → Except GenError Bool
  | 0, _, _, _ => .error e
  | fuel + 1, initSize, size, a => step size (decRelS e step fuel initSize (size - 1)) a

/-- **Generic soundness, two-counter form.** Same three-line induction on fuel as `decRel_sound`;
    the size index is carried along and never inspected, so uniform step-soundness suffices. -/
theorem decRelS_sound {e : GenError} {step : Nat → CheckerStep A} {R : A → Prop}
    (hstep : ∀ sz, StepSound (step sz) R) :
    ∀ (fuel initSize size : Nat) (a : A), decRelS e step fuel initSize size a = .ok true → R a
  | 0, _, _, a => by intro h; simp [decRelS] at h
  | fuel + 1, iS, sz, a => fun h =>
      hstep sz _ a (fun a' h' => decRelS_sound hstep fuel iS (sz - 1) a' h') h

/-- **Generic refutation-soundness, two-counter form.** -/
theorem decRelS_refute {e : GenError} {step : Nat → CheckerStep A} {R : A → Prop}
    (hstep : ∀ sz, StepRefute (step sz) R) :
    ∀ (fuel initSize size : Nat) (a : A), decRelS e step fuel initSize size a = .ok false → ¬ R a
  | 0, _, _, a => by intro h; simp [decRelS] at h
  | fuel + 1, iS, sz, a => fun h =>
      hstep sz _ a (fun a' h' => decRelS_refute hstep fuel iS (sz - 1) a' h') h

/-- `step` is complete relative to a **measure pair**, the two-counter analogue of `StepComplete`.

`φ` budgets fuel and `σ` budgets size, and they are genuinely different axes: `decRelS` decrements
`size` at every level while `fuel` only has to outlast the derivation. Note the recursive hypothesis
is available at `sz - 1` and nowhere else — that is not a simplification, it is what `decRelS` actually
passes, so a step that wanted its premise checked at the *same* size could not satisfy this. -/
def StepCompleteS (step : Nat → CheckerStep A) (R : A → Prop) (φ σ : A → Nat) : Prop :=
  ∀ (sz : Nat) (rec : A → Except GenError Bool) (a : A), σ a ≤ sz → R a →
    (∀ a', R a' → φ a' < φ a → σ a' ≤ sz - 1 → rec a' = .ok true) →
    step sz rec a = .ok true

/-- **Generic positive completeness for the two-counter checker.** The counterpart of
`decRel_complete`, and the checker analogue of `genRelB_complete`/`genRelFam_complete`: one induction
on fuel, with the size budget threaded through the step's own hypothesis. -/
theorem decRelS_complete {e : GenError} {step : Nat → CheckerStep A} {R : A → Prop} {φ σ : A → Nat}
    (hstep : StepCompleteS step R φ σ) :
    ∀ (fuel initSize sz : Nat) (a : A), R a → φ a < fuel → σ a ≤ sz →
      decRelS e step fuel initSize sz a = .ok true
  | 0, _, _, _ => fun _ hf _ => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, iS, sz, a => fun hR hf hs =>
    hstep sz _ a hs hR
      (fun a' hR' hlt hs' => decRelS_complete hstep fuel iS (sz - 1) a' hR' (by omega) hs')

/-- `step` is **decisive guarded by a measure pair** — the two-counter analogue of `StepDecisive`.

Both budgets are needed and for different reasons: without enough `fuel` the iteration bottoms out at
the out-of-fuel `error`, and without enough `size` the emitted `size = 0` case has replaced its
recursive slot with a `throw`, which is *also* an `error`. Decisiveness is precisely the claim that
neither happens. -/
def StepDecisiveS (step : Nat → CheckerStep A) (φ σ : A → Nat) : Prop :=
  ∀ (sz : Nat) (rec : A → Except GenError Bool) (a : A), σ a ≤ sz →
    (∀ a', φ a' < φ a → σ a' ≤ sz - 1 → ∃ b, rec a' = .ok b) →
    ∃ b, step sz rec a = .ok b

/-- **Generic decisiveness for the two-counter checker.** With `decRelS_sound` and `decRelS_refute`
this completes the four-fold `DecOpt` correctness in the size-indexed setting: the verdict is always
definite, and definite verdicts are correct in both polarities. -/
theorem decRelS_decisive {e : GenError} {step : Nat → CheckerStep A} {φ σ : A → Nat}
    (hstep : StepDecisiveS step φ σ) :
    ∀ (fuel initSize sz : Nat) (a : A), φ a < fuel → σ a ≤ sz →
      ∃ b, decRelS e step fuel initSize sz a = .ok b
  | 0, _, _, _ => fun hf _ => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, iS, sz, a => fun hf hs =>
    hstep sz _ a hs (fun a' hlt hs' => decRelS_decisive hstep fuel iS (sz - 1) a' (by omega) hs')

/-- The single-counter theory is the special case where the step ignores its size index — so nothing
    already proven is lost by moving to `decRelS`. -/
theorem decRelS_const_eq_decRel (step : CheckerStep A) :
    ∀ (fuel initSize size : Nat) (a : A),
      decRelS (.genError "out of fuel") (fun _ => step) fuel initSize size a = decRel step fuel a
  | 0, _, _, _ => rfl
  | fuel + 1, iS, sz, a => by
      simp only [decRelS, decRel]
      congr 1
      funext a'
      exact decRelS_const_eq_decRel step fuel iS (sz - 1) a'

/-- One reflected constructor branch: its applicability condition and its branch checker. -/
structure CtorBranch (A : Type) where
  cond : A → Prop
  br : CheckerStep A

/-- The relation's step: backtrack over the constructor branches. -/
def stepBacktrack (brs : List (CtorBranch A)) : CheckerStep A :=
  fun rec a => checkerBacktrack (brs.map (fun c => fun _ => c.br rec a))

theorem stepBacktrack_sound {brs : List (CtorBranch A)} {R : A → Prop}
    (hadeq : ∀ a, R a ↔ ∃ c ∈ brs, c.cond a)
    (hbr : ∀ c ∈ brs, ∀ (rec : A → Except GenError Bool) (a : A),
      (∀ a', rec a' = .ok true → R a') → c.br rec a = .ok true → c.cond a) :
    StepSound (stepBacktrack brs) R := by
  intro rec a hrec h
  simp only [stepBacktrack, checkerBacktrack_ok_true] at h
  obtain ⟨f, hf, hfv⟩ := h
  rw [List.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  exact (hadeq a).mpr ⟨c, hc, hbr c hc rec a hrec hfv⟩

theorem stepBacktrack_refute {brs : List (CtorBranch A)} {R : A → Prop}
    (hadeq : ∀ a, R a ↔ ∃ c ∈ brs, c.cond a)
    (hbr : ∀ c ∈ brs, ∀ (rec : A → Except GenError Bool) (a : A),
      (∀ a', rec a' = .ok false → ¬ R a') → c.br rec a = .ok false → ¬ c.cond a) :
    StepRefute (stepBacktrack brs) R := by
  intro rec a hrec h hR
  simp only [stepBacktrack, checkerBacktrack_ok_false] at h
  obtain ⟨c, hc, hcond⟩ := (hadeq a).mp hR
  exact hbr c hc rec a hrec (h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)) hcond

theorem stepBacktrack_decisive {brs : List (CtorBranch A)} {μ : A → Nat}
    (hbr : ∀ c ∈ brs, ∀ (rec : A → Except GenError Bool) (a : A),
      (∀ a', μ a' < μ a → ∃ b, rec a' = .ok b) → ∃ b, c.br rec a = .ok b) :
    StepDecisive (stepBacktrack brs) μ := by
  intro rec a hrec
  simp only [stepBacktrack]
  apply checkerBacktrack_isOk
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  exact hbr c hc rec a hrec

theorem stepBacktrack_complete {brs : List (CtorBranch A)} {R : A → Prop} {μ : A → Nat}
    (hadeq : ∀ a, R a ↔ ∃ c ∈ brs, c.cond a)
    (hbr : ∀ c ∈ brs, ∀ (rec : A → Except GenError Bool) (a : A),
      (∀ a', μ a' < μ a → R a' → rec a' = .ok true) → c.cond a → c.br rec a = .ok true) :
    StepComplete (stepBacktrack brs) R μ := by
  intro rec a hrec hR
  simp only [stepBacktrack, checkerBacktrack_ok_true]
  obtain ⟨c, hc, hcond⟩ := (hadeq a).mp hR
  exact ⟨fun _ => c.br rec a, List.mem_map.mpr ⟨c, hc, rfl⟩, hbr c hc rec a hrec hcond⟩

end Specimen.Correctness
