import Specimen
import Specimen.Correctness.CheckerInterp

/-!
# Soundness of an *actually derived* checker

`Specimen/Correctness/EvSlice.lean` proves the theory against a **hand-written** checker. This file
closes the remaining gap: it takes the checker that `derive_checker` really emits and proves it sound,
via the generic two-counter theory — so the model is pinned to the deriver's actual output rather than
to a transcription of it.

The chain is:

1. `sortedStep` — the emitted one-level operator, transcribed from the derived source. It is
   *size-indexed* (at `size = 0` the recursive constructor's slot is a `throw`) and closed over
   `initSize` (the side condition is checked at `initSize`, not `size`).
2. `aux_dec_eq` — the bridge: the emitted worker **is** `decRelS` at that step.
3. `sortedStep_sound` — the per-constructor obligation.
4. `instDecOptSorted_sound` — soundness of the emitted checker, via `decRelS_sound`.

## Why this is worth keeping in the suite

It is a regression guard on *emission shape*. If the deriver changes how it emits checkers — the
counter arity, the size-0 branch, where side conditions are checked — step 2 stops compiling, which is
exactly the signal wanted. Every fact encoded here was established by reading emitted output, after
inferring it from the emitter's source got it wrong (the size-0 case keeps all three branch slots with
the recursive one replaced by a `throw`; it does not emit only the base branches).
-/

open Plausible Specimen.Correctness

inductive Sorted : List Nat → Prop where
  | nil  : Sorted []
  | one  : ∀ x, Sorted [x]
  | cons : ∀ x y rest, x ≤ y → Sorted (y :: rest) → Sorted (x :: y :: rest)

#guard_msgs(drop info) in
derive_checker (fun xs => Sorted xs)

/-- The emitted checker's one-level operator, transcribed from the derived source: size-indexed
    (`size = 0` replaces the recursive constructor's slot with a throw) and closed over `initSize`
    (the side condition is checked at `initSize`, not `size`).

    The throw is `outOfFuelError`, which reads as *inconclusive*: at size 0 the recursive constructor was
    never tried, so "no base case matched" must not be reported as `false`. It was `genericFailure` — a
    definite refutation — until the emitted checker's size-0 failsafe was fixed (#56). -/
def sortedStep (i : Nat) : Nat → CheckerStep (List Nat)
  | 0 => fun _ xs => DecOpt.checkerBacktrack
      [ fun _ => match xs with | [] => .ok true | _ => .ok false,
        fun _ => match xs with | [_] => .ok true | _ => .ok false,
        fun _ => throw Gen.outOfFuelError ]
  | _ + 1 => fun rec xs => DecOpt.checkerBacktrack
      [ fun _ => match xs with | [] => .ok true | _ => .ok false,
        fun _ => match xs with | [_] => .ok true | _ => .ok false,
        fun _ => match xs with
          | x :: y :: rest => DecOpt.andOptList [rec (y :: rest), DecOpt.decOpt (x ≤ y) i]
          | _ => .ok false ]

/-- **The bridge**: the *actually emitted* checker is the generic two-counter model at `sortedStep`. -/
theorem aux_dec_eq : ∀ (fuel i sz : Nat) (xs : List Nat),
    instDecOptSorted.aux_dec fuel i sz xs
      = decRelS Gen.outOfFuelError (sortedStep i) fuel i sz xs
  | 0, _, _, _ => rfl
  | fuel + 1, i, 0, xs => by
      simp only [instDecOptSorted.aux_dec, decRelS, sortedStep]
  | fuel + 1, i, sz + 1, xs => by
      cases xs with
      | nil => simp only [instDecOptSorted.aux_dec, decRelS, sortedStep]
      | cons a t =>
        cases t with
        | nil => simp only [instDecOptSorted.aux_dec, decRelS, sortedStep]
        | cons b u =>
          simp only [instDecOptSorted.aux_dec, decRelS, sortedStep, Nat.add_sub_cancel,
            aux_dec_eq fuel i sz (b :: u)]


/-! ## Soundness of the emitted checker, through the generic theory

With the bridge in hand, `decRelS_sound` applies to the real derived `DecOpt` instance — no
hand-written stand-in. -/

/-- Each size-indexed step is sound: a branch answering `ok true` really witnesses `Sorted`. -/
theorem sortedStep_sound (i : Nat) : ∀ sz, StepSound (sortedStep i sz) Sorted := by
  intro sz rec xs hrec h
  cases sz with
  | zero =>
    simp only [sortedStep, checkerBacktrack_ok_true, List.mem_cons, List.not_mem_nil,
      or_false] at h
    obtain ⟨f, hf, hfv⟩ := h
    rcases hf with rfl | rfl | rfl
    · match xs, hfv with
      | [], _ => exact Sorted.nil
    · match xs, hfv with
      | [x], _ => exact Sorted.one x
    · exact absurd hfv (by simp [throw, throwThe, MonadExceptOf.throw])
  | succ sz =>
    simp only [sortedStep, checkerBacktrack_ok_true, List.mem_cons, List.not_mem_nil,
      or_false] at h
    obtain ⟨f, hf, hfv⟩ := h
    rcases hf with rfl | rfl | rfl
    · match xs, hfv with
      | [], _ => exact Sorted.nil
    · match xs, hfv with
      | [x], _ => exact Sorted.one x
    · match xs, hfv with
      | x :: y :: rest, hfv =>
        simp only [andOptList_ok_true, List.mem_cons, List.not_mem_nil, or_false] at hfv
        refine Sorted.cons x y rest ?_ (hrec _ (hfv _ (Or.inl rfl)))
        -- Side condition: `DecOpt` for a decidable `P` is `fun _ => .ok (decide P)`, so `ok true`
        -- gives `P` by `of_decide_eq_true`.
        have hle := hfv _ (Or.inr rfl)
        simp only [DecOpt.decOpt] at hle
        exact of_decide_eq_true (by simpa using hle)

/-- **Soundness of the emitted checker.** -/
theorem instDecOptSorted_sound (fuel i sz : Nat) (xs : List Nat) :
    instDecOptSorted.aux_dec fuel i sz xs = .ok true → Sorted xs := by
  rw [aux_dec_eq]
  exact decRelS_sound (sortedStep_sound i) fuel i sz xs

/-! ## Completeness of the same emitted checker

The other direction, through `decRelS_complete`. Two measures again — `φ` for fuel, `σ` for size —
because `decRelS` spends size at every level while fuel only has to outlast the derivation. For
`Sorted` both are the list length, but they are separately necessary: the `size = 0` case of the
emitted checker replaces the recursive constructor's slot with a `throw`, so a list of length ≥ 2 is
undecidable there however much *fuel* is available. -/

/-- Both measures: list length. -/
def sortedMeasure (xs : List Nat) : Nat := xs.length

theorem sortedStep_complete (i : Nat) :
    StepCompleteS (sortedStep i) Sorted sortedMeasure sortedMeasure := by
  intro sz rec xs hs hSorted hrec
  cases hSorted with
  | nil =>
    -- the `[]` branch answers yes at every size, including `0`
    cases sz <;> simp only [sortedStep, DecOpt.checkerBacktrack] <;> rfl
  | one x =>
    cases sz <;> simp only [sortedStep, DecOpt.checkerBacktrack] <;> rfl
  | cons x y rest hxy hrest =>
    -- `sortedMeasure (x :: y :: rest) = rest.length + 2 ≤ sz` forces `sz ≠ 0`, which is exactly what
    -- makes the recursive slot present rather than a `throw`.
    have hsz : sz ≠ 0 := by simp only [sortedMeasure, List.length_cons] at hs; omega
    obtain ⟨sz', rfl⟩ : ∃ sz', sz = sz' + 1 := ⟨sz - 1, by omega⟩
    have hsub : sortedMeasure (y :: rest) ≤ sz' := by
      simp only [sortedMeasure, List.length_cons] at hs ⊢; omega
    have hlt : sortedMeasure (y :: rest) < sortedMeasure (x :: y :: rest) := by
      simp only [sortedMeasure, List.length_cons]; omega
    have hr := hrec (y :: rest) hrest hlt (by simpa using hsub)
    simp only [sortedStep, DecOpt.checkerBacktrack, hr, DecOpt.andOptList, DecOpt.decOpt,
      hxy, decide_true]
    rfl

/-- **Completeness of the emitted checker**: a sorted list is accepted, given enough of both budgets. -/
theorem instDecOptSorted_complete (fuel i sz : Nat) (xs : List Nat)
    (h : Sorted xs) (hf : xs.length < fuel) (hs : xs.length ≤ sz) :
    instDecOptSorted.aux_dec fuel i sz xs = .ok true := by
  rw [aux_dec_eq]
  exact decRelS_complete (sortedStep_complete i) fuel i sz xs h hf hs

/-! ## Refutation-soundness and decisiveness — the other two of the four-fold

`DecOpt` is three-valued, so "correct" is four claims, not two: `ok true` implies the relation, `ok
false` implies its negation, every `R`-value eventually gets `ok true`, and the verdict is never
`error` given budget. The first two are one-directional and hold unconditionally; the last two need
budgets. -/

theorem sortedStep_refute (i : Nat) : ∀ sz, StepRefute (sortedStep i sz) Sorted := by
  intro sz rec xs hrec hfalse hSorted
  cases sz with
  | zero =>
    -- Vacuous: the `size = 0` case has a `throw` in the recursive slot, and `checkerBacktrack`
    -- reports `ok false` only when EVERY branch does. So it can never say `ok false` here — which is
    -- exactly what the poison flag is for.
    simp only [sortedStep] at hfalse
    have h := checkerBacktrack_ok_false.mp hfalse _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    simp at h
  | succ sz =>
    simp only [sortedStep] at hfalse
    have hall := checkerBacktrack_ok_false.mp hfalse
    cases hSorted with
    | nil => have h := hall _ (List.Mem.head _); simp at h
    | one x => have h := hall _ (List.Mem.tail _ (List.Mem.head _)); simp at h
    | cons x y rest hxy hrest =>
      have h3 := hall _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      simp only at h3
      rcases List.mem_cons.mp (andOptList_ok_false.mp h3) with h | h
      · exact hrec _ h.symm hrest
      · rcases List.mem_cons.mp h with h | h
        · have hd : DecOpt.decOpt (x ≤ y) i = .ok false := h.symm
          simp only [DecOpt.decOpt, hxy, decide_true] at hd
          simp at hd
        · simp at h

/-- **Refutation-soundness of the emitted checker.** -/
theorem instDecOptSorted_refute (fuel i sz : Nat) (xs : List Nat) :
    instDecOptSorted.aux_dec fuel i sz xs = .ok false → ¬ Sorted xs := by
  rw [aux_dec_eq]
  exact decRelS_refute (sortedStep_refute i) fuel i sz xs

theorem sortedStep_decisive (i : Nat) :
    StepDecisiveS (sortedStep i) sortedMeasure sortedMeasure := by
  intro sz rec xs hs hrec
  cases sz with
  | zero =>
    -- `sortedMeasure xs ≤ 0` forces `xs = []`, and that branch answers `ok true`.
    --
    -- Note `checkerBacktrack_isOk` does **not** apply here: it needs *every* branch definite, and the
    -- `size = 0` case has a `throw` in the recursive slot. Definiteness holds for a different reason —
    -- `checkerBacktrack` reports `ok true` as soon as ONE branch does, so it short-circuits before the
    -- error branch matters. Decisiveness at the size floor is a property of the disjunction's
    -- laziness, not of its branches.
    simp only [sortedMeasure, Nat.le_zero, List.length_eq_zero_iff] at hs
    subst hs
    simp only [sortedStep]
    exact ⟨true, checkerBacktrack_ok_true.mpr ⟨_, List.Mem.head _, rfl⟩⟩
  | succ sz =>
    simp only [sortedStep]
    refine checkerBacktrack_isOk ?_
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · cases xs <;> exact ⟨_, rfl⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · match xs with
        | [] => exact ⟨false, rfl⟩
        | [_] => exact ⟨true, rfl⟩
        | _ :: _ :: _ => exact ⟨false, rfl⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · match xs with
          | [] => exact ⟨false, rfl⟩
          | [_] => exact ⟨false, rfl⟩
          | x :: y :: rest =>
            have hsub : sortedMeasure (y :: rest) ≤ sz := by
              simp only [sortedMeasure, List.length_cons] at hs ⊢; omega
            have hlt : sortedMeasure (y :: rest) < sortedMeasure (x :: y :: rest) := by
              simp only [sortedMeasure, List.length_cons]; omega
            obtain ⟨b, hb⟩ := hrec (y :: rest) hlt (by simpa using hsub)
            simp only [hb, DecOpt.andOptList, DecOpt.decOpt]
            cases b <;> exact ⟨_, rfl⟩
        · exact absurd hc (by simp)

/-- **Decisiveness of the emitted checker**: given both budgets the verdict is never `error`. -/
theorem instDecOptSorted_decisive (fuel i sz : Nat) (xs : List Nat)
    (hf : xs.length < fuel) (hs : xs.length ≤ sz) :
    ∃ b, instDecOptSorted.aux_dec fuel i sz xs = .ok b := by
  rw [aux_dec_eq]
  exact decRelS_decisive (sortedStep_decisive i) fuel i sz xs hf hs

-- Pinned: all four directions, so a refactor cannot silently add an axiom. The two that use
-- `Classical.choice` are exactly the two that go through `checkerBacktrack`'s `ok false`
-- characterisation (soundness) or its `isOk` lemma (decisiveness); the two one-directional
-- implications need only `propext`/`Quot.sound`.
/-- info: 'instDecOptSorted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instDecOptSorted_sound

/-- info: 'instDecOptSorted_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms instDecOptSorted_complete

/-- info: 'instDecOptSorted_refute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms instDecOptSorted_refute

/-- info: 'instDecOptSorted_decisive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instDecOptSorted_decisive
