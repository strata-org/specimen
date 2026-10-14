import Specimen.Correctness.Semantics

/-!
# Generic relation-level generator interpreter (soundness)

The randomized producer analogue of `decRel`/`enumRel`: a generator is the fuel-iteration of a
one-level `GenStep` over the real `Plausible.Gen`, bottoming at `failGen` (`throw`). Soundness —
everything in the support satisfies `P` — is the assumption-free direction (mirrors `enumRel_sound`
using the support predicate `genSupportAt` instead of `List` membership); it needs no RNG axiom.

**Completeness is not proved at `Plausible.Gen`.** It is a reachability claim — some seed yields the
value — and over Plausible's opaque `StdGen` the only route is `GenAxioms`' postulated support laws plus
a size-monotonicity assumption (`SizedMonotone`). Completeness is instead proved for generators read at
Basalt's `SPMF`, with no generator axioms, in `GenInterpSPMF` (the `proofs/` package, which needs
Mathlib).
-/

open Plausible

namespace Specimen.Correctness

variable {A : Type}

/-- One-level generator step: extend the previous fuel-level's generator. -/
abbrev GenStep (A : Type) := Gen A → Gen A

/-- The empty generator (produces nothing). -/
def failGen : Gen A := throw (.genError "out of fuel")

/-- `failGen` has empty support. -/
theorem genSupportAt_failGen (sz : Nat) (x : A) : ¬ genSupportAt (failGen : Gen A) sz x := by
  rintro ⟨seed, h⟩
  rw [show Gen.runPure (failGen : Gen A) seed sz = .error (.genError "out of fuel") from rfl] at h
  simp at h

/-- Full generator: fuel-iterate the one-level step from `failGen`. -/
def genRel (step : GenStep A) : Nat → Gen A
  | 0 => failGen
  | fuel + 1 => step (genRel step fuel)

/-- Outcomes of the generator: values in the support at some fuel (size = fuel). -/
def semGenRel (step : GenStep A) (x : A) : Prop :=
  ∃ fuel, genSupportAt (genRel step fuel) fuel x

/-- `step` preserves the specification over the support (at every size). -/
def StepGenSound (step : GenStep A) (P : A → Prop) : Prop :=
  ∀ prev, (∀ sz x, genSupportAt prev sz x → P x) → ∀ sz x, genSupportAt (step prev) sz x → P x

/-- Generator soundness, per fuel and size. -/
theorem genRel_mem_sound {step : GenStep A} {P : A → Prop} (h : StepGenSound step P) :
    ∀ (fuel sz : Nat) (x : A), genSupportAt (genRel step fuel) sz x → P x
  | 0, sz, x => fun hx => absurd hx (genSupportAt_failGen sz x)
  | fuel + 1, sz, x => fun hx =>
    h (genRel step fuel) (fun sz' x' hx' => genRel_mem_sound h fuel sz' x' hx') sz x hx

/-- **Generic generator soundness**: every value in the support satisfies `P`. Assumption-free
    (no RNG axiom) — soundness only inspects one concrete run, not full reachability. -/
theorem genRel_sound {step : GenStep A} {P : A → Prop} (h : StepGenSound step P) :
    ∀ x, semGenRel step x → P x :=
  fun _ ⟨fuel, hx⟩ => genRel_mem_sound h fuel fuel _ hx

end Specimen.Correctness
