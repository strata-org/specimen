import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.EnumeratorCombinators

/-!
# Semantic domains for the three producers

To state soundness/completeness uniformly we give each producer a **set of outcomes** semantics
(à la QuickChick's `semProd`/`semGen`/`semEnum`) as a predicate `α → Prop`. We deliberately use
`α → Prop` rather than a `Set` type so the development needs no Mathlib.

For each producer we define:
* its outcome predicate (`genSupport`, `enumSupport`, or the boolean verdict for a checker);
* `…Sound`  — every outcome satisfies the specification `P`;
* `…Complete` — every value satisfying `P` is an outcome.

These are the *targets* the generic interpreter theorems will establish. `.ok true`/`.ok false`/
`.error` model the paper's `Some true`/`Some false`/`None` (proved / disproved / out-of-fuel).
-/

open Plausible LazyList

namespace Specimen.Correctness

/-! ## Checkers (`DecOpt`): a fuel-indexed three-valued decision -/

/-- A checker is **sound**: whenever it answers "yes" (`ok true`) at any fuel, `P` holds. -/
def CheckerSound (dec : Nat → Except GenError Bool) (P : Prop) : Prop :=
  ∀ fuel, dec fuel = .ok true → P

/-- A checker is **refutation-sound**: whenever it answers "no" (`ok false`), `P` fails. -/
def CheckerRefute (dec : Nat → Except GenError Bool) (P : Prop) : Prop :=
  ∀ fuel, dec fuel = .ok false → ¬ P

/-- A checker is **complete**: if `P` holds, some fuel makes it answer "yes". -/
def CheckerComplete (dec : Nat → Except GenError Bool) (P : Prop) : Prop :=
  P → ∃ fuel, dec fuel = .ok true

/-- Fuel monotonicity: a definite verdict is preserved as fuel increases. This is the gluing
    lemma (QuickChick's `SizeMonotonic`) that lets sub-checkers at different fuels be combined. -/
def DecOptMonotone (dec : Nat → Except GenError Bool) : Prop :=
  ∀ fuel b, dec fuel = .ok b → dec (fuel + 1) = .ok b

/-- Negative (refutation) completeness: whenever `P` is false, some fuel yields a definite `ok false`.
    This is the direction that fails for general inductive relations (r.e. but not co-r.e.). -/
def CheckerRefuteComplete (dec : Nat → Except GenError Bool) (P : Prop) : Prop :=
  ¬ P → ∃ fuel, dec fuel = .ok false

/-- A checker has **bounded refutation** for `P` when it conclusively decides the *negative*: it never
    wrongly refutes (`CheckerRefute`) and always eventually refutes a true-negative
    (`CheckerRefuteComplete`). This is exactly what a negated premise `¬P` needs from `P`'s checker,
    and the admissibility condition for negated clauses. -/
def RefutesBounded (dec : Nat → Except GenError Bool) (P : Prop) : Prop :=
  CheckerRefute dec P ∧ CheckerRefuteComplete dec P

/-- Any decidable proposition has bounded refutation (the canonical provider): its total two-valued
    decision refutes conclusively in both directions. -/
theorem refutesBounded_of_decidable (P : Prop) [Decidable P] :
    RefutesBounded (fun _ => .ok (decide P)) P := by
  refine ⟨fun _ h => of_decide_eq_false (Except.ok.inj h), fun hnp => ⟨0, ?_⟩⟩
  simp only [Except.ok.injEq]
  exact decide_eq_false_iff_not.mpr hnp

/-- **Decisive at bounded fuel**: once fuel reaches `bound`, the checker returns a definite verdict
    (`ok _`), never `error`. This is the generic essence of "the proof search is bounded / the
    recursion structurally decreases": `bound` is the search-depth needed, and reaching it exhausts
    the search. It is decidability *relative to a measure* — no unbounded existentials, recursion
    well-founded — without committing to how the bound is obtained. -/
def Decisive (dec : Nat → Except GenError Bool) (bound : Nat) : Prop :=
  ∀ fuel, bound ≤ fuel → ∃ b, dec fuel = .ok b

/-- **Generic bridge**: a sound, refutation-sound checker that is decisive at some bound has bounded
    refutation. So `Decisive` (from a structural measure) is a *sufficient* generic condition for a
    negated premise's admissibility — no per-relation refutation-completeness proof is needed beyond
    exhibiting the bound. -/
theorem refutesBounded_of_decisive {dec : Nat → Except GenError Bool} {P : Prop} {bound : Nat}
    (hdec : Decisive dec bound) (hs : CheckerSound dec P) (hr : CheckerRefute dec P) :
    RefutesBounded dec P := by
  refine ⟨hr, fun hnp => ?_⟩
  obtain ⟨b, hb⟩ := hdec bound (Nat.le_refl _)
  cases b with
  | true => exact absurd (hs bound hb) hnp
  | false => exact ⟨bound, hb⟩

/-! ## Enumerators: deterministic, exhaustive lazy enumeration -/

/-- Outcomes of a single (fallible) enumerator at a given `size`: the values `x` for which `ok x`
    appears in the produced lazy list. `error` entries (out-of-fuel / disproved) are not outcomes. -/
def enumSupportAt {α} (e : ExceptT GenError Enumerator α) (size : Nat) (x : α) : Prop :=
  (Except.ok x) ∈ ((ExceptT.run e) size)

/-- Outcomes of a **sized** constrained enumerator: values enumerated at some budget (running the
    enumerator at that same budget, mirroring how `enumST`/`runSizedEnum` are invoked). -/
def enumSupport {α} (es : Nat → ExceptT GenError Enumerator α) (x : α) : Prop :=
  ∃ budget, enumSupportAt (es budget) budget x

/-- Enumerator **soundness**: every enumerated value satisfies `P`. -/
def EnumSound {α} (es : Nat → ExceptT GenError Enumerator α) (P : α → Prop) : Prop :=
  ∀ x, enumSupport es x → P x

/-- Enumerator **completeness**: every value satisfying `P` is enumerated at some budget. -/
def EnumComplete {α} (es : Nat → ExceptT GenError Enumerator α) (P : α → Prop) : Prop :=
  ∀ x, P x → enumSupport es x

/-! ## Generators: randomized production, characterized by support over seeds

`Gen α = StateT (ULift StdGen) (ReaderT (ULift Nat) (Except GenError)) α`. A pure runner threads a
seed and a size and reads off the `Except`-result, discarding the final RNG state. The **support**
`genSupportAt` is the set of values producible for *some* seed — this abstracts away the particular
randomness, exactly as QuickChick's `semGenSize` does. -/

/-- Deterministically run a generator with an explicit `seed` and `size`, keeping only the value. -/
def Gen.runPure {α : Type} (g : Gen α) (seed : StdGen) (size : Nat) : Except GenError α :=
  Except.map Prod.fst (ReaderT.run (StateT.run g (ULift.up seed)) (ULift.up size))

/-- Support of a generator at a fixed `size`: the values producible for some seed. -/
def genSupportAt {α : Type} (g : Gen α) (size : Nat) (x : α) : Prop :=
  ∃ seed, Gen.runPure g seed size = .ok x

/-- Support of a **sized** generator: producible at some budget, running the generator at that same
    budget as its `Gen`-size (mirroring `arbitraryST := Gen.sized (arbitrarySizedST P)`). -/
def genSupport {α : Type} (g : Nat → Gen α) (x : α) : Prop :=
  ∃ size, genSupportAt (g size) size x

/-- Generator **soundness**: every value in the support satisfies `P`. -/
def GenSound {α : Type} (g : Nat → Gen α) (P : α → Prop) : Prop :=
  ∀ x, genSupport g x → P x

/-- Generator **completeness**: every value satisfying `P` is in the support at some budget. -/
def GenComplete {α : Type} (g : Nat → Gen α) (P : α → Prop) : Prop :=
  ∀ x, P x → genSupport g x

/-- Support monotonicity for a sized generator (QuickChick's `SizedMonotonic`): larger budgets only
    add to the support. This is what lets completeness pick "a large enough size". -/
def SizedMonotone {α : Type} (g : Nat → Gen α) : Prop :=
  ∀ s s' x, s ≤ s' → genSupportAt (g s) s x → genSupportAt (g s') s' x

end Specimen.Correctness
