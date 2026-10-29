import Specimen.Correctness.Semantics

/-!
# Generic relation-level producer interpreter (enumerator)

The producer analogue of `CheckerInterp`, for the deterministic case: an enumerator is the
fuel-iteration of a one-level `EnumStep` that extends the previous level's enumeration with values
producible in one more step. Values are ordinary `List A` (the finite enumeration at each fuel),
sidestepping `LazyList`'s `partial` bind — the real `LazyList` enumerator connects via `fromList`
(see `LazyListLemmas`, as in the `Ev` enumerator slice).

Mirrors `decRel` beat-for-beat:
* `enumRel_sound`   — a step that preserves `P` ⟹ every enumerated value satisfies `P`;
* `enumRel_complete` — a **measure-guarded** step ⟹ every `P`-value is enumerated (structurally
  decreasing; no monotonicity needed, all smaller values share the outer fuel).

## Why there is no enumerator *adequacy bridge*, and what it would take

The generator leg has one: `DerivedGeneratorViaInterp` in the `proofs/` package proves the emitted
generator is *literally* `genRelB` at a particular step, by induction on fuel with every case `rfl` or a
rewrite by the induction hypothesis. `TypingBridge` does the same for a mutually recursive pair. Nothing
comparable is possible for the enumerator, and the reason is worth recording because it is not a gap in
this file.

The generator bridge is cheap **because of the Basalt port**. Basalt makes generators polymorphic over
an abstract `Gen` class, so the *same* emitted definition can be read at Basalt's `SPMF`, where its
support is what the proofs are about, and the interpreter can be stated as an equation between terms of
the same type.

Enumerators have no such class. They are hard-wired to `ExceptT GenError Enumerator`, i.e.
`Nat → LazyList (Except GenError α)`, so:

1. There is no interpretation at which an emitted enumerator and a `List`-based `enumRel` inhabit the
   same type. The best available statement is a *membership correspondence*, not an identity.
2. The correspondence cannot be proved by unfolding. `LazyList`'s bind is
   `bindLazyList l f = roundRobinConcat (f <$> l)`, and while both have `eq_def`, `roundRobinConcat`
   reduces to an inner `go` that recurses through `Thunk.get` — not structurally, hence `partial`.
   Verified: `LazyList.roundRobinConcat.go.eq_def` and `LazyList.roundRobinConcat.induct` **do not
   exist**. The recursion that does the work is opaque, so there is no induction to do.

Hence the `fromList` strategy: keep the development over `List`, where induction is available, and
cross to `LazyList` only at the membership boundary (`LazyListLemmas.mem_fromList`). That is sound and
is what the `Ev` enumerator slice does, but it proves things about a `List` model rather than about the
emitted term.

The fix is the same medicine Basalt applied to generators: give enumerators an abstract class with a
`List`/multiset interpretation. Then `enumerate` becomes an equationally-reasonable combinator, the
`partial` round-robin becomes one *interpretation* rather than the definition, and the enumerator gets
the same `rfl`-style bridge. Until then, "enumerator soundness/completeness" means it of the model.

One structural difference in the emitted enumerator that a future bridge does *not* have to handle:
`enumerate` takes an **unweighted** list and runs every branch exactly once, so there is no analogue of
the generator's `size == 0` dead-recursion problem — the size-0 case simply omits the recursive
branches. Completeness therefore needs a size bound but no weight-positivity side condition.
-/

namespace Specimen.Correctness

variable {A : Type}

/-- One-level enumerator step: given the previous level's enumeration, produce this level's. -/
abbrev EnumStep (A : Type) := List A → List A

/-- Full enumerator: fuel-iterate the one-level step from the empty enumeration. -/
def enumRel (step : EnumStep A) : Nat → List A
  | 0 => []
  | fuel + 1 => step (enumRel step fuel)

/-- Outcomes of the enumerator: values produced at some fuel. -/
def semEnumRel (step : EnumStep A) (x : A) : Prop := ∃ fuel, x ∈ enumRel step fuel

/-- `step` preserves the specification: if every previously-enumerated value satisfies `P`, so does
    every value it adds. -/
def StepEnumSound (step : EnumStep A) (P : A → Prop) : Prop :=
  ∀ prev, (∀ x ∈ prev, P x) → ∀ x ∈ step prev, P x

/-- `step` is **measure-guarded complete**: given `P a` and that every strictly-smaller-measure
    `P`-value is already in `prev`, `step` produces `a`. This is "recursive premises structurally
    decrease `μ`" for producers. -/
def StepEnumComplete (step : EnumStep A) (P : A → Prop) (μ : A → Nat) : Prop :=
  ∀ prev a, P a → (∀ a', μ a' < μ a → P a' → a' ∈ prev) → a ∈ step prev

/-- Enumerator soundness, per fuel. -/
theorem enumRel_mem_sound {step : EnumStep A} {P : A → Prop} (h : StepEnumSound step P) :
    ∀ (fuel : Nat) (x : A), x ∈ enumRel step fuel → P x
  | 0, x => by intro hx; simp [enumRel] at hx
  | fuel + 1, x => fun hx =>
    h (enumRel step fuel) (fun y hy => enumRel_mem_sound h fuel y hy) x hx

/-- **Generic enumerator soundness**: everything enumerated satisfies `P`. -/
theorem enumRel_sound {step : EnumStep A} {P : A → Prop} (h : StepEnumSound step P) :
    ∀ x, semEnumRel step x → P x :=
  fun _ ⟨fuel, hx⟩ => enumRel_mem_sound h fuel _ hx

theorem enumRel_complete_aux {step : EnumStep A} {P : A → Prop} {μ : A → Nat}
    (h : StepEnumComplete step P μ) :
    ∀ (fuel : Nat) (a : A), μ a < fuel → P a → a ∈ enumRel step fuel
  | 0, a, hlt, _ => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, a, hlt, hP =>
    h (enumRel step fuel) a hP (fun a' ha' hP' => enumRel_complete_aux h fuel a' (by omega) hP')

/-- **Generic enumerator completeness** for structurally-decreasing relations: every `P`-value is
    enumerated (at fuel `μ a + 1`). No monotonicity — smaller values share the outer fuel. -/
theorem enumRel_complete {step : EnumStep A} {P : A → Prop} {μ : A → Nat}
    (h : StepEnumComplete step P μ) : ∀ a, P a → semEnumRel step a :=
  fun a hP => ⟨μ a + 1, enumRel_complete_aux h (μ a + 1) a (Nat.lt_succ_self _) hP⟩

end Specimen.Correctness
