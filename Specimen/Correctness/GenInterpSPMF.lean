import Specimen.Correctness.Semantics
import Basalt.SPMF.Backtrack

/-!
# Generic relation-level generator interpreter, at Basalt's `SPMF` — no generator axioms

The randomized analogue of `decRel`/`enumRel`, and the third leg of the correctness development.
`GenInterp` proved generic generator *soundness* over the real `Plausible.Gen`, but could not prove
completeness: reachability over an opaque `StdGen` is not provable, so `GenAxioms` postulates two
QuickChick-style support laws (`genSupportAt_bind`, `genSupportAt_backtrack`).

A generator emitted under `specimen.emitBasalt` is polymorphic in Basalt's `Gen` class, so the same
definition can be read at Basalt's `SPMF`, a sub-probability distribution, where its *support* — the
values it produces with nonzero probability — is what the theorems below are about. There:

* the bind law is `SPMF.mem_support_bind_iff`, and
* the backtrack law is `BacktrackGen.mem_support_backtrack_ok_iff`.

Both are theorems. So the results below — soundness **and** completeness — carry no generator axioms
(their axioms are Lean's standard `propext`, `Classical.choice`, `Quot.sound`; `SPMF` is classical).
`GenInterp` still says something this file does not: that soundness holds of the code as it actually
runs under Plausible. The two are readings of the same emitted definition.

## The two budgets

Emitted generators take `fuel`, `initSize` and `size`, and the shape of a completeness statement is
forced by how they use them (see `StlcCompleteness`, where this was worked out concretely first):

* **fuel** is the termination backstop — it only has to exceed the derivation's *depth*;
* **size** is the search budget, and it is what branches actually spend: the emitter decrements it
  for linear constructors and *halves* it for the branching ones.

So a step is given the previous fuel level not as a single generator but as a **family indexed by
size**, letting each branch recurse at whatever size it likes. Completeness is then stated against a
pair of measures — `φ` for fuel, `σ` for size — rather than the single measure `enumRel_complete`
needs.

## Why completeness is conditional

It has to be: the default weight function gives a recursive constructor weight `0` at `size = 0`, so
recursive branches are genuinely dead at small sizes and *no* unconditional statement is true. `σ` is
where that shows up — a faithful `σ` for a halving constructor doubles, and its floor is the
dead-recursion bound.
-/

namespace Specimen.Correctness

variable {k : ProducerKind} {I A : Type}

/-- A producer at the `SPMF` interpretation, at either kind.

The *carrier* is pinned to `SPMF` because `Produces` is a statement about support. The *kind* is not
pinned: everything below that depends only on `Monad` — the `Outcome` algebra and the whole
fuel-iteration interpreter — is stated once and serves generators and enumerators alike. Only the
branch combinator is kind-specific. -/
abbrev SProducer (k : ProducerKind) (A : Type) := Producer k SPMF A

/-- The generator specialisation. Emitted generator code and every bridge mentions this, so it stays a
name of its own rather than an inlined `SProducer .gen`. -/
abbrev SGen (A : Type) := SProducer .gen A

/-- `x` is producible by `g`. Note the `Outcome.ok`: a generator that reliably *fails* has empty
support in this sense, which is what makes soundness non-trivial. -/
def Produces (g : SProducer k A) (x : A) : Prop := Outcome.ok x ∈ g.run.support

/-- Nothing is producible from `exhaust` — the fuel floor. -/
theorem not_produces_exhaust (x : A) : ¬ Produces (Producer.exhaust : SProducer k A) x := by
  simp [Produces, Producer.exhaust]

/-- Likewise for `refute`; both failures are unproductive, they differ only in what they *claim*. -/
theorem not_produces_refute (x : A) : ¬ Produces (Producer.refute : SProducer k A) x := by
  simp [Produces, Producer.refute]

/-! ### `Produces` algebra

Every branch obligation in every bridge decomposes the same three ways — through a `bind`, a `pure`,
and a `liftGen`. Proving them once here is what keeps the per-branch proofs about the *relation*
rather than about the support monad.

Note what `produces_bind` does with failure: a `bind` whose first component fails cannot produce
anything, so the existential witness is always an `ok`. That is the whole content of `BacktrackGen`'s
short-circuiting, and it is why branch proofs never have to mention `refuted`/`exhausted`. -/

/-- The support of a producer `bind`, outcome by outcome. -/
theorem mem_support_run_bind {A B : Type} {g : SProducer k A} {f : A → SProducer k B}
    {o : Outcome B} :
    o ∈ (g >>= f).run.support ↔
      (∃ a, Outcome.ok a ∈ g.run.support ∧ o ∈ (f a).run.support) ∨
      (Outcome.refuted ∈ g.run.support ∧ o = .refuted) ∨
      (Outcome.exhausted ∈ g.run.support ∧ o = .exhausted) := by
  change o ∈ (g.run >>= fun r => match r with
    | .ok a => (f a).run | .refuted => pure .refuted | .exhausted => pure .exhausted).support ↔ _
  rw [SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨r, hr, ho⟩
    cases r with
    | ok a => exact .inl ⟨a, hr, ho⟩
    | refuted => exact .inr (.inl ⟨hr, SPMF.mem_support_pure_iff.mp ho⟩)
    | exhausted => exact .inr (.inr ⟨hr, SPMF.mem_support_pure_iff.mp ho⟩)
  · rintro (⟨a, ha, ho⟩ | ⟨hr, rfl⟩ | ⟨hr, rfl⟩)
    · exact ⟨_, ha, ho⟩
    · exact ⟨_, hr, SPMF.mem_support_pure_iff.mpr rfl⟩
    · exact ⟨_, hr, SPMF.mem_support_pure_iff.mpr rfl⟩

/-- Decompose a successful `bind`. -/
theorem produces_bind {A B : Type} {g : SProducer k A} {f : A → SProducer k B} {b : B}
    (h : Produces (g >>= f) b) : ∃ a, Produces g a ∧ Produces (f a) b := by
  rcases mem_support_run_bind.mp h with h | ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · cases h
  · cases h

/-- Build a successful `bind`. -/
theorem produces_bind_of {A B : Type} {g : SProducer k A} {f : A → SProducer k B} {a : A} {b : B}
    (ha : Produces g a) (hb : Produces (f a) b) : Produces (g >>= f) b :=
  mem_support_run_bind.mpr (.inl ⟨a, ha, hb⟩)

@[simp] theorem produces_bind_iff {A B : Type} {g : SProducer k A} {f : A → SProducer k B} {b : B} :
    Produces (g >>= f) b ↔ ∃ a, Produces g a ∧ Produces (f a) b :=
  ⟨produces_bind, fun ⟨_, ha, hb⟩ => produces_bind_of ha hb⟩

@[simp] theorem produces_pure_iff {A : Type} {a b : A} :
    Produces (pure a : SProducer k A) b ↔ b = a := by
  simp only [Produces, Producer.run_pure, SPMF.mem_support_pure_iff, Outcome.ok.injEq]

/-- `liftGen` produces exactly what the underlying generator's support contains. -/
@[simp] theorem produces_liftGen_iff {A : Type} {g : SPMF A} {a : A} :
    Produces (BacktrackGen.liftGen g) a ↔ a ∈ g.support := by
  simp only [Produces, BacktrackGen.liftGen, Producer.run_lift, SPMF.mem_support_bind_iff,
    SPMF.mem_support_pure_iff, Outcome.ok.injEq]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · exact fun h => ⟨a, h, rfl⟩

/-- Every outcome a lifted generator can produce is a success. -/
theorem mem_support_liftGen_cases {A : Type} {g : SPMF A} {o : Outcome A}
    (h : o ∈ (BacktrackGen.liftGen g).run.support) : ∃ a, o = Outcome.ok a := by
  simp only [BacktrackGen.liftGen, Producer.run_lift, SPMF.mem_support_bind_iff,
    SPMF.mem_support_pure_iff] at h
  obtain ⟨a, _, rfl⟩ := h
  exact ⟨a, rfl⟩

/-- One-level generator step, over inputs `I` and outputs `A`.

`prev` is the previous fuel level **as a family over size *and input***. Both indices are needed to
model emitted code: a branch may recurse at `size - 1` or `size / 2` (the emitter halves at branching
constructors), and it almost always recurses at a *different input* — the `lookup` generator walks
`Γ`'s tail, `typing`'s `TAbs` extends the context. A step over a single `SGen A` cannot express
either, which is why this is indexed rather than closed over its arguments.

`initSize` needs no index: it is threaded unchanged through every emitted recursive call, so a
concrete step just closes over it. -/
abbrev SProducerStep (k : ProducerKind) (I A : Type) :=
  (Nat → I → SProducer k A) → Nat → I → SProducer k A

/-- Generator specialisation of `SProducerStep`. -/
abbrev SGenStep (I A : Type) := SProducerStep .gen I A

/-- Full generator: fuel-iterate the one-level step, bottoming out at `exhaust`. This is exactly the
emitted `match fuel with | 0 => exhaust | fuel+1 => …` skeleton.

`noncomputable` because `SPMF` is — the support interpretation is a reasoning device, not something
to run. The emitted definition it models is executable at `Plausible.Gen`. -/
noncomputable def genRelB (step : SProducerStep k I A) : Nat → Nat → I → SProducer k A
  | 0, _, _ => Producer.exhaust
  | fuel + 1, size, i => step (genRelB step fuel) size i

/-- Everything producible from input `i` at some fuel and size. -/
def semGenRelB (step : SProducerStep k I A) (i : I) (x : A) : Prop :=
  ∃ fuel size, Produces (genRelB step fuel size i) x

/-- `step` preserves the specification: if the previous level only produced `P`-related values, so
does this one. `P` relates an input to a legal output — it is the relation being derived from. -/
def StepGenSoundB (step : SProducerStep k I A) (P : I → A → Prop) : Prop :=
  ∀ prev, (∀ sz i x, Produces (prev sz i) x → P i x) →
    ∀ sz i x, Produces (step prev sz i) x → P i x

/-- `step` is **complete relative to the measure pair** `(φ, σ)`: given `P i a`, enough size, and a
previous level that already reaches every `P`-pair of strictly smaller fuel measure (at any sufficient
size), the step reaches `a` from `i`.

The measures range over input *and* output because a recursive call may shrink either — `lookup`
shrinks both, but a relation whose output is fixed-size shrinks only the input. -/
def StepGenCompleteB (step : SProducerStep k I A) (P : I → A → Prop) (φ σ : I → A → Nat) : Prop :=
  ∀ prev sz i a, P i a → σ i a ≤ sz →
    (∀ j b, P j b → φ j b < φ i a → ∀ sz', σ j b ≤ sz' → Produces (prev sz' j) b) →
    Produces (step prev sz i) a

theorem genRelB_produces_sound {step : SProducerStep k I A} {P : I → A → Prop}
    (h : StepGenSoundB step P) :
    ∀ (fuel sz : Nat) (i : I) (x : A), Produces (genRelB step fuel sz i) x → P i x
  | 0, _, _, x => fun hx => absurd hx (not_produces_exhaust x)
  | fuel + 1, sz, i, x => fun hx =>
    h (genRelB step fuel)
      (fun sz' i' x' hx' => genRelB_produces_sound h fuel sz' i' x' hx') sz i x hx

/-- **Generic generator soundness.** -/
theorem genRelB_sound {step : SProducerStep k I A} {P : I → A → Prop} (h : StepGenSoundB step P) :
    ∀ i x, semGenRelB step i x → P i x :=
  fun _ _ ⟨fuel, sz, hx⟩ => genRelB_produces_sound h fuel sz _ _ hx

/-- **Generic generator completeness.** Induction on fuel alone suffices: the step's own hypothesis
already restricts the recursive appeal to strictly smaller `φ`, and `φ a < fuel + 1` bounds it. -/
theorem genRelB_complete {step : SProducerStep k I A} {P : I → A → Prop} {φ σ : I → A → Nat}
    (h : StepGenCompleteB step P φ σ) :
    ∀ (fuel : Nat) (i : I) (a : A), P i a → φ i a < fuel → ∀ sz, σ i a ≤ sz →
      Produces (genRelB step fuel sz i) a := by
  intro fuel
  induction fuel with
  | zero => intro i a _ hf; exact absurd hf (by omega)
  | succ fuel ih =>
    intro i a hPa hf sz hs
    exact h (genRelB step fuel) sz i a hPa hs
      (fun j b hPb hlt sz' hs' => ih j b hPb (by omega) sz' hs')

/-! ### Turning a failed search into a refutation

A failure verdict cannot do this on its own. `Outcome.exhausted` has three sources in emitted code — the
fuel backstop tripping, a `size = 0` truncated disjunction, and a premise checker answering
inconclusively — and only the middle one involves a search that actually completed. So reading
`exhausted` as "nothing exists within this budget" is unsound in general.

What *is* sound uses only the **absence of a success**, plus completeness. These two lemmas separate the
honest part from the part that needs an extra assumption, and neither inspects the failure constructor. -/

/-- Producing nothing does not refute — it **bounds the witnesses**. Any `a` satisfying `P` must exceed
one of the two budgets. This is just the contrapositive of completeness, and it is the strongest
conclusion available from a failed search alone. -/
theorem witness_exceeds_budget_of_not_produces {step : SProducerStep k I A} {P : I → A → Prop}
    {φ σ : I → A → Nat} (h : StepGenCompleteB step P φ σ) (i : I) (fuel sz : Nat)
    (hno : ∀ a, ¬ Produces (genRelB step fuel sz i) a) :
    ∀ a, P i a → ¬ (φ i a < fuel ∧ σ i a ≤ sz) := by
  intro a hPa hb
  exact hno a (genRelB_complete h fuel i a hPa hb.1 sz hb.2)

/-- With a bound saying every witness *would* have fitted in the budget, producing nothing **does**
refute. That bound is where the "the search was exhaustive" claim belongs — as a hypothesis about the
budget covering the relation, rather than as a reading of a verdict constructor.

Note what is *not* needed: no assumption about which failure was returned, so a fuel-truncated run cannot
silently invalidate the conclusion. `hbound` already rules that out by requiring `φ i a < fuel`. -/
theorem refutes_of_not_produces {step : SProducerStep k I A} {P : I → A → Prop}
    {φ σ : I → A → Nat} (h : StepGenCompleteB step P φ σ) (i : I) (fuel sz : Nat)
    (hbound : ∀ a, P i a → φ i a < fuel ∧ σ i a ≤ sz)
    (hno : ∀ a, ¬ Produces (genRelB step fuel sz i) a) :
    ∀ a, ¬ P i a :=
  fun a hPa => witness_exceeds_budget_of_not_produces h i fuel sz hno a hPa (hbound a hPa)

/-- Corollary in the form a caller wants: pick fuel and size from the measures. -/
theorem genRelB_complete' {step : SProducerStep k I A} {P : I → A → Prop} {φ σ : I → A → Nat}
    (h : StepGenCompleteB step P φ σ) (i : I) (a : A) (hPa : P i a) :
    Produces (genRelB step (φ i a + 1) (σ i a) i) a :=
  genRelB_complete h (φ i a + 1) i a hPa (by omega) (σ i a) (by omega)

/-! ## Monotonicity in fuel

`Semantics.lean` declares `SizedMonotone` — QuickChick's `SizedMonotonic` — as a target for
`Plausible.Gen` generators but never proves it. This is the `SPMF` analogue for the fuel axis, and it is
the law that justifies the thing every testing loop assumes: raising the budget never *loses* a value it
could already produce.

It needs a hypothesis, because `genRelB` is only as monotone as its step: a step is free to inspect the
previous level and behave non-monotonically. `StepGenMono` rules that out, and `stepBacktrackB_mono`
discharges it branch-wise for the shape the emitter actually produces. -/

/-- `step` turns a support-increasing change of `prev` into a support-increasing change of its own
output. -/
def StepGenMono (step : SProducerStep k I A) : Prop :=
  ∀ (prev prev' : Nat → I → SProducer k A),
    (∀ sz i x, Produces (prev sz i) x → Produces (prev' sz i) x) →
    ∀ sz i x, Produces (step prev sz i) x → Produces (step prev' sz i) x

/-- **More fuel never loses a value.** -/
theorem genRelB_fuel_mono {step : SProducerStep k I A} (h : StepGenMono step) :
    ∀ (fuel fuel' : Nat), fuel ≤ fuel' → ∀ (sz : Nat) (i : I) (x : A),
      Produces (genRelB step fuel sz i) x → Produces (genRelB step fuel' sz i) x := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ x hx; exact absurd hx (not_produces_exhaust x)
  | succ fuel ih =>
    intro fuel' hle sz i x hx
    cases fuel' with
    | zero => exact absurd hle (by omega)
    | succ fuel' =>
      exact h (genRelB step fuel) (genRelB step fuel')
        (fun sz' i' x' hx' => ih fuel' (by omega) sz' i' x' hx') sz i x hx

/-! ## Relation-level assembly

The emitted code is always `BacktrackGen.backtrack` over one branch per constructor, each a function
of `Unit` so only the selected branch is built, so the two `Step*` obligations above reduce to
per-branch obligations. This is the generator counterpart of `stepBacktrack_sound`/`stepBacktrack_refute`
in `CheckerInterp.lean`.

The asymmetry between the two directions is the point. Soundness needs **every** branch to be sound,
because any one of them might be the one that fired. Completeness needs only **some** branch to cover
`a`, and additionally that its weight is positive — which is exactly where the `size == 0` dead
recursion bites, and why the weight side-condition cannot be dropped. -/

/-- Branch lists as the emitter produces them: dependent on `prev`, `size` and the input. -/
abbrev BranchList (I A : Type) := (Nat → I → SGen A) → Nat → I → List (Nat × (Unit → SGen A))

/-- The step built by backtracking over the branch list. -/
noncomputable def stepBacktrackB (branches : BranchList I A) : SGenStep I A :=
  fun prev sz i => BacktrackGen.backtrack (branches prev sz i)

/-- Soundness reduces to: *every* branch is sound. -/
theorem stepBacktrackB_sound {branches : BranchList I A} {P : I → A → Prop}
    (hbr : ∀ prev, (∀ sz i x, Produces (prev sz i) x → P i x) →
      ∀ sz i p, p ∈ branches prev sz i → ∀ x, Produces (p.2 ()) x → P i x) :
    StepGenSoundB (stepBacktrackB branches) P := by
  intro prev hprev sz i x hx
  obtain ⟨p, hp, _, hpx⟩ := BacktrackGen.mem_support_backtrack_ok _ _ hx
  exact hbr prev hprev sz i p hp x hpx

/-- Completeness reduces to: *some* positively-weighted branch covers `a`. -/
theorem stepBacktrackB_complete {branches : BranchList I A} {P : I → A → Prop}
    {φ σ : I → A → Nat}
    (hbr : ∀ prev sz i a, P i a → σ i a ≤ sz →
      (∀ j b, P j b → φ j b < φ i a → ∀ sz', σ j b ≤ sz' → Produces (prev sz' j) b) →
      ∃ p ∈ branches prev sz i, 0 < p.1 ∧ Produces (p.2 ()) a) :
    StepGenCompleteB (stepBacktrackB branches) P φ σ := by
  intro prev sz i a hPa hs hrec
  obtain ⟨p, hp, hpos, hpa⟩ := hbr prev sz i a hPa hs hrec
  exact BacktrackGen.mem_support_backtrack_of_branch _ p hp hpos _ hpa

/-- Monotonicity reduces to: whatever a branch produced under `prev`, *some* positively-weighted branch
still produces under `prev'`. Usually the corresponding branch, but the statement does not require it —
which matters because the branch *list* may itself depend on `prev`.

`BacktrackGen.mem_support_backtrack_ok` returns the witnessing branch *live* (`0 < p.1`), so the caller
may assume the source branch had positive weight — without that, the obligation would be unprovable for
a branch whose weight is `0` at `size = 0`, exactly the case the default weight function creates. -/
theorem stepBacktrackB_mono {branches : BranchList I A}
    (hbr : ∀ prev prev', (∀ sz i x, Produces (prev sz i) x → Produces (prev' sz i) x) →
      ∀ sz i p, p ∈ branches prev sz i → 0 < p.1 → ∀ x, Produces (p.2 ()) x →
        ∃ q ∈ branches prev' sz i, 0 < q.1 ∧ Produces (q.2 ()) x) :
    StepGenMono (stepBacktrackB branches) := by
  intro prev prev' hmono sz i x hx
  obtain ⟨p, hp, hp0, hpx⟩ := BacktrackGen.mem_support_backtrack_ok _ _ hx
  obtain ⟨q, hq, hq0, hqx⟩ := hbr prev prev' hmono sz i p hp hp0 x hpx
  exact BacktrackGen.mem_support_backtrack_of_branch _ q hq hq0 _ hqx

/-- The emitted `size = 0` case wraps its (truncated) branch list in `refutedToExhausted`, which
changes only the *failure* verdict, never the successes — so it is invisible to both soundness and
completeness. Without this the `size = 0` case of real emitted code would not fit the interpreter. -/
@[simp] theorem produces_refutedToExhausted_iff (g : SProducer k A) (x : A) :
    Produces (Producer.refutedToExhausted g) x ↔ Produces g x :=
  BacktrackGen.mem_support_refutedToExhausted_ok_iff _ _

/-! ## Mutually recursive modes

`derive_mutual` emits a *family* of generators, not one: `typing` gets a mode with the type as input
and a mode with the type as an output, and each mode's `TApp` branch calls the other. `genRelB` cannot
express that — its `prev` has a single input and output type.

The fix is to index everything by a mode `M`, with per-mode input and output types. Mutual recursion is
then just the ordinary recursion of a single interpreter over a family, and the fuel argument is shared
across modes, which is exactly how the emitted `mutual` block threads it.

`genRelB` is the `M = Unit` case; it is kept separate because the non-dependent form is much pleasanter
for single relations, which are the common case. -/

section Family

variable {M : Type} {I A : M → Type}

/-- One-level step over a family of modes. `prev` is now indexed by mode as well as size and input. -/
abbrev FamStep (M : Type) (I A : M → Type) :=
  ((m : M) → Nat → I m → SGen (A m)) → (m : M) → Nat → I m → SGen (A m)

/-- Fuel-iterate a family step. One fuel counter for all modes — as in the emitted `mutual` block. -/
noncomputable def genRelFam (step : FamStep M I A) : Nat → (m : M) → Nat → I m → SGen (A m)
  | 0, _, _, _ => BacktrackGen.exhaust
  | fuel + 1, m, size, i => step (genRelFam step fuel) m size i

/-- Specification for a family: per mode, which outputs are legal for which inputs. -/
abbrev FamSpec (M : Type) (I A : M → Type) := (m : M) → I m → A m → Prop

def StepFamSoundB (step : FamStep M I A) (P : FamSpec M I A) : Prop :=
  ∀ prev, (∀ m sz i x, Produces (prev m sz i) x → P m i x) →
    ∀ m sz i x, Produces (step prev m sz i) x → P m i x

/-- Completeness for a family. The fuel measure `φ` is compared **across modes** — that is what makes
mutual recursion sound to unfold: mode 1's `TApp` appeals to mode 2 at a strictly smaller `φ`, so
neither mode's obligation is circular. -/
def StepFamCompleteB (step : FamStep M I A) (P : FamSpec M I A)
    (φ σ : (m : M) → I m → A m → Nat) : Prop :=
  ∀ prev m sz i a, P m i a → σ m i a ≤ sz →
    (∀ m' j b, P m' j b → φ m' j b < φ m i a → ∀ sz', σ m' j b ≤ sz' → Produces (prev m' sz' j) b) →
    Produces (step prev m sz i) a

theorem genRelFam_produces_sound {step : FamStep M I A} {P : FamSpec M I A}
    (h : StepFamSoundB step P) :
    ∀ (fuel : Nat) (m : M) (sz : Nat) (i : I m) (x : A m),
      Produces (genRelFam step fuel m sz i) x → P m i x
  | 0, _, _, _, x => fun hx => absurd hx (not_produces_exhaust x)
  | fuel + 1, m, sz, i, x => fun hx =>
    h (genRelFam step fuel)
      (fun m' sz' i' x' hx' => genRelFam_produces_sound h fuel m' sz' i' x' hx') m sz i x hx

/-- **Generic soundness for a mutual family.** -/
theorem genRelFam_sound {step : FamStep M I A} {P : FamSpec M I A} (h : StepFamSoundB step P)
    (m : M) (i : I m) (x : A m) (hx : ∃ fuel sz, Produces (genRelFam step fuel m sz i) x) :
    P m i x :=
  let ⟨fuel, sz, hx⟩ := hx
  genRelFam_produces_sound h fuel m sz i x hx

/-- **Generic completeness for a mutual family.** Still a single induction on fuel: because `φ`
decreases across modes, one counter suffices for the whole family. -/
theorem genRelFam_complete {step : FamStep M I A} {P : FamSpec M I A}
    {φ σ : (m : M) → I m → A m → Nat} (h : StepFamCompleteB step P φ σ) :
    ∀ (fuel : Nat) (m : M) (i : I m) (a : A m), P m i a → φ m i a < fuel →
      ∀ sz, σ m i a ≤ sz → Produces (genRelFam step fuel m sz i) a := by
  intro fuel
  induction fuel with
  | zero => intro m i a _ hf; exact absurd hf (by omega)
  | succ fuel ih =>
    intro m i a hPa hf sz hs
    exact h (genRelFam step fuel) m sz i a hPa hs
      (fun m' j b hPb hlt sz' hs' => ih m' j b hPb (by omega) sz' hs')

end Family

end Specimen.Correctness
