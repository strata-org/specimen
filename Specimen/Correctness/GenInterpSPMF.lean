import Specimen.Correctness.Semantics
import Specimen.BasaltClasses
import Basalt.BacktrackWith
import Basalt.OptionT
import Basalt.Enum.BacktrackWithLaws

/-!
# Generic relation-level generator interpreter, at Basalt's `SPMF`

The randomized analogue of `decRel`/`enumRel`, and the third leg of the correctness development.
`GenInterp` proves generic generator *soundness* over the real `Plausible.Gen` but not completeness,
which needs the reverse support laws: `Plausible.Gen` threads its seed through `>>=` rather than
splitting it, so those laws fail there (see `GenSupport`).

A generator emitted under `specimen.emitBasalt` is polymorphic in its generator monad, so the same
definition can be read at `SGen`, Basalt's `SPMF` with a refutation (`OptionT`) and a labelled failure
(`ExceptT Exhaustion`) on top: the sampler's own monad, with `SPMF` where the sampler draws. Its
*successes* — the values it produces with nonzero probability — are what the theorems below are about.
There:

* the bind law is `SPMF.mem_support_bind_iff`, through the two transformers, and
* the backtrack law is `Basalt.Backtrack.mem_support_searchWith_ok` and its converse.

Both are theorems, so the results below, soundness **and** completeness, use only Lean's standard
axioms `propext`, `Classical.choice` and `Quot.sound` (`SPMF` is classical).
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

namespace Specimen

/-- The labels in the order the sampler joins them by: the `max` of `Specimen.Exhaustion` is this
lattice's join, so Basalt's laws about the search apply to the instance derived code runs at. -/
instance : SemilatticeSup Exhaustion where
  le a b := a.rank ≤ b.rank
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm a b h₁ h₂ := by cases a <;> cases b <;> simp_all [Exhaustion.rank]
  sup := max
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide

end Specimen

namespace Specimen.Correctness

variable {I A : Type}

/-- A derived generator at the `SPMF` interpretation: the monad it runs at under Plausible, with
`SPMF` in place of Plausible's `Gen`. -/
abbrev SGen (A : Type) := ExceptT Exhaustion (OptionT SPMF) A

/-- `x` is producible by `g`: a success in its support. A generator that reliably *fails* has empty
support in this sense, which is what makes soundness non-trivial. -/
def Produces (g : SGen A) (x : A) : Prop := some (.ok x) ∈ g.run.run.support

/-- Nothing is producible when the fuel runs out — the fuel floor. -/
theorem not_produces_outOfFuel (x : A) : ¬ Produces (Specimen.outOfFuel : SGen A) x := by
  simp [Produces, Specimen.outOfFuel, FailWith.failWith, OptionT.run_pure]

/-- Likewise for a refutation, a truncation and an undecided premise: every failure is unproductive;
they differ only in what they *claim*. -/
theorem not_produces_refute (x : A) : ¬ Produces (Specimen.refute : SGen A) x := by
  simp [Produces, Specimen.refute, Fail.fail, ExceptT.lift, OptionT.run_failure]

theorem not_produces_truncated (x : A) : ¬ Produces (Specimen.truncated : SGen A) x := by
  simp [Produces, Specimen.truncated, FailWith.failWith, OptionT.run_pure]

theorem not_produces_inconclusive (x : A) : ¬ Produces (Specimen.inconclusive : SGen A) x := by
  simp [Produces, Specimen.inconclusive, FailWith.failWith, OptionT.run_pure]

/-! ### `Produces` algebra

Every branch obligation in every bridge decomposes the same two ways — through a `bind` and a `pure`.
Proving them once here is what keeps the per-branch proofs about the *relation* rather than about the
support monad.

Note what `produces_bind` does with failure: a `bind` whose first component fails cannot produce
anything, so the existential witness is always a success. That is the whole content of the
transformers' short-circuiting, and it is why branch proofs never mention a failure. -/

/-- Decompose a successful `bind`. -/
theorem produces_bind {A B : Type} {g : SGen A} {f : A → SGen B} {b : B}
    (h : Produces (g >>= f) b) : ∃ a, Produces g a ∧ Produces (f a) b := by
  rcases (Basalt.EnumeratesWith.mem_support_run_bind (.ok b)).mp h with h | ⟨_, _, h⟩
  · exact h
  · cases h

/-- Build a successful `bind`. -/
theorem produces_bind_of {A B : Type} {g : SGen A} {f : A → SGen B} {a : A} {b : B}
    (ha : Produces g a) (hb : Produces (f a) b) : Produces (g >>= f) b :=
  (Basalt.EnumeratesWith.mem_support_run_bind (.ok b)).mpr (.inl ⟨a, ha, hb⟩)

@[simp] theorem produces_bind_iff {A B : Type} {g : SGen A} {f : A → SGen B} {b : B} :
    Produces (g >>= f) b ↔ ∃ a, Produces g a ∧ Produces (f a) b :=
  ⟨produces_bind, fun ⟨_, ha, hb⟩ => produces_bind_of ha hb⟩

@[simp] theorem produces_pure_iff {A : Type} {a b : A} :
    Produces (pure a : SGen A) b ↔ b = a := by
  simp [Produces, OptionT.run_pure]

/-! ### Backtracking -/

/-- What `backtrack` can produce is what its branches of positive weight can. -/
theorem produces_backtrack_iff (gs : List (Nat × (Unit → SGen A))) (x : A) :
    Produces (Basalt.Backtrack.backtrack gs) x ↔ ∃ p ∈ gs, 0 < p.1 ∧ Produces (p.2 ()) x :=
  ⟨Basalt.Backtrack.mem_support_searchWith_ok gs.length gs none x,
   fun ⟨p, hp, hk, h⟩ => Basalt.Backtrack.mem_support_searchWith_ok_of_branch gs.length gs none
     p hp hk (List.length_pos_of_mem hp) x h⟩

/-- A success of `backtrack` came from a branch of positive weight: `pickDrop` only ever selects an
entry `n` fell strictly below, so the witness is live. -/
theorem produces_backtrack_ok (gs : List (Nat × (Unit → SGen A))) (x : A)
    (h : Produces (Basalt.Backtrack.backtrack gs) x) : ∃ p ∈ gs, 0 < p.1 ∧ Produces (p.2 ()) x :=
  (produces_backtrack_iff gs x).mp h

/-- A success of a branch of positive weight is one of `backtrack`; a zero-weight branch is never
drawn. -/
theorem produces_backtrack_of_branch (gs : List (Nat × (Unit → SGen A))) (p : Nat × (Unit → SGen A))
    (hp : p ∈ gs) (hk : 0 < p.1) (x : A) (h : Produces (p.2 ()) x) :
    Produces (Basalt.Backtrack.backtrack gs) x :=
  (produces_backtrack_iff gs x).mpr ⟨p, hp, hk, h⟩

/-! The failures as `simp` facts, so that `simp` closes a branch that ends in one — the `size = 0`
pool's truncation branches among them. -/

@[simp] theorem produces_refute_iff (x : A) : Produces (Specimen.refute : SGen A) x ↔ False :=
  iff_false_intro (not_produces_refute x)

@[simp] theorem produces_outOfFuel_iff (x : A) : Produces (Specimen.outOfFuel : SGen A) x ↔ False :=
  iff_false_intro (not_produces_outOfFuel x)

@[simp] theorem produces_truncated_iff (x : A) : Produces (Specimen.truncated : SGen A) x ↔ False :=
  iff_false_intro (not_produces_truncated x)

@[simp] theorem produces_inconclusive_iff (x : A) :
    Produces (Specimen.inconclusive : SGen A) x ↔ False :=
  iff_false_intro (not_produces_inconclusive x)

/-! ### Failures

`Produces` is an `∃` over executions. Two statements about failure need the other outcomes: a run
that ends refuted (`Refutes`, `none` in the support), and a generator none of whose runs fails
(`NeverFails`). Both come with the same `bind`/`pure` algebra and a law for `backtrack`, proved by
induction on Basalt's search. -/

/-- Some run of `g` ends in a refutation. -/
def Refutes (g : SGen A) : Prop := none ∈ g.run.run.support

/-- Every run of `g` succeeds. -/
def NeverFails (g : SGen A) : Prop := ∀ o ∈ g.run.run.support, ∃ a, o = some (.ok a)

theorem mem_support_run_bind_none {A B : Type} {g : SGen A} {f : A → SGen B} :
    none ∈ (g >>= f).run.run.support ↔ Refutes g ∨ ∃ a, Produces g a ∧ Refutes (f a) := by
  rw [ExceptT.run_bind, OptionT.run_bind, Option.elimM, SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨o, ho, h⟩
    rcases o with _ | _ | a
    · exact .inl ho
    · simp [Option.elim, OptionT.run_pure] at h
    · exact .inr ⟨a, ho, h⟩
  · rintro (h | ⟨a, ha, h⟩)
    · exact ⟨none, h, by simp [Option.elim]⟩
    · exact ⟨some (.ok a), ha, h⟩

@[simp] theorem refutes_bind_iff {A B : Type} {g : SGen A} {f : A → SGen B} :
    Refutes (g >>= f) ↔ Refutes g ∨ ∃ a, Produces g a ∧ Refutes (f a) :=
  mem_support_run_bind_none

@[simp] theorem not_refutes_pure (a : A) : ¬ Refutes (pure a : SGen A) := by
  simp [Refutes, OptionT.run_pure]

theorem refutes_refute : Refutes (Specimen.refute : SGen A) := by
  simp [Refutes, Specimen.refute, Fail.fail, ExceptT.lift, OptionT.run_failure]

theorem not_refutes_outOfFuel : ¬ Refutes (Specimen.outOfFuel : SGen A) := by
  simp [Refutes, Specimen.outOfFuel, FailWith.failWith, OptionT.run_pure]

theorem not_refutes_inconclusive : ¬ Refutes (Specimen.inconclusive : SGen A) := by
  simp [Refutes, Specimen.inconclusive, FailWith.failWith, OptionT.run_pure]

theorem not_refutes_truncated : ¬ Refutes (Specimen.truncated : SGen A) := by
  simp [Refutes, Specimen.truncated, FailWith.failWith, OptionT.run_pure]

theorem neverFails_pure (a : A) : NeverFails (pure a : SGen A) := fun o ho => by
  simp only [ExceptT.run_pure, OptionT.run_pure, SPMF.mem_support_pure_iff] at ho
  exact ⟨a, ho⟩

theorem neverFails_bind {A B : Type} {g : SGen A} {f : A → SGen B} (hg : NeverFails g)
    (hf : ∀ a, Produces g a → NeverFails (f a)) : NeverFails (g >>= f) := fun o ho => by
  rcases o with _ | r
  · rcases mem_support_run_bind_none.mp ho with h | ⟨a, ha, h⟩
    · obtain ⟨_, h⟩ := hg _ h; cases h
    · obtain ⟨_, h⟩ := hf a ha _ h; cases h
  · rcases (Basalt.EnumeratesWith.mem_support_run_bind r).mp ho with ⟨a, ha, h⟩ | ⟨e, he, rfl⟩
    · exact hf a ha _ h
    · obtain ⟨_, h⟩ := hg _ he; cases h

section search

open Basalt.Backtrack

variable {β : Type}

theorem pickDrop_some_of_lt : ∀ {gs : List (Nat × β)} {n : Nat}, n < sumWeights gs →
    ∃ k g rest, pickDrop gs n = some (k, g, rest)
  | [], _, h => by simp at h
  | (k, g) :: gs, n, h => by
    by_cases hn : n < k
    · exact ⟨k, g, gs, by simp [pickDrop, hn]⟩
    · obtain ⟨k', g', r', h'⟩ := pickDrop_some_of_lt (gs := gs) (n := n - k)
        (by simp only [sumWeights_cons] at h; omega)
      exact ⟨k', g', (k, g) :: r', by simp [pickDrop, hn, h']⟩

theorem pickDrop_cases : ∀ {gs : List (Nat × β)} {n k : Nat} {g : β} {rest : List (Nat × β)},
    pickDrop gs n = some (k, g, rest) → rest.length + 1 = gs.length ∧ ∀ q ∈ gs, q = (k, g) ∨ q ∈ rest
  | [], _, _, _, _, h => by simp [pickDrop] at h
  | (k₀, g₀) :: gs, n, k, g, rest, h => by
    by_cases hn : n < k₀
    · simp only [pickDrop, hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact .inl rfl
      · exact .inr hq
    · simp only [pickDrop, hn, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨k', g', rest'⟩, h', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨hl, hc⟩ := pickDrop_cases h'
      refine ⟨by simp [hl], fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact .inr (List.mem_cons_self ..)
      · rcases hc q hq with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

theorem sumWeights_pos : ∀ {gs : List (Nat × β)} {p : Nat × β}, p ∈ gs → 0 < p.1 →
    0 < sumWeights gs
  | [], _, hp, _ => by simp at hp
  | q :: gs, p, hp, hk => by
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [sumWeights_cons]; omega
    · have := sumWeights_pos hp hk
      simp only [sumWeights_cons]; omega

theorem none_mem_finish {acc : Option Exhaustion} :
    none ∈ (finish acc : OptionT SPMF (Except Exhaustion A)).run.support ↔ acc = none := by
  cases acc with
  | none =>
    change none ∈ (Pure.pure none : SPMF (Option (Except Exhaustion A))).support ↔ _
    simp
  | some l =>
    change none ∈ (Pure.pure (some (Except.error l)) : SPMF (Option (Except Exhaustion A))).support ↔ _
    simp

theorem finish_neverFails {acc : Option Exhaustion} {o : Option (Except Exhaustion A)}
    (h : o ∈ (finish acc : OptionT SPMF (Except Exhaustion A)).run.support) :
    o = none ∨ ∃ l, o = some (.error l) := by
  cases acc with
  | none =>
    change o ∈ (Pure.pure none : SPMF (Option (Except Exhaustion A))).support at h
    exact .inl (SPMF.mem_support_pure_iff.mp h)
  | some l =>
    change o ∈ (Pure.pure (some (Except.error l)) : SPMF (Option (Except Exhaustion A))).support at h
    exact .inr ⟨l, SPMF.mem_support_pure_iff.mp h⟩

/-- A search that ends refuted saw no label, and refuted on every branch of positive weight: a
positive branch is either tried, or still in the list when the search stops, which it cannot. -/
theorem refutes_searchWith : ∀ (fuel : Nat) (gs : List (Nat × (Unit → SGen A)))
    (acc : Option Exhaustion), gs.length ≤ fuel →
    none ∈ (searchWith fuel gs acc).run.support →
    acc = none ∧ ∀ p ∈ gs, 0 < p.1 → Refutes (p.2 ())
  | _, [], acc, _, h => by
    simp only [searchWith] at h
    exact ⟨none_mem_finish.mp h, by simp⟩
  | 0, _ :: _, _, hl, _ => absurd hl (by simp)
  | fuel + 1, q :: gs, acc, hl, h => by
    simp only [searchWith, OptionT.run_mk, SPMF.mem_support_bind_iff] at h
    obtain ⟨n, _, h⟩ := h
    split at h
    · rename_i hpick
      refine ⟨none_mem_finish.mp h, fun p hp hk => ?_⟩
      have hpos := sumWeights_pos hp hk
      have hn := n.down.property.2
      obtain ⟨_, _, _, h'⟩ := pickDrop_some_of_lt (gs := q :: gs) (n := n.down.val) (by omega)
      rw [h'] at hpick; cases hpick
    · rename_i k g rest hpick
      obtain ⟨hlen, hcases⟩ := pickDrop_cases hpick
      rw [SPMF.mem_support_bind_iff] at h
      obtain ⟨o, ho, h⟩ := h
      rcases o with _ | _ | a
      · obtain ⟨hacc, hrest⟩ := refutes_searchWith fuel rest acc (by simp only [List.length_cons] at hl hlen; omega) h
        refine ⟨hacc, fun p hp hk => ?_⟩
        rcases hcases p hp with rfl | hp'
        · exact ho
        · exact hrest p hp' hk
      · have := (refutes_searchWith fuel rest _ (by simp only [List.length_cons] at hl hlen; omega) h).1
        simp at this
      · simp at h

/-- What `backtrack` refutes, every branch of positive weight can refute. -/
theorem refutes_backtrack {gs : List (Nat × (Unit → SGen A))}
    (h : Refutes (Basalt.Backtrack.backtrack gs)) : ∀ p ∈ gs, 0 < p.1 → Refutes (p.2 ()) :=
  (refutes_searchWith gs.length gs none (Nat.le_refl _) h).2

@[simp] theorem refutes_truncated_iff : Refutes (Specimen.truncated : SGen A) ↔ False :=
  iff_false_intro not_refutes_truncated

@[simp] theorem refutes_outOfFuel_iff : Refutes (Specimen.outOfFuel : SGen A) ↔ False :=
  iff_false_intro not_refutes_outOfFuel

@[simp] theorem refutes_inconclusive_iff : Refutes (Specimen.inconclusive : SGen A) ↔ False :=
  iff_false_intro not_refutes_inconclusive

@[simp] theorem refutes_refute_iff : Refutes (Specimen.refute : SGen A) ↔ True :=
  iff_true_intro refutes_refute

/-- A search with a branch of positive weight that cannot fail cannot fail: that branch is tried
before the search can stop, and succeeds. -/
theorem neverFails_searchWith : ∀ (fuel : Nat) (gs : List (Nat × (Unit → SGen A)))
    (acc : Option Exhaustion) (p : Nat × (Unit → SGen A)), p ∈ gs → 0 < p.1 →
    NeverFails (p.2 ()) → gs.length ≤ fuel →
    ∀ o ∈ (searchWith fuel gs acc).run.support, ∃ a, o = some (.ok a)
  | _, [], _, _, hp, _, _, _, _, _ => by simp at hp
  | 0, _ :: _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | fuel + 1, q :: gs, acc, p, hp, hk, hnf, hl, o, ho => by
    simp only [searchWith, OptionT.run_mk, SPMF.mem_support_bind_iff] at ho
    obtain ⟨n, _, ho⟩ := ho
    split at ho
    · rename_i hpick
      have hpos := sumWeights_pos hp hk
      have hn := n.down.property.2
      obtain ⟨_, _, _, h'⟩ := pickDrop_some_of_lt (gs := q :: gs) (n := n.down.val) (by omega)
      rw [h'] at hpick; cases hpick
    · rename_i k g rest hpick
      obtain ⟨hlen, hcases⟩ := pickDrop_cases hpick
      rw [SPMF.mem_support_bind_iff] at ho
      obtain ⟨o', ho', ho⟩ := ho
      have hrest : (k, g) ≠ p → p ∈ rest := fun hne => (hcases p hp).resolve_left (Ne.symm hne)
      rcases o' with _ | _ | a
      · by_cases he : (k, g) = p
        · subst he; obtain ⟨_, h⟩ := hnf _ ho'; cases h
        · exact neverFails_searchWith fuel rest acc p (hrest he) hk hnf (by simp only [List.length_cons] at hl hlen; omega) o ho
      · by_cases he : (k, g) = p
        · subst he; obtain ⟨_, h⟩ := hnf _ ho'; cases h
        · exact neverFails_searchWith fuel rest _ p (hrest he) hk hnf (by simp only [List.length_cons] at hl hlen; omega) o ho
      · exact ⟨a, SPMF.mem_support_pure_iff.mp ho⟩

/-- `backtrack` with a branch of positive weight that cannot fail cannot fail. -/
theorem neverFails_backtrack (gs : List (Nat × (Unit → SGen A))) (p : Nat × (Unit → SGen A))
    (hp : p ∈ gs) (hk : 0 < p.1) (h : NeverFails (p.2 ())) :
    NeverFails (Basalt.Backtrack.backtrack gs) :=
  neverFails_searchWith gs.length gs none p hp hk h (Nat.le_refl _)

end search

/-- One-level generator step, over inputs `I` and outputs `A`.

`prev` is the previous fuel level **as a family over size *and input***. Both indices are needed to
model emitted code: a branch may recurse at `size - 1` or `size / 2` (the emitter halves at branching
constructors), and it almost always recurses at a *different input* — the `lookup` generator walks
`Γ`'s tail, `typing`'s `TAbs` extends the context. A step over a single `SGen A` cannot express
either, which is why this is indexed rather than closed over its arguments.

`initSize` needs no index: it is threaded unchanged through every emitted recursive call, so a
concrete step just closes over it. -/
abbrev SGenStep (I A : Type) :=
  (Nat → I → SGen A) → Nat → I → SGen A

/-- Full generator: fuel-iterate the one-level step, bottoming out at `outOfFuel`. This is exactly the
emitted `match fuel with | 0 => outOfFuel | fuel+1 => …` skeleton.

`noncomputable` because `SPMF` is — the support interpretation is a reasoning device, not something
to run. The emitted definition it models is executable at `Plausible.Gen`. -/
noncomputable def genRelB (step : SGenStep I A) : Nat → Nat → I → SGen A
  | 0, _, _ => Specimen.outOfFuel
  | fuel + 1, size, i => step (genRelB step fuel) size i

/-- Everything producible from input `i` at some fuel and size. -/
def semGenRelB (step : SGenStep I A) (i : I) (x : A) : Prop :=
  ∃ fuel size, Produces (genRelB step fuel size i) x

/-- `step` preserves the specification: if the previous level only produced `P`-related values, so
does this one. `P` relates an input to a legal output — it is the relation being derived from. -/
def StepGenSoundB (step : SGenStep I A) (P : I → A → Prop) : Prop :=
  ∀ prev, (∀ sz i x, Produces (prev sz i) x → P i x) →
    ∀ sz i x, Produces (step prev sz i) x → P i x

/-- `step` is **complete relative to the measure pair** `(φ, σ)`: given `P i a`, enough size, and a
previous level that already reaches every `P`-pair of strictly smaller fuel measure (at any sufficient
size), the step reaches `a` from `i`.

The measures range over input *and* output because a recursive call may shrink either — `lookup`
shrinks both, but a relation whose output is fixed-size shrinks only the input. -/
def StepGenCompleteB (step : SGenStep I A) (P : I → A → Prop) (φ σ : I → A → Nat) : Prop :=
  ∀ prev sz i a, P i a → σ i a ≤ sz →
    (∀ j b, P j b → φ j b < φ i a → ∀ sz', σ j b ≤ sz' → Produces (prev sz' j) b) →
    Produces (step prev sz i) a

theorem genRelB_produces_sound {step : SGenStep I A} {P : I → A → Prop}
    (h : StepGenSoundB step P) :
    ∀ (fuel sz : Nat) (i : I) (x : A), Produces (genRelB step fuel sz i) x → P i x
  | 0, _, _, x => fun hx => absurd hx (not_produces_outOfFuel x)
  | fuel + 1, sz, i, x => fun hx =>
    h (genRelB step fuel)
      (fun sz' i' x' hx' => genRelB_produces_sound h fuel sz' i' x' hx') sz i x hx

/-- **Generic generator soundness.** -/
theorem genRelB_sound {step : SGenStep I A} {P : I → A → Prop} (h : StepGenSoundB step P) :
    ∀ i x, semGenRelB step i x → P i x :=
  fun _ _ ⟨fuel, sz, hx⟩ => genRelB_produces_sound h fuel sz _ _ hx

/-- **Generic generator completeness.** Induction on fuel alone suffices: the step's own hypothesis
already restricts the recursive appeal to strictly smaller `φ`, and `φ a < fuel + 1` bounds it. -/
theorem genRelB_complete {step : SGenStep I A} {P : I → A → Prop} {φ σ : I → A → Nat}
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

A failure verdict cannot do this on its own. A labelled failure has three sources in emitted code — the
fuel backstop tripping, a `size = 0` truncated disjunction, and a premise checker answering
inconclusively — and only the middle one involves a search that actually completed. So reading
a labelled failure as "nothing exists within this budget" is unsound in general.

What *is* sound uses only the **absence of a success**, plus completeness. These two lemmas separate the
honest part from the part that needs an extra assumption, and neither inspects the failure constructor. -/

/-- Producing nothing does not refute — it **bounds the witnesses**. Any `a` satisfying `P` must exceed
one of the two budgets. This is just the contrapositive of completeness, and it is the strongest
conclusion available from a failed search alone. -/
theorem witness_exceeds_budget_of_not_produces {step : SGenStep I A} {P : I → A → Prop}
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
theorem refutes_of_not_produces {step : SGenStep I A} {P : I → A → Prop}
    {φ σ : I → A → Nat} (h : StepGenCompleteB step P φ σ) (i : I) (fuel sz : Nat)
    (hbound : ∀ a, P i a → φ i a < fuel ∧ σ i a ≤ sz)
    (hno : ∀ a, ¬ Produces (genRelB step fuel sz i) a) :
    ∀ a, ¬ P i a :=
  fun a hPa => witness_exceeds_budget_of_not_produces h i fuel sz hno a hPa (hbound a hPa)

/-- Corollary in the form a caller wants: pick fuel and size from the measures. -/
theorem genRelB_complete' {step : SGenStep I A} {P : I → A → Prop} {φ σ : I → A → Nat}
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
def StepGenMono (step : SGenStep I A) : Prop :=
  ∀ (prev prev' : Nat → I → SGen A),
    (∀ sz i x, Produces (prev sz i) x → Produces (prev' sz i) x) →
    ∀ sz i x, Produces (step prev sz i) x → Produces (step prev' sz i) x

/-- **More fuel never loses a value.** -/
theorem genRelB_fuel_mono {step : SGenStep I A} (h : StepGenMono step) :
    ∀ (fuel fuel' : Nat), fuel ≤ fuel' → ∀ (sz : Nat) (i : I) (x : A),
      Produces (genRelB step fuel sz i) x → Produces (genRelB step fuel' sz i) x := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ x hx; exact absurd hx (not_produces_outOfFuel x)
  | succ fuel ih =>
    intro fuel' hle sz i x hx
    cases fuel' with
    | zero => exact absurd hle (by omega)
    | succ fuel' =>
      exact h (genRelB step fuel) (genRelB step fuel')
        (fun sz' i' x' hx' => ih fuel' (by omega) sz' i' x' hx') sz i x hx

/-! ## Relation-level assembly

The emitted code is always `Basalt.Backtrack.backtrack` over one branch per constructor, each a function
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
  fun prev sz i => Basalt.Backtrack.backtrack (branches prev sz i)

/-- Soundness reduces to: *every* branch is sound. -/
theorem stepBacktrackB_sound {branches : BranchList I A} {P : I → A → Prop}
    (hbr : ∀ prev, (∀ sz i x, Produces (prev sz i) x → P i x) →
      ∀ sz i p, p ∈ branches prev sz i → ∀ x, Produces (p.2 ()) x → P i x) :
    StepGenSoundB (stepBacktrackB branches) P := by
  intro prev hprev sz i x hx
  obtain ⟨p, hp, _, hpx⟩ := (produces_backtrack_iff _ _).mp hx
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
  exact (produces_backtrack_iff _ _).mpr ⟨p, hp, hpos, hpa⟩

/-- Monotonicity reduces to: whatever a branch produced under `prev`, *some* positively-weighted branch
still produces under `prev'`. Usually the corresponding branch, but the statement does not require it —
which matters because the branch *list* may itself depend on `prev`.

`produces_backtrack_iff` returns the witnessing branch *live* (`0 < p.1`), so the caller
may assume the source branch had positive weight — without that, the obligation would be unprovable for
a branch whose weight is `0` at `size = 0`, exactly the case the default weight function creates. -/
theorem stepBacktrackB_mono {branches : BranchList I A}
    (hbr : ∀ prev prev', (∀ sz i x, Produces (prev sz i) x → Produces (prev' sz i) x) →
      ∀ sz i p, p ∈ branches prev sz i → 0 < p.1 → ∀ x, Produces (p.2 ()) x →
        ∃ q ∈ branches prev' sz i, 0 < q.1 ∧ Produces (q.2 ()) x) :
    StepGenMono (stepBacktrackB branches) := by
  intro prev prev' hmono sz i x hx
  obtain ⟨p, hp, hp0, hpx⟩ := (produces_backtrack_iff _ _).mp hx
  obtain ⟨q, hq, hq0, hqx⟩ := hbr prev prev' hmono sz i p hp hp0 x hpx
  exact (produces_backtrack_iff _ _).mpr ⟨q, hq, hq0, hqx⟩


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
  | 0, _, _, _ => Specimen.outOfFuel
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
  | 0, _, _, _, x => fun hx => absurd hx (not_produces_outOfFuel x)
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
