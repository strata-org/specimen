import Specimen.Correctness.GenInterpSPMF
import Basalt.Laws

/-!
# Size as the termination measure

The emitted generators recurse structurally on a fuel counter, but the counter is only a termination
certificate: every recursive call of a step is made at a strictly smaller size, however the size is
split between the calls. Stated as `SizeDecreasing`, that one property makes the fuel irrelevant once it
exceeds the size, and the fuel-indexed generator at `size + 1` is the unique solution of the step's
unfolding equation. So a derived generator *is* `fixGen step`, a function of the size alone, and every
property of it is proved by induction on the size: soundness and completeness alike, with no fixpoint
order and no fuel in the statement.

This needs no order on the generator monad. Read at `SPMF`, the fuel-indexed levels are also the Kleene
chain of the step, eventually constant from `size + 1` on, but nothing here uses that.
-/

namespace Specimen.Correctness

variable {I A : Type}

/-- `step` at size `sz` consults the previous level only below `sz`. -/
def SizeDecreasing (step : SGenStep I A) : Prop :=
  ∀ (prev prev' : Nat → I → SGen A) (sz : Nat) (i : I),
    (∀ sz' < sz, ∀ j, prev sz' j = prev' sz' j) → step prev sz i = step prev' sz i

/-- **Fuel irrelevance.** Above the size, the fuel no longer matters. -/
theorem genRelB_fuel_irrel {step : SGenStep I A} (h : SizeDecreasing step) :
    ∀ (sz fuel fuel' : Nat) (i : I), sz < fuel → sz < fuel' →
      genRelB step fuel sz i = genRelB step fuel' sz i := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | _ sz ih =>
    intro fuel fuel' i hf hf'
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
    exact h _ _ sz i fun sz' hlt j => ih sz' hlt f f' j (by omega) (by omega)

/-- The generator as a function of the size alone: the fuel-indexed one at the least fuel that never
runs out. -/
noncomputable def fixGen (step : SGenStep I A) (sz : Nat) (i : I) : SGen A :=
  genRelB step (sz + 1) sz i

theorem genRelB_eq_fixGen {step : SGenStep I A} (h : SizeDecreasing step) {fuel sz : Nat} (i : I)
    (hf : sz < fuel) : genRelB step fuel sz i = fixGen step sz i :=
  genRelB_fuel_irrel h sz fuel (sz + 1) i hf (by omega)

/-- **The unfolding equation.** -/
theorem fixGen_eq {step : SGenStep I A} (h : SizeDecreasing step) (sz : Nat) (i : I) :
    fixGen step sz i = step (fixGen step) sz i :=
  h _ _ sz i fun sz' hlt j => genRelB_fuel_irrel h sz' sz (sz' + 1) j hlt (by omega)

/-- **Uniqueness.** Any solution of the unfolding equation is `fixGen step`. -/
theorem fixGen_unique {step : SGenStep I A} (h : SizeDecreasing step) (F : Nat → I → SGen A)
    (hF : ∀ sz i, F sz i = step F sz i) : ∀ sz i, F sz i = fixGen step sz i := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | _ sz ih =>
    intro i
    rw [hF, fixGen_eq h]
    exact h _ _ sz i fun sz' hlt j => ih sz' hlt j

/-- **Soundness**, from the same per-step obligation as at any fuel. -/
theorem fixGen_sound {step : SGenStep I A} {P : I → A → Prop} (hs : StepGenSoundB step P)
    (sz : Nat) (i : I) (x : A) (hx : Produces (fixGen step sz i) x) : P i x :=
  genRelB_produces_sound hs (sz + 1) sz i x hx

/-- `step` is complete relative to a size measure `σ` alone: given `P i a` within the size, and a
previous level that reaches every `P`-pair at every smaller size that fits it, the step reaches `a`. The
recursive appeal is only below `sz`, which is what lets one measure serve for both termination and
completeness. -/
def StepGenCompleteS (step : SGenStep I A) (P : I → A → Prop) (σ : I → A → Nat) : Prop :=
  ∀ (prev : Nat → I → SGen A) (sz : Nat) (i : I) (a : A), P i a → σ i a ≤ sz →
    (∀ sz' < sz, ∀ j b, P j b → σ j b ≤ sz' → Produces (prev sz' j) b) →
    Produces (step prev sz i) a

/-- **Completeness**, by induction on the size. -/
theorem fixGen_complete {step : SGenStep I A} {P : I → A → Prop} {σ : I → A → Nat}
    (h : SizeDecreasing step) (hc : StepGenCompleteS step P σ) :
    ∀ (sz : Nat) (i : I) (a : A), P i a → σ i a ≤ sz → Produces (fixGen step sz i) a := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | _ sz ih =>
    intro i a hPa hσ
    rw [fixGen_eq h]
    exact hc _ sz i a hPa hσ fun sz' hlt j b hPb hσ' => ih sz' hlt j b hPb hσ'

/-! ## For the emitted shape: backtracking over a branch list -/

/-- The branch list at `sz` consults the previous level only below `sz`. -/
def BranchesSizeDecreasing (branches : BranchList I A) : Prop :=
  ∀ (prev prev' : Nat → I → SGen A) (sz : Nat) (i : I),
    (∀ sz' < sz, ∀ j, prev sz' j = prev' sz' j) → branches prev sz i = branches prev' sz i

theorem stepBacktrackB_sizeDecreasing {branches : BranchList I A}
    (h : BranchesSizeDecreasing branches) : SizeDecreasing (stepBacktrackB branches) :=
  fun prev prev' sz i hagree => by
    simp only [stepBacktrackB]; rw [h prev prev' sz i hagree]

/-- Completeness reduces to: *some* positively-weighted branch covers `a`. -/
theorem stepBacktrackB_completeS {branches : BranchList I A} {P : I → A → Prop}
    {σ : I → A → Nat}
    (hbr : ∀ prev sz i a, P i a → σ i a ≤ sz →
      (∀ sz' < sz, ∀ j b, P j b → σ j b ≤ sz' → Produces (prev sz' j) b) →
      ∃ p ∈ branches prev sz i, 0 < p.1 ∧ Produces (p.2 ()) a) :
    StepGenCompleteS (stepBacktrackB branches) P σ := by
  intro prev sz i a hPa hs hrec
  obtain ⟨p, hp, hpos, hpa⟩ := hbr prev sz i a hPa hs hrec
  exact (produces_backtrack_iff _ _).mpr ⟨p, hp, hpos, hpa⟩

/-! ## As Basalt laws

`Produces g x` is `some (.ok x)` in the support of `g`'s `SPMF` run, so the statements above are Basalt's
`IsSoundFor` and `IsCompleteFor` of that run, at the outcomes that are successes. -/

theorem produces_sound_iff_isSoundFor {g : SGen A} {P : A → Prop} :
    (∀ x, Produces g x → P x) ↔ IsSoundFor g.run.run (fun o => ∀ x, o = some (.ok x) → P x) :=
  ⟨fun h o ho x hx => by subst hx; exact h x ho, fun h x hx => h _ hx x rfl⟩

theorem produces_complete_iff_isCompleteFor {g : SGen A} {P : A → Prop} :
    (∀ x, P x → Produces g x) ↔ IsCompleteFor g.run.run (fun o => ∃ x, o = some (.ok x) ∧ P x) :=
  ⟨fun h o ⟨x, hx, hPx⟩ => by subst hx; exact h x hPx, fun h x hPx => h _ ⟨x, rfl, hPx⟩⟩

/-- A derived generator, read at its size, is sound for its relation as a Basalt law. -/
theorem fixGen_isSoundFor {step : SGenStep I A} {P : I → A → Prop} (hs : StepGenSoundB step P)
    (sz : Nat) (i : I) :
    IsSoundFor (fixGen step sz i).run.run (fun o => ∀ x, o = some (.ok x) → P i x) :=
  produces_sound_iff_isSoundFor.mp (fixGen_sound hs sz i)

/-- …and complete for it within the size, as a Basalt law. -/
theorem fixGen_isCompleteFor {step : SGenStep I A} {P : I → A → Prop} {σ : I → A → Nat}
    (h : SizeDecreasing step) (hc : StepGenCompleteS step P σ) (sz : Nat) (i : I) :
    IsCompleteFor (fixGen step sz i).run.run (fun o => ∃ x, o = some (.ok x) ∧ P i x ∧ σ i x ≤ sz) :=
  fun o ⟨x, hx, hPx, hσ⟩ => by subst hx; exact fixGen_complete h hc sz i x hPx hσ

end Specimen.Correctness
