import Specimen.BasaltClasses
import Basalt.PlausibleGen

/-!
# The sampler a Basalt-derived generator runs at

`Specimen.BasaltSampler`, `ExceptT Exhaustion (OptionT Plausible.Gen)`, is four monads deep: every
bind of a derived generator matches an `Except`, an `Option` and Plausible's own `Except`, and passes
a size no derived code reads. `Sampler` is the same computation in one layer: a function of the random
generator's state to one result, which carries the next state unless the run aborted.

It is a drop-in replacement, run for run: the same draws from the same `StdGen` (`draw` is what
`Plausible.Gen.choose` computes), the same search over branches, the same `default`
(`refute`, as `[Gen G]` makes it in derived code), the same failures, so the same values from the same
seed. `Specimen.SamplerAgreement` proves each operation commutes with the reading of a `Sampler` as a
`BasaltSampler`. The one change is inside the search: the total weight is carried rather than summed
again after every draw, which changes no draw.
-/

open Lean.Order

namespace Specimen

/-- A run's result: a value, a refutation, or a labelled failure, each with the generator's next
state; or an abort with one of Plausible's errors, which ends the run (Plausible's `Except` layer, the
order's bottom). -/
inductive Sampler.Res (α : Type) where
  | ok (a : α) (g : StdGen)
  | refute (g : StdGen)
  | fail (e : Exhaustion) (g : StdGen)
  | abort (e : Plausible.GenError)

/-- A derived generator's run: the generator's state to one result. -/
def Sampler (α : Type) : Type := StdGen → Sampler.Res α

namespace Sampler

@[inline] protected def pure (a : α) : Sampler α := fun g => .ok a g

@[inline] protected def bind (x : Sampler α) (f : α → Sampler β) : Sampler β := fun g =>
  match x g with
  | .ok a g => f a g
  | .refute g => .refute g
  | .fail e g => .fail e g
  | .abort e => .abort e

instance : Monad Sampler where
  pure := Sampler.pure
  bind := Sampler.bind

/-- A draw in `[lo, hi]` and the next state, as Plausible's `BoundedRandom Nat` makes it (so as
`Plausible.Gen.choose` does): `randNat` on `[0, hi - lo]`, reduced into `Fin (hi - lo + 1)`, offset by
`lo`. No proof argument, so the bound can be rewritten under it. -/
@[inline] def draw (lo hi : Nat) (g : StdGen) : Nat × StdGen :=
  let r := randNat g 0 (hi - lo)
  (lo + (Fin.ofNat (hi - lo).succ r.1).val, r.2)

theorem draw_le (lo hi : Nat) (h : lo ≤ hi) (g : StdGen) : lo ≤ (draw lo hi g).1 ∧ (draw lo hi g).1 ≤ hi := by
  have := (Fin.ofNat (hi - lo).succ (randNat g 0 (hi - lo)).1).isLt
  simp only [draw]
  omega

instance : RandomChoice Sampler where
  choose lo hi h g := .ok ⟨⟨(draw lo hi g).1, draw_le lo hi h g⟩⟩ (draw lo hi g).2

/-- `refute`, as `default` is at `ExceptT ε (OptionT G)` through `[Gen G]`. -/
instance : Inhabited (Sampler α) := ⟨fun g => .refute g⟩

/-! ## The order: pointwise in the state, flat with an abort at the bottom, as Plausible's -/

instance instOrderRes : PartialOrder (Res α) :=
  FlatOrder.instOrder (b := Res.abort default)

instance instCCPORes : CCPO (Res α) :=
  FlatOrder.instCCPO (b := Res.abort default)

instance instOrder : PartialOrder (Sampler α) := inferInstanceAs (PartialOrder (StdGen → Res α))

instance instCCPO : CCPO (Sampler α) := inferInstanceAs (CCPO (StdGen → Res α))

theorem bind_apply (x : Sampler α) (f : α → Sampler β) (g : StdGen) :
    (x >>= f) g = match x g with
      | .ok a g => f a g
      | .refute g => .refute g
      | .fail e g => .fail e g
      | .abort e => .abort e := rfl

instance : MonoBind Sampler where
  bind_mono_left {_ _ x₁ x₂ f} h g := by
    show @FlatOrder.rel _ (Res.abort default) ((x₁ >>= f) g) ((x₂ >>= f) g)
    rw [bind_apply, bind_apply]
    have hg := h g
    generalize x₁ g = y₁ at hg ⊢
    generalize x₂ g = y₂ at hg ⊢
    cases hg with
    | bot => exact FlatOrder.rel.bot
    | refl => exact FlatOrder.rel.refl
  bind_mono_right {_ _ x f₁ f₂} h g := by
    show @FlatOrder.rel _ (Res.abort default) ((x >>= f₁) g) ((x >>= f₂) g)
    rw [bind_apply, bind_apply]
    cases x g with
    | ok a g => exact h a g
    | _ => exact FlatOrder.rel.refl

instance : Gen Sampler where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance

instance : Fail Sampler := ⟨fun g => .refute g⟩

instance : FailWith Exhaustion Sampler := ⟨fun e g => .fail e g⟩

/-! ## The search -/

/-- How a search with nothing left to try ends, as `Backtrack.finish`. -/
@[inline] def finish : Option Exhaustion → Sampler α
  | none => fun g => .refute g
  | some e => fun g => .fail e g

/-- `Backtrack.searchWith` at `Sampler`: draw a branch by weight; on a refutation or a labelled
failure draw again from the rest, the labels joined. `total` is the branches' total weight, carried
(the drawn branch's weight subtracted) rather than summed again. -/
def search (total : Nat) : Nat → List (Nat × (Unit → Sampler α)) → Option Exhaustion → Sampler α
  | _, [], acc => finish acc
  | 0, _ :: _, acc => finish acc
  | fuel + 1, gs@(_ :: _), acc => fun g =>
    let r := draw 0 (total - 1) g
    match Backtrack.pickDrop gs r.1 with
    | none => finish acc r.2
    | some (k, b, rest) =>
      match b () r.2 with
      | .ok a g => .ok a g
      | .refute g => search (total - k) fuel rest acc g
      | .fail e g => search (total - k) fuel rest (some (acc.elim e (max · e))) g
      | .abort e => .abort e

instance : Backtrack Sampler where
  backtrack gs := search (Backtrack.sumWeights gs) gs.length gs none

/-- One draw, no retry, as `Pick` is at `ExceptT ε (OptionT G)`. -/
instance : Pick Sampler where
  pick gs _ := search (Backtrack.sumWeights gs) 1 gs none

/-! ## Monotonicity -/

section monotonicity

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

theorem search_mono : ∀ (total fuel : Nat) {gs₁ gs₂ : List (Nat × (Unit → Sampler α))}
    (acc : Option Exhaustion), gs₁ ⊑ gs₂ → search total fuel gs₁ acc ⊑ search total fuel gs₂ acc
  | _, _, [], [], _, _ => PartialOrder.rel_refl
  | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h =>
    absurd (Backtrack.length_eq_of_rel h) (by simp)
  | _, 0, _ :: _, _ :: _, _, _ => PartialOrder.rel_refl
  | total, fuel + 1, p₁ :: gs₁, p₂ :: gs₂, acc, h => fun g => by
    show @FlatOrder.rel _ (Res.abort default) (search total (fuel + 1) (p₁ :: gs₁) acc g)
      (search total (fuel + 1) (p₂ :: gs₂) acc g)
    simp only [search]
    rcases Backtrack.pickDrop_rel h (draw 0 (total - 1) g).1 with
      ⟨h₁, h₂⟩ | ⟨k, b₁, b₂, r₁, r₂, h₁, h₂, hb, hr⟩
    · rw [h₁, h₂]; exact FlatOrder.rel.refl
    · rw [h₁, h₂]
      dsimp only
      have hg := hb () (draw 0 (total - 1) g).2
      generalize b₁ () (draw 0 (total - 1) g).2 = y₁ at hg ⊢
      generalize b₂ () (draw 0 (total - 1) g).2 = y₂ at hg ⊢
      cases hg with
      | bot => exact FlatOrder.rel.bot
      | refl =>
        split
        · exact FlatOrder.rel.refl
        · exact search_mono _ fuel acc hr _
        · exact search_mono _ fuel _ hr _
        · exact FlatOrder.rel.refl

instance : MonoBacktrack Sampler where
  backtrack_mono {_ gs₁ gs₂} h := by
    show search (Backtrack.sumWeights gs₁) gs₁.length gs₁ none ⊑
      search (Backtrack.sumWeights gs₂) gs₂.length gs₂ none
    rw [Backtrack.length_eq_of_rel h, Backtrack.sumWeights_eq_of_rel h]
    exact search_mono _ _ none h

end monotonicity

/-! ## Running at Plausible -/

/-- Run at `Plausible.Gen` on its state, throwing as `BasaltSampler.toPlausibleGen` does:
`Gen.genericFailure` for a refutation, `Gen.outOfFuel` for a labelled failure. -/
def toPlausibleGen (x : Sampler α) : Plausible.Gen α := fun s _ =>
  match x s.down with
  | .ok a g => .ok (a, ⟨g⟩)
  | .refute _ => .error Plausible.Gen.genericFailure
  | .fail _ _ => .error Plausible.Gen.outOfFuel
  | .abort e => .error e

end Sampler

end Specimen
