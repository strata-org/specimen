import Specimen.Sampler
import Specimen.BasaltBridge

/-!
# `Sampler` runs as `BasaltSampler` does

`Sampler.toBasalt` reads a `Sampler` run as a `BasaltSampler` one, and every operation a derived
generator is built from commutes with it: `pure`, `bind`, a draw, `default`, a refutation, a labelled
failure, `backtrack` and `pick`. A derived generator is polymorphic in its monad and built from these
alone, so at `Sampler` it is the reading of itself at `BasaltSampler`; and running either at Plausible
is the same (`toPlausibleGen_toBasalt`). So the same seed gives the same value, or the same error.
-/

namespace Specimen.Sampler

open Backtrack

/-- A result as `BasaltSampler`'s base, `Plausible.Gen`, returns it. -/
def Res.toBasalt : Res α → Except Plausible.GenError (Option (Except Exhaustion α) × ULift StdGen)
  | .ok a g => .ok (some (.ok a), ⟨g⟩)
  | .refute g => .ok (none, ⟨g⟩)
  | .fail e g => .ok (some (.error e), ⟨g⟩)
  | .abort e => .error e

/-- A `Sampler` run read as a `BasaltSampler` one; it reads no size. -/
def toBasalt (x : Sampler α) : BasaltSampler α :=
  ExceptT.mk (OptionT.mk (fun s _ => (x s.down).toBasalt))

theorem toBasalt_pure (a : α) : toBasalt (pure a : Sampler α) = (pure a : BasaltSampler α) := rfl

theorem toBasalt_bind (x : Sampler α) (f : α → Sampler β) :
    toBasalt (x >>= f) = (toBasalt x >>= fun a => toBasalt (f a)) := by
  funext s r
  show ((x >>= f) s.down).toBasalt = _
  rw [bind_apply]
  simp only [toBasalt, bind, ExceptT.bind, ExceptT.mk, OptionT.bind, OptionT.mk, StateT.bind,
    ReaderT.bind, ExceptT.bindCont]
  cases x s.down <;> rfl

theorem toBasalt_choose (lo hi : Nat) (h : lo ≤ hi) :
    toBasalt (RandomChoice.choose lo hi h : Sampler _) =
      (RandomChoice.choose lo hi h : BasaltSampler _) := rfl

theorem toBasalt_default :
    toBasalt (@Inhabited.default _ (Gen.instInhabited (g := Sampler) α)) =
      @Inhabited.default _ (Gen.instInhabited (g := BasaltSampler) α) := rfl

theorem toBasalt_fail : toBasalt (Fail.fail : Sampler α) = (Fail.fail : BasaltSampler α) := rfl

theorem toBasalt_failWith (e : Exhaustion) :
    toBasalt (FailWith.failWith e : Sampler α) = (FailWith.failWith e : BasaltSampler α) := rfl

/-! ## The search -/

/-- A branch list read at `BasaltSampler`. -/
def mapBranches (gs : List (Nat × (Unit → Sampler α))) : List (Nat × (Unit → BasaltSampler α)) :=
  gs.map fun p => (p.1, fun u => toBasalt (p.2 u))

@[simp] theorem sumWeights_mapBranches (gs : List (Nat × (Unit → Sampler α))) :
    sumWeights (mapBranches gs) = sumWeights gs := by
  simp [mapBranches]

theorem pickDrop_mapBranches : ∀ (gs : List (Nat × (Unit → Sampler α))) (n : Nat),
    pickDrop (mapBranches gs) n =
      (pickDrop gs n).map fun (k, b, rest) => (k, fun u => toBasalt (b u), mapBranches rest)
  | [], _ => rfl
  | (k, b) :: rest, n => by
    simp only [mapBranches, List.map_cons, pickDrop]
    split
    · rfl
    · rw [← mapBranches, pickDrop_mapBranches rest]
      cases pickDrop rest (n - k) <;> rfl

theorem pickDrop_cons_mapBranches (p : Nat × (Unit → Sampler α)) (gs : List (Nat × (Unit → Sampler α)))
    (n : Nat) :
    pickDrop ((p.1, fun u => toBasalt (p.2 u)) :: mapBranches gs) n =
      (pickDrop (p :: gs) n).map fun (k, b, rest) => (k, fun u => toBasalt (b u), mapBranches rest) :=
  pickDrop_mapBranches (p :: gs) n

theorem sumWeights_cons_mapBranches (p : Nat × (Unit → Sampler α)) (gs : List (Nat × (Unit → Sampler α))) :
    sumWeights ((p.1, fun u => toBasalt (p.2 u)) :: mapBranches gs) = sumWeights (p :: gs) :=
  sumWeights_mapBranches (p :: gs)

theorem sumWeights_of_pickDrop : ∀ {gs : List (Nat × β)} {n k b rest},
    pickDrop gs n = some (k, b, rest) → sumWeights rest + k = sumWeights gs
  | [], _, _, _, _, h => by simp [pickDrop] at h
  | (k', b') :: gs, n, k, b, rest, h => by
    simp only [pickDrop] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [sumWeights_cons]; omega
    · cases hp : pickDrop gs (n - k') with
      | none => simp [hp] at h
      | some t =>
        obtain ⟨k₀, b₀, r₀⟩ := t
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have := sumWeights_of_pickDrop hp
        simp only [sumWeights_cons]; omega

theorem toBasalt_finish (acc : Option Exhaustion) :
    toBasalt (finish acc : Sampler α) = ExceptT.mk (Backtrack.finish acc) := by
  cases acc <;> rfl

/-- A draw at `BasaltSampler`'s base is `draw` on the state. -/
theorem choose_apply (lo hi : Nat) (h : lo ≤ hi) :
    (RandomChoice.choose lo hi h : Plausible.Gen _) =
      fun s _ => .ok (⟨⟨(draw lo hi s.down).1, draw_le lo hi h s.down⟩⟩, ⟨(draw lo hi s.down).2⟩) := rfl

/-- A `Sampler` run read at `BasaltSampler`, applied. -/
theorem toBasalt_apply (x : Sampler α) (s : ULift StdGen) (r : ULift Nat) :
    (toBasalt x).run.run s r = (x s.down).toBasalt := rfl

theorem toBasalt_search : ∀ (fuel : Nat) (gs : List (Nat × (Unit → Sampler α)))
    (acc : Option Exhaustion) (total : Nat), total = sumWeights gs →
      toBasalt (search total fuel gs acc) = ExceptT.mk (searchWith fuel (mapBranches gs) acc)
  | fuel, [], acc, _, _ => by cases fuel <;> cases acc <;> rfl
  | 0, _ :: _, acc, _, _ => by cases acc <;> rfl
  | fuel + 1, p :: gs, acc, total, ht => by
    subst ht
    funext s r
    show (search _ (fuel + 1) (p :: gs) acc s.down).toBasalt =
      searchWith (fuel + 1) ((p.1, fun u => toBasalt (p.2 u)) :: mapBranches gs) acc s r
    simp only [searchWith]
    rw [choose_apply]
    simp only [OptionT.mk, bind, StateT.bind, ReaderT.bind, Except.bind, search]
    rw [pickDrop_cons_mapBranches, sumWeights_cons_mapBranches]
    generalize draw 0 (sumWeights (p :: gs) - 1) s.down = d
    obtain ⟨n, g⟩ := d
    cases hpd : pickDrop (p :: gs) n with
    | none => cases acc <;> rfl
    | some t =>
      obtain ⟨k, b, rest⟩ := t
      have hrest : sumWeights (p :: gs) - k = sumWeights rest := by
        have := sumWeights_of_pickDrop hpd; omega
      have ih₁ := fun acc => toBasalt_search fuel rest acc _ hrest
      simp only [Option.map_some, StateT.bind, ReaderT.bind, bind, Except.bind, toBasalt_apply]
      cases b () g with
      | ok a g' => rfl
      | refute g' => exact congrFun (congrFun (ih₁ acc) ⟨g'⟩) r
      | fail e g' => exact congrFun (congrFun (ih₁ _) ⟨g'⟩) r
      | abort e => rfl

theorem toBasalt_backtrack (gs : List (Nat × (Unit → Sampler α))) :
    toBasalt (Backtrack.backtrack gs) = Backtrack.backtrack (mapBranches gs) := by
  show toBasalt (search (sumWeights gs) gs.length gs none) =
    ExceptT.mk (searchWith (mapBranches gs).length (mapBranches gs) none)
  rw [show (mapBranches gs).length = gs.length by simp [mapBranches]]
  exact toBasalt_search _ gs none _ rfl

theorem toBasalt_pick (gs : List (Nat × (Unit → Sampler α))) (h : 0 < sumWeights gs)
    (h' : 0 < sumWeights (mapBranches gs)) :
    toBasalt (Pick.pick gs h) = Pick.pick (mapBranches gs) h' :=
  toBasalt_search 1 gs none _ rfl

/-- Run at Plausible, a `Sampler` run is its reading at `BasaltSampler` run there: the same value
from the same state, or the same error. -/
theorem toPlausibleGen_toBasalt (x : Sampler α) :
    x.toPlausibleGen = (toBasalt x).toPlausibleGen := by
  funext s r
  unfold Sampler.toPlausibleGen BasaltSampler.toPlausibleGen
  simp only [bind, StateT.bind, ReaderT.bind, Except.bind, toBasalt_apply]
  cases x s.down <;> rfl

end Specimen.Sampler
