import Plausible

/-!
# Specimen–Basalt Bridge Mockup: DecOpt Example

This file demonstrates how the proposed Basalt-compatible DecOpt typeclass
works within generators, with execution via Plausible.Gen.
-/

open Lean.Order

namespace MockDecOpt

/-! ## Basalt infrastructure (same as BridgeMockup.lean) -/

class RandomChoice (m : Type u → Type v) where
  choose : (lo hi : Nat) → (h : lo ≤ hi) → m (ULift Nat)

class Gen (g : Type u → Type v) where
  instInhabited : ∀ α, Inhabited (g α)
  instMonad : Monad g
  instRandomChoice : RandomChoice g
  instCCPO : ∀ α, CCPO (g α)
  instMonoBind : MonoBind g

instance [m : Gen g] : ∀ α, Inhabited (g α) := m.instInhabited
instance [m : Gen g] : Monad g := m.instMonad
instance [m : Gen g] : RandomChoice g := m.instRandomChoice
instance [m : Gen g] : ∀ α, CCPO (g α) := m.instCCPO
instance [m : Gen g] : MonoBind g := m.instMonoBind

private instance instPartialOrderExceptGenError : PartialOrder (Except Plausible.GenError α) :=
  FlatOrder.instOrder (b := Except.error default)

private instance instCCPOExceptGenError : CCPO (Except Plausible.GenError α) :=
  FlatOrder.instCCPO (b := Except.error default)

private instance : MonoBind (Except Plausible.GenError) where
  bind_mono_left h := by
    cases h with
    | bot => exact FlatOrder.rel.bot
    | refl => exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Except Plausible.GenError _› with
    | error => exact FlatOrder.rel.refl
    | ok a => exact h a

private instance : RandomChoice Plausible.Gen where
  choose lo hi _ := do
    let ⟨val, _⟩ ← Plausible.Gen.choose Nat lo hi (by omega)
    ULift.up <$> pure val

instance : Gen Plausible.Gen where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance

/-! ## BacktrackGen -/

structure BacktrackGen (G : Type → Type) (α : Type) where
  run : G (Option α)

namespace BacktrackGen

instance [Gen G] : Monad (BacktrackGen G) where
  pure a := ⟨pure (some a)⟩
  bind x f := ⟨do
    match ← x.run with
    | some a => (f a).run
    | none => pure none⟩

instance [Gen G] : Inhabited (BacktrackGen G α) where
  default := ⟨pure none⟩

def liftGen [Gen G] (g : G α) : BacktrackGen G α :=
  ⟨do let a ← g; pure (some a)⟩

def fail [Gen G] : BacktrackGen G α :=
  ⟨pure none⟩

def toPlausibleGen (x : BacktrackGen Plausible.Gen α) : Plausible.Gen α := do
  match ← x.run with
  | some a => pure a
  | none => throw (.genError "backtracking exhausted")

end BacktrackGen

def backtrack [Gen G] (gs : List (Nat × (Unit → BacktrackGen G α))) : BacktrackGen G α :=
  ⟨go gs⟩
where
  go : List (Nat × (Unit → BacktrackGen G α)) → G (Option α)
  | [] => pure none
  | [(_, g)] => (g ()).run
  | gs => do
    let idx ← RandomChoice.choose 0 (gs.length - 1) (by omega)
    let (_, g) := gs[idx.down]!
    match ← (g ()).run with
    | some a => pure (some a)
    | none => go (gs.eraseIdx idx.down)
  termination_by gs => gs.length

class GenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], G α

/-! ## DecOpt: Basalt-compatible checker -/

/-- A partial decision procedure for P, polymorphic over Gen G.
    Returns some true/false if decided, none if can't decide (backtrack). -/
class DecOpt (P : Prop) where
  decOpt : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G Bool

/-- Any Decidable instance gives a DecOpt that never fails. -/
instance (priority := low) [Decidable P] : DecOpt P where
  decOpt _ := pure (decide P)

/-! ## Example: generate-then-check with a bounded constraint -/

instance : GenFor Nat (fun _ => True) where
  gen := do
    let n ← RandomChoice.choose 0 20 (by omega)
    pure n.down

/-- Generate a pair (a, b) where a ≤ b and both are in [lo, hi].
    Strategy: generate freely, then check constraints via DecOpt.
    Multiple branches allow retrying on failure. -/
def genSortedBounded [Gen G] [GenFor Nat (fun _ => True)]
    (lo hi : Nat) (_initSize : Nat) : (size : Nat) → BacktrackGen G (Nat × Nat)
  | _ =>
    let branch : Unit → BacktrackGen G (Nat × Nat) := fun () => do
      let a ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
      let b ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
      -- Check all constraints using DecOpt; fail (backtrack) if any don't hold
      match ← DecOpt.decOpt (P := decide (lo ≤ a ∧ a ≤ hi ∧ lo ≤ b ∧ b ≤ hi ∧ a ≤ b) = true) 0 with
      | true => pure (a, b)
      | false => BacktrackGen.fail
    -- Repeat the branch to give multiple retry attempts
    backtrack [(1, branch), (1, branch), (1, branch), (1, branch), (1, branch),
               (1, branch), (1, branch), (1, branch), (1, branch), (1, branch)]

end MockDecOpt

open MockDecOpt

-- Run genSortedBounded with lo=0, hi=20 (matches generator range for high success rate)
#eval! do
  IO.println "=== genSortedBounded (lo=0, hi=20, size=10) ==="
  let mut successes := 0
  for _ in List.range 50 do
    try
      let result ← Plausible.Gen.run
        (BacktrackGen.toPlausibleGen (genSortedBounded (G := Plausible.Gen) 0 20 10 0)) 10
      IO.println s!"  success: {repr result}"
      successes := successes + 1
    catch _ => pure ()
  IO.println s!"  ({successes}/50 attempts succeeded)"
