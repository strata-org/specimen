import Plausible

/-!
# Specimen–Basalt Bridge Mockup: Running Example

This file mocks up the proposed generator structure using Basalt's actual Gen class
definition (which depends only on core Lean's Lean.Order) and demonstrates execution
via Plausible's Gen monad.
-/

open Lean.Order

/-! ## Basalt Gen class (copied from Basalt/Gen.lean) -/

namespace Mock

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

/-! ## Plausible.Gen as a Basalt Gen instance (adapted from Basalt/PlausibleGen.lean) -/

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

/-- Unwrap BacktrackGen to Plausible.Gen, throwing on failure. -/
def toPlausibleGen (x : BacktrackGen Plausible.Gen α) : Plausible.Gen α := do
  match ← x.run with
  | some a => pure a
  | none => throw (.genError "backtracking exhausted")

def BacktrackGen.toGen [Gen G] [Inhabited α] (g : BacktrackGen G α) : G α := do
  match ← g.run with
  | some a => pure a
  | none => pure default  -- ⊥ (divergence)

end BacktrackGen

/-! ## backtrack combinator -/

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

/-! ## GenFor / BacktrackGenFor typeclasses -/

class GenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], G α

class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G α

/-! ## Running example -/

inductive Ty | nat | bool
  deriving Repr, Inhabited, BEq

inductive Expr
  | litNat (n : Nat)
  | litBool (b : Bool)
  | isZero (e : Expr)
  deriving Repr, Inhabited

inductive Stmt
  | expr (e : Expr)
  | letBind (x : Nat) (e : Expr) (body : Stmt)
  | assert (e : Expr) (τ : Ty)
  deriving Repr, Inhabited

inductive HasType : Expr → Ty → Prop
  | litNat (n : Nat) : HasType (.litNat n) .nat
  | litBool (b : Bool) : HasType (.litBool b) .bool
  | isZero (e : Expr) : HasType e .nat → HasType (.isZero e) .bool

inductive WellTypedStmt : Stmt → Prop
  | expr (e : Expr) (τ : Ty) : HasType e τ → WellTypedStmt (.expr e)
  | letBind (x : Nat) (e : Expr) (body : Stmt) (τ : Ty) :
      HasType e τ → WellTypedStmt body → WellTypedStmt (.letBind x e body)
  | assert (e : Expr) (τ : Ty) : HasType e τ → WellTypedStmt (.assert e τ)

/-! ## GenFor instances for leaf types -/

instance : GenFor Nat (fun _ => True) where
  gen := do
    -- Simple geometric distribution
    let n ← RandomChoice.choose 0 100 (by omega)
    pure n.down

instance : GenFor Bool (fun _ => True) where
  gen := do
    let n ← RandomChoice.choose 0 1 (by omega)
    pure (n.down == 0)

instance : GenFor Ty (fun _ => True) where
  gen := do
    let n ← RandomChoice.choose 0 1 (by omega)
    pure (if n.down == 0 then Ty.nat else Ty.bool)

/-! ## genHasType: the derived constrained generator -/

def genHasType [Gen G] [GenFor Nat (fun _ => True)] [GenFor Bool (fun _ => True)]
    (initSize : Nat) (τ : Ty) : (size : Nat) → BacktrackGen G Expr
  | 0 => backtrack [
      (1, fun () => match τ with
        | .nat => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            pure (Expr.litNat n)
        | .bool => do
            let b ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Bool)
            pure (Expr.litBool b)),
      (1, fun () => match τ with
        | .bool => do
            let b ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Bool)
            pure (Expr.litBool b)
        | .nat => BacktrackGen.fail)]
  | size + 1 => backtrack [
      (1, fun () => match τ with
        | .nat => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            pure (Expr.litNat n)
        | .bool => do
            let b ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Bool)
            pure (Expr.litBool b)),
      (1, fun () => match τ with
        | .bool => do
            let b ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Bool)
            pure (Expr.litBool b)
        | .nat => BacktrackGen.fail),
      (size + 1, fun () => match τ with
        | .bool => do
            let e ← genHasType initSize Ty.nat size
            pure (Expr.isZero e)
        | .nat => BacktrackGen.fail)]

/-! ## Register genHasType as a BacktrackGenFor instance -/

instance [GenFor Nat (fun _ => True)] [GenFor Bool (fun _ => True)]
    : ∀ τ, BacktrackGenFor Expr (fun e => HasType e τ) :=
  fun τ => ⟨fun {_} [_] size => genHasType size τ size⟩

/-! ## genWellTypedStmt: uses BacktrackGenFor for cross-generator call -/

def genWellTypedStmt [Gen G] [GenFor Nat (fun _ => True)] [GenFor Bool (fun _ => True)]
    [GenFor Ty (fun _ => True)]
    [∀ τ, BacktrackGenFor Expr (fun e => HasType e τ)]
    (initSize : Nat) : (size : Nat) → BacktrackGen G Stmt
  | 0 => backtrack [
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Stmt.expr e)),
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Stmt.assert e τ))]
  | size + 1 => backtrack [
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Stmt.expr e)),
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Stmt.assert e τ)),
      (size + 1, fun () => do
        let body ← genWellTypedStmt initSize size
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        let x ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
        pure (Stmt.letBind x e body))]

/-! ## frequency combinator (for non-backtracking generators) -/

/-- Weighted random selection without retry. For non-backtracking generators. -/
def frequency [Gen G] (default : G α) (gs : List (Nat × (Unit → G α))) : G α :=
  match gs with
  | [] => default
  | [(_, g)] => g ()
  | gs => do
    let idx ← RandomChoice.choose 0 (gs.length - 1) (by omega)
    let (_, g) := gs[idx.down]!
    g ()

/-! ## Unconstrained generator example (derive Arbitrary → GenFor) -/

/-- A simple parametric binary tree to illustrate unconstrained generator derivation. -/
inductive Tree (α : Type) where
  | leaf
  | node (left : Tree α) (val : α) (right : Tree α)
  deriving Repr

/-- Basalt-polymorphic unconstrained generator for Tree α.
    This is what Specimen should emit instead of the Plausible-specific ArbitraryFueled instance. -/
def Tree.gen [Gen G] [GenFor α (fun _ => True)] : (fuel : Nat) → G (Tree α)
  | 0 => frequency (pure Tree.leaf) [
      (1, fun () => pure Tree.leaf)]
  | fuel + 1 => frequency (pure Tree.leaf) [
      (1, fun () => pure Tree.leaf),
      (fuel + 1, fun () => do
        let left ← Tree.gen fuel
        let val ← GenFor.gen (P := fun _ => True)
        let right ← Tree.gen fuel
        pure (Tree.node left val right))]

/-- Register as a GenFor instance. -/
instance [GenFor α (fun _ => True)] : GenFor (Tree α) (fun _ => True) where
  gen := Tree.gen 5  -- fixed default fuel; in practice would use Gen.sized

/-! ## Execution via Plausible -/

end Mock

open Mock

/-! ## Status quo: what Specimen emits today for unconstrained generators (using Plausible directly)
    This verifies that the "What Specimen emits today" code in SPECIMEN-BASALT-BRIDGE.md Section 6
    is accurate. -/
namespace StatusQuo
open Plausible

instance [Arbitrary α] : ArbitraryFueled (Tree α) where
  arbitraryFueled :=
    let rec aux_arb (fuel : Nat) : Plausible.Gen (Tree α) :=
      match fuel with
      | Nat.zero => Gen.oneOfWithDefault (pure Tree.leaf) [pure Tree.leaf]
      | fuel' + 1 => Gen.frequency (pure Tree.leaf)
          [(1, pure Tree.leaf),
           (fuel' + 1, do
              let left ← aux_arb fuel'
              let val ← Arbitrary.arbitrary
              let right ← aux_arb fuel'
              return Tree.node left val right)]
    fun fuel => aux_arb fuel

end StatusQuo

-- Run genHasType at Plausible.Gen and print results.
#eval! do
  IO.println "=== genHasType (τ = .nat, size = 3) ==="
  for _ in List.range 5 do
    let result ← Plausible.Gen.run
      (BacktrackGen.toPlausibleGen (genHasType (G := Plausible.Gen) 3 .nat 3)) 10
    IO.println s!"  {repr result}"

#eval! do
  IO.println "=== genHasType (τ = .bool, size = 3) ==="
  for _ in List.range 5 do
    let result ← Plausible.Gen.run
      (BacktrackGen.toPlausibleGen (genHasType (G := Plausible.Gen) 3 .bool 3)) 10
    IO.println s!"  {repr result}"

#eval! do
  IO.println "=== genWellTypedStmt (size = 3) ==="
  for _ in List.range 5 do
    let result ← Plausible.Gen.run
      (BacktrackGen.toPlausibleGen (genWellTypedStmt (G := Plausible.Gen) 3 3)) 10
    IO.println s!"  {repr result}"

#eval! do
  IO.println "=== Tree.gen (fuel = 3) ==="
  for _ in List.range 5 do
    let result ← Plausible.Gen.run (Tree.gen (G := Plausible.Gen) (α := Nat) 3) 10
    IO.println s!"  {repr result}"