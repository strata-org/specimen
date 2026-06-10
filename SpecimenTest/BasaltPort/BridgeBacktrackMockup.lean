import Plausible
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.GeneratorCombinators

/-!
# Specimen–Basalt Bridge Mockup: Backtracking, Sub-generators, and Checkers

This file demonstrates all three mechanisms from Specimen-Basalt-port.md in a single
example that genuinely exercises each:

1. **Backtracking**: The `isPos` branch (targeting `.bool`) generates `n` randomly and
   fails if `n = 0`. The `add` and `lit` branches fail when `τ ≠ .nat`. The `backtrack`
   combinator retries another branch on failure.
2. **Sub-generators (BacktrackGenFor)**: The `WellFormed` generator calls into the
   `HasType` generator via typeclass resolution (`BacktrackGenFor.gen`).
3. **Checkers (DecOpt)**: `n ≠ 0` is checked via `DecOpt` after `n` is already generated —
   this is a pure guard on an already-determined value.

The mockup presents:
- What Specimen generates **today** (status quo, using Plausible directly)
- What the **migrated** code looks like (using BacktrackGen, GenFor, BacktrackGenFor, DecOpt)

The status-quo code is taken directly from Specimen's trace output for this example.
-/

open Lean.Order

namespace MockBacktrack

/-! ## Basalt infrastructure -/

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

/-! ## Combinators -/

/-- Sum of weights in a weighted generator list. -/
def sumWeights (gs : List (Nat × β)) : Nat :=
  gs.map Prod.fst |>.sum

/-- Weighted selection with drop: given `n ∈ [0, total-1]`, find the element whose weight
    interval contains `n`, return its weight, the element, and the remaining list. -/
def pickDrop [Inhabited β] (gs : List (Nat × β)) (n : Nat) : Nat × β × List (Nat × β) :=
  match gs with
  | [] => (0, default, [])
  | (k, g) :: rest =>
    if n < k then (k, g, rest)
    else
      let (k', g', rest') := pickDrop rest (n - k)
      (k', g', (k, g) :: rest')

/-- Weighted backtracking: randomly pick a branch by weight, try it, retry remaining on failure.
    Uses fuel (initially gs.length) for termination, matching Specimen's backtrackFuel. -/
def backtrack [Gen G] (gs : List (Nat × (Unit → BacktrackGen G α))) : BacktrackGen G α :=
  ⟨go gs.length (sumWeights gs) gs⟩
where
  go : Nat → Nat → List (Nat × (Unit → BacktrackGen G α)) → G (Option α)
  | _, _, [] => pure none
  | 0, _, _ => pure none
  | fuel + 1, total, gs@(_ :: _) => do
    let n ← RandomChoice.choose 0 (total - 1) (by omega)
    let (k, g, gs') := pickDrop gs n.down
    match ← (g ()).run with
    | some a => pure (some a)
    | none => go fuel (total - k) gs'

/-! ## Typeclasses -/

class GenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], G α

class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G α

class DecOpt (P : Prop) where
  decOpt : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G Bool

instance (priority := low) [Decidable P] : DecOpt P where
  decOpt _ := pure (decide P)

/-! ## Running example -/

inductive Ty | nat | bool
  deriving Repr, Inhabited, BEq, DecidableEq

inductive Expr
  | lit (n : Nat)
  | isPos (n : Nat)
  | add (l r : Expr)
  deriving Repr, Inhabited

inductive HasType : Expr → Ty → Prop
  | lit (n) : HasType (.lit n) .nat
  | isPos (n) : n ≠ 0 → HasType (.isPos n) .bool
  | add (l r) : HasType l .nat → HasType r .nat → HasType (.add l r) .nat

inductive Prog
  | expr (e : Expr)
  | both (e1 e2 : Expr)
  deriving Repr, Inhabited

inductive WellFormed : Prog → Prop
  | expr (e τ) : HasType e τ → WellFormed (.expr e)
  | both (e1 e2 τ) : HasType e1 τ → HasType e2 τ → WellFormed (.both e1 e2)

/-! ## GenFor instances for leaf types -/

instance : GenFor Nat (fun _ => True) where
  gen := do
    let n ← RandomChoice.choose 0 100 (by omega)
    pure n.down

instance : GenFor Ty (fun _ => True) where
  gen := do
    let n ← RandomChoice.choose 0 1 (by omega)
    pure (if n.down == 0 then Ty.nat else Ty.bool)

/-! ## Migrated genHasType (Basalt-polymorphic)

This is what Specimen should emit after the migration. It mirrors the structure of
the actual Specimen output (shown in the StatusQuo section below) with the following
mechanical transformations:
- `GeneratorCombinators.backtrack [(w, body)]` → `backtrack [(w, fun () => body)]`
- `MonadExcept.throw ...` → `BacktrackGen.fail`
- `Arbitrary.arbitrary` → `BacktrackGen.liftGen (GenFor.gen ...)`
- `match DecOpt.decOpt ... with | Except.ok true => ... | _ => throw` →
  `match ← DecOpt.decOpt ... with | true => ... | false => BacktrackGen.fail`
- `return` → `pure`
- Return type: `Plausible.Gen Expr` → `BacktrackGen G Expr`
- Polymorphic over `[Gen G]`
-/

def genHasType [Gen G] [GenFor Nat (fun _ => True)]
    (initSize : Nat) (τ : Ty) : (size : Nat) → BacktrackGen G Expr
  | 0 => backtrack [
      (1, fun () => match τ with
        | .nat => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            pure (Expr.lit n)
        | _ => BacktrackGen.fail),
      (1, fun () => match τ with
        | .bool => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            -- *** CHECKER (DecOpt) ***: check n ≠ 0 on already-generated n
            match ← DecOpt.decOpt (P := ¬(n = 0)) initSize with
            | true => pure (Expr.isPos n)
            | false => BacktrackGen.fail
        | _ => BacktrackGen.fail)]
  | size + 1 => backtrack [
      (1, fun () => match τ with
        | .nat => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            pure (Expr.lit n)
        | _ => BacktrackGen.fail),
      (1, fun () => match τ with
        | .bool => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            -- *** CHECKER (DecOpt) ***
            match ← DecOpt.decOpt (P := ¬(n = 0)) initSize with
            | true => pure (Expr.isPos n)
            | false => BacktrackGen.fail
        | _ => BacktrackGen.fail),
      -- *** BACKTRACKING ***: this branch fails when τ ≠ .nat
      (size + 1, fun () => match τ with
        | .nat => do
            let l ← genHasType initSize .nat size
            let r ← genHasType initSize .nat size
            pure (Expr.add l r)
        | _ => BacktrackGen.fail)]

/-! ## Register genHasType as a BacktrackGenFor instance -/

instance [GenFor Nat (fun _ => True)]
    : ∀ τ, BacktrackGenFor Expr (fun e => HasType e τ) :=
  fun τ => ⟨fun {_} [_] size => genHasType size τ size⟩

/-! ## Migrated genWellFormed (Basalt-polymorphic)

Demonstrates the sub-generator mechanism: calls HasType via BacktrackGenFor resolution. -/

def genWellFormed [Gen G] [GenFor Nat (fun _ => True)] [GenFor Ty (fun _ => True)]
    [∀ τ, BacktrackGenFor Expr (fun e => HasType e τ)]
    (initSize : Nat) : (size : Nat) → BacktrackGen G Prog
  | 0 => backtrack [
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        -- *** SUB-GENERATOR (BacktrackGenFor) ***
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.expr e)),
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        -- *** SUB-GENERATOR *** (twice, for same type)
        let e1 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        let e2 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.both e1 e2))]
  | _size + 1 => backtrack [
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.expr e)),
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e1 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        let e2 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.both e1 e2))]

/-! ## frequency combinator (for non-backtracking generators) -/

/-- Weighted selection by interval: given `n ∈ [0, total-1]`, find the element whose weight
    interval contains `n`. -/
def pick (default : β) (gs : List (Nat × β)) (n : Nat) : Nat × β :=
  match gs with
  | [] => (0, default)
  | (k, g) :: rest =>
    if n < k then (k, g)
    else pick default rest (n - k)

/-- Weighted random selection without retry (matches GeneratorCombinators.frequency).
    Picks a generator from `gs` by weight interval. Returns `default` if `gs` is empty. -/
def frequency [Gen G] (default : G α) (gs : List (Nat × (Unit → G α))) : G α :=
  match gs with
  | [] => default
  | _ => do
    let total := sumWeights gs
    let n ← RandomChoice.choose 0 (total - 1) (by omega)
    (pick (fun () => default) gs n.down).snd ()

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

end MockBacktrack

/-! ## Status quo: what Specimen actually generates today (from trace output)

This is the *exact* code Specimen produces for this example, confirming the mockup above
faithfully mirrors the structure. -/

namespace StatusQuo
open Plausible
open MockBacktrack (Ty Expr HasType Prog WellFormed)

instance : Arbitrary Ty where
  arbitrary := do
    let n ← Gen.choose Nat 0 1 (by omega)
    pure (if n.val == 0 then Ty.nat else Ty.bool)

instance : ArbitrarySizedSuchThat Expr (fun e => HasType e τ) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (τ : Ty) : Plausible.Gen Expr :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, match τ with
            | Ty.nat => do
              let (n : Nat) ← Arbitrary.arbitrary
              return Expr.lit n
            | _ => MonadExcept.throw (Plausible.GenError.genError "fail")),
           (1, match τ with
            | Ty.bool => do
              let (n : Nat) ← Arbitrary.arbitrary
              match _root_.DecOpt.decOpt (P := ¬(n = 0)) initSize with
              | Except.ok true => return Expr.isPos n
              | _ => MonadExcept.throw (Plausible.GenError.genError "fail")
            | _ => MonadExcept.throw (Plausible.GenError.genError "fail"))]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1, match τ with
            | Ty.nat => do
              let (n : Nat) ← Arbitrary.arbitrary
              return Expr.lit n
            | _ => MonadExcept.throw (Plausible.GenError.genError "fail")),
           (1, match τ with
            | Ty.bool => do
              let (n : Nat) ← Arbitrary.arbitrary
              match _root_.DecOpt.decOpt (P := ¬(n = 0)) initSize with
              | Except.ok true => return Expr.isPos n
              | _ => MonadExcept.throw (Plausible.GenError.genError "fail")
            | _ => MonadExcept.throw (Plausible.GenError.genError "fail")),
           (Nat.succ size', match τ with
            | Ty.nat => do
              let (l : Expr) ← aux_arb initSize size' Ty.nat
              let (r : Expr) ← aux_arb initSize size' Ty.nat
              return Expr.add l r
            | _ => MonadExcept.throw (Plausible.GenError.genError "fail"))]
    fun size => aux_arb size size τ

instance : ArbitrarySizedSuchThat Prog (fun p => WellFormed p) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : Plausible.Gen Prog :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, do
            let (τ : Ty) ← Arbitrary.arbitrary
            let (e : Expr) ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
            return Prog.expr e),
           (1, do
            let (τ : Ty) ← Arbitrary.arbitrary
            let (e1 : Expr) ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
            let (e2 : Expr) ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
            return Prog.both e1 e2)]
      | Nat.succ _size' =>
        GeneratorCombinators.backtrack
          [(1, do
            let (τ : Ty) ← Arbitrary.arbitrary
            let (e : Expr) ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
            return Prog.expr e),
           (1, do
            let (τ : Ty) ← Arbitrary.arbitrary
            let (e1 : Expr) ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
            let (e2 : Expr) ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
            return Prog.both e1 e2)]
    fun size => aux_arb size size

end StatusQuo

/-! ## Execution -/

open MockBacktrack

#eval do
  IO.println "=== genHasType (τ = .bool, size = 5) — isPos with DecOpt n≠0 check ==="
  for _ in List.range 8 do
    let result ← Plausible.Gen.run
      (BacktrackGen.toPlausibleGen (genHasType (G := Plausible.Gen) 5 .bool 5)) 10
    IO.println s!"  {repr result}"

#eval do
  IO.println "=== genHasType (τ = .nat, size = 3) — lit and add, with backtracking ==="
  for _ in List.range 5 do
    let result ← Plausible.Gen.run
      (BacktrackGen.toPlausibleGen (genHasType (G := Plausible.Gen) 3 .nat 3)) 10
    IO.println s!"  {repr result}"

#eval do
  IO.println "=== genWellFormed (size = 3) — sub-generator calls into HasType ==="
  for _ in List.range 5 do
    let result : Prog ← Plausible.Gen.run
      (BacktrackGen.toPlausibleGen (genWellFormed (G := Plausible.Gen) 3 3)) 10
    IO.println s!"  {repr result}"

-- Also run the status-quo version to confirm both produce the same kinds of output
#eval do
  IO.println "=== StatusQuo HasType (τ = .bool, size = 5) ==="
  for _ in List.range 5 do
    let inst : ArbitrarySizedSuchThat Expr (fun e => HasType e .bool) := inferInstance
    let result ← Plausible.Gen.run (inst.arbitrarySizedST 5) 10
    IO.println s!"  {repr result}"

/-! ## Status quo: what Specimen emits today for unconstrained generators -/
namespace UnconstrainedStatusQuo
open Plausible
open MockBacktrack (Tree)

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

end UnconstrainedStatusQuo

-- Run the migrated unconstrained generator
#eval do
  IO.println "=== Tree.gen (fuel = 3) ==="
  for _ in List.range 5 do
    let result ← Plausible.Gen.run (Tree.gen (G := Plausible.Gen) (α := Nat) 3) 10
    IO.println s!"  {repr result}"
