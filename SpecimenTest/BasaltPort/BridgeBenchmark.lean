import Plausible
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.GeneratorCombinators

/-!
# Benchmark: Legacy Specimen generators vs Basalt-bridge BacktrackGen

This file provides an apples-to-apples performance comparison between:
- **Legacy**: exception-based backtracking via `GeneratorCombinators.backtrack`
- **Bridge**: Option-based backtracking via `BacktrackGen` (Basalt approach)

Both versions generate the same set of values for the same size parameter.
The leaf Nat generator uses a fixed range [0, 100] in both versions to ensure equivalence.
-/

open Lean.Order

namespace BridgeBenchmark

/-! ## Shared definitions -/

inductive Ty | nat | bool
  deriving Repr, Inhabited, BEq, DecidableEq

inductive Expr
  | lit (n : Nat)
  | isPos (n : Nat)
  | nary (a b c d e : Expr)
  deriving Repr, Inhabited

inductive HasType : Expr → Ty → Prop
  | lit (n) : HasType (.lit n) .nat
  | isPos (n) : n ≠ 0 → HasType (.isPos n) .bool
  | nary (a b c d e) : HasType a .nat → HasType b .nat → HasType c .nat →
      HasType d .nat → HasType e .nat → HasType (.nary a b c d e) .nat

/-- Fixed-range Nat generator for the legacy side (matches bridge's [0,100] range). -/
private def genNatLegacy : Plausible.Gen Nat := do
  let ⟨n, _⟩ ← Plausible.Gen.choose Nat 0 100 (by omega)
  pure n

/-! ## Legacy (exception-based) -/

namespace Legacy

/-- The exact code pattern Specimen emits today, using exception-based backtracking.
    Uses `genNatLegacy` (fixed [0,100]) instead of `Arbitrary.arbitrary` for equivalence. -/
@[specialize] def genHasType (initSize : Nat) (size : Nat) (τ : Ty) : Plausible.Gen Expr :=
  match size with
  | 0 =>
    GeneratorCombinators.backtrack
      [(1, match τ with
        | .nat => do
          let n ← genNatLegacy
          return Expr.lit n
        | _ => MonadExcept.throw (.genError "fail")),
       (1, match τ with
        | .bool => do
          let n ← genNatLegacy
          match @DecOpt.decOpt (¬(n = 0)) _ initSize with
          | .ok true => return Expr.isPos n
          | _ => MonadExcept.throw (.genError "fail")
        | _ => MonadExcept.throw (.genError "fail"))]
  | size' + 1 =>
    GeneratorCombinators.backtrack
      [(1, match τ with
        | .nat => do
          let n ← genNatLegacy
          return Expr.lit n
        | _ => MonadExcept.throw (.genError "fail")),
       (1, match τ with
        | .bool => do
          let n ← genNatLegacy
          match @DecOpt.decOpt (¬(n = 0)) _ initSize with
          | .ok true => return Expr.isPos n
          | _ => MonadExcept.throw (.genError "fail")
        | _ => MonadExcept.throw (.genError "fail")),
       (size' + 1, match τ with
        | .nat => do
          let a ← genHasType initSize size' .nat
          let b ← genHasType initSize size' .nat
          let c ← genHasType initSize size' .nat
          let d ← genHasType initSize size' .nat
          let e ← genHasType initSize size' .nat
          return Expr.nary a b c d e
        | _ => MonadExcept.throw (.genError "fail"))]

def run (τ : Ty) (size : Nat) : Plausible.Gen Expr :=
  genHasType size size τ

end Legacy

/-! ## Bridge (Option-based BacktrackGen) -/

namespace Bridge

/-! ### Basalt infrastructure (minimal, for benchmarking) -/

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

private instance : PartialOrder (Except Plausible.GenError α) :=
  FlatOrder.instOrder (b := Except.error default)

private instance : CCPO (Except Plausible.GenError α) :=
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
  choose lo hi h := do
    let ⟨val, _⟩ ← Plausible.Gen.choose Nat lo hi h
    pure ⟨val⟩

instance : Gen Plausible.Gen where
  instInhabited := inferInstance
  instMonad := inferInstance
  instRandomChoice := inferInstance
  instCCPO := inferInstance
  instMonoBind := inferInstance

/-! ### BacktrackGen -/

structure BacktrackGen (G : Type → Type) (α : Type) where
  run : G (Option α)

namespace BacktrackGen

@[inline] def bind' [Gen G] (x : BacktrackGen G α) (f : α → BacktrackGen G β) : BacktrackGen G β :=
  ⟨do match ← x.run with
      | some a => (f a).run
      | none => pure none⟩

instance [Gen G] : Monad (BacktrackGen G) where
  pure a := ⟨pure (some a)⟩
  bind := bind'

instance [Gen G] : Inhabited (BacktrackGen G α) where
  default := ⟨pure none⟩

@[inline] def liftGen [Gen G] (g : G α) : BacktrackGen G α :=
  ⟨do let a ← g; pure (some a)⟩

@[inline] def fail [Gen G] : BacktrackGen G α :=
  ⟨pure none⟩

def toPlausibleGen (x : BacktrackGen Plausible.Gen α) : Plausible.Gen α := do
  match ← x.run with
  | some a => pure a
  | none => throw (.genError "backtracking exhausted")

end BacktrackGen

/-! ### backtrack combinator -/

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

/-! ### GenFor and DecOpt -/

class GenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], G α

class BDecOpt (P : Prop) where
  decOpt : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G Bool

instance (priority := low) [Decidable P] : BDecOpt P where
  decOpt _ := pure (decide P)

/-- Fixed-range [0,100] Nat generator, matching the legacy side. -/
instance : GenFor Nat (fun _ => True) where
  gen := do
    let n ← RandomChoice.choose 0 100 (by omega)
    pure n.down

/-! ### The bridge generator -/

@[specialize] def genHasType [Gen G] [GenFor Nat (fun _ => True)]
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
            match ← BDecOpt.decOpt (P := ¬(n = 0)) initSize with
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
            match ← BDecOpt.decOpt (P := ¬(n = 0)) initSize with
            | true => pure (Expr.isPos n)
            | false => BacktrackGen.fail
        | _ => BacktrackGen.fail),
      (size + 1, fun () => match τ with
        | .nat => do
            let a ← genHasType initSize .nat size
            let b ← genHasType initSize .nat size
            let c ← genHasType initSize .nat size
            let d ← genHasType initSize .nat size
            let e ← genHasType initSize .nat size
            pure (Expr.nary a b c d e)
        | _ => BacktrackGen.fail)]

def run (τ : Ty) (size : Nat) : Plausible.Gen Expr :=
  BacktrackGen.toPlausibleGen (genHasType (G := Plausible.Gen) size τ size)

end Bridge

/-! ## Benchmark harness -/

/-- Run a generator `n` times, discarding failures, return elapsed ms. -/
def timeGen (gen : Plausible.Gen Expr) (n : Nat) (runSize : Nat) : IO Nat := do
  let t0 ← IO.monoMsNow
  for _ in List.range n do
    try
      let _ ← Plausible.Gen.run gen runSize
    catch _ => pure ()
  let t1 ← IO.monoMsNow
  pure (t1 - t0)

/-- Run benchmark at a given recursion size, comparing legacy vs bridge. -/
def benchAtSize (size : Nat) (iters : Nat) (τ : Ty) : IO Unit := do
  -- Warm up
  for _ in List.range 100 do
    try let _ ← Plausible.Gen.run (Legacy.run τ size) 10 catch _ => pure ()
    try let _ ← Plausible.Gen.run (Bridge.run τ size) 10 catch _ => pure ()

  let legacyMs ← timeGen (Legacy.run τ size) iters 10
  let bridgeMs ← timeGen (Bridge.run τ size) iters 10

  let ratio := if legacyMs == 0 then "∞" else s!"{(bridgeMs * 100) / legacyMs}%"
  IO.println s!"  size={size}: legacy={legacyMs}ms, bridge={bridgeMs}ms, ratio(bridge/legacy)={ratio}"

/-! ## Main benchmark -/

#eval do
  let iters := 2000
  IO.println s!"=== A/B Benchmark: Legacy vs Bridge (HasType, {iters} iterations) ==="
  IO.println ""

  IO.println "--- τ = .nat (all branches succeed, exercises recursion) ---"
  for size in [2, 3, 4] do
    benchAtSize size iters .nat

  IO.println ""
  IO.println "--- τ = .bool (isPos branch only, exercises backtracking + DecOpt check) ---"
  for size in [2, 3, 4] do
    benchAtSize size iters .bool

/-! ## Microbenchmark: stress backtracking (multiple branch retries)

The interesting case for backtracking overhead is when multiple branches are tried
and fail before one succeeds. Each failed branch does real work (generates values,
checks conditions) before failing. This exercises:
- The retry loop (picking a new branch after failure)
- Failure propagation through nested binds within a branch

We set up 5 branches where the first 4 always fail (after doing some work)
and only the last one can succeed. With weight-based selection, the failing
branches are tried first with high probability.
-/

namespace StressBacktrack

private def genNat100Legacy : Plausible.Gen Nat := do
  let ⟨n, _⟩ ← Plausible.Gen.choose Nat 0 100 (by omega)
  pure n

/-- Legacy: 5 branches with heavy weights on the failing ones.
    Each failing branch generates 5 Nats (simulating liftGen work) before failing. -/
@[specialize] def legacyMultiBranch (initSize : Nat) : Plausible.Gen Expr :=
  GeneratorCombinators.backtrack
    [(10, do
      let a ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      if a + 1 == 999 then return Expr.lit a
      else MonadExcept.throw (.genError "fail")),
     (10, do
      let a ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      if a + 2 == 999 then return Expr.lit a
      else MonadExcept.throw (.genError "fail")),
     (10, do
      let a ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      if a + 3 == 999 then return Expr.lit a
      else MonadExcept.throw (.genError "fail")),
     (10, do
      let a ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      let _ ← genNat100Legacy
      if a + 4 == 999 then return Expr.lit a
      else MonadExcept.throw (.genError "fail")),
     (1, do
      let n ← genNat100Legacy
      match @DecOpt.decOpt (¬(n = 0)) _ initSize with
      | .ok true => return Expr.isPos n
      | _ => return Expr.isPos 1)]

/-- Bridge (unbatched): 5 separate liftGens per failing branch. -/
@[specialize] def bridgeMultiBranch [Bridge.Gen G] [Bridge.GenFor Nat (fun _ => True)]
    (initSize : Nat) : Bridge.BacktrackGen G Expr :=
  Bridge.backtrack
    [(10, fun () => do
      let a ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      if a + 1 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (10, fun () => do
      let a ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      if a + 2 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (10, fun () => do
      let a ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      if a + 3 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (10, fun () => do
      let a ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      let _ ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      if a + 4 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (1, fun () => do
      let n ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      match ← Bridge.BDecOpt.decOpt (P := ¬(n = 0)) initSize with
      | true => pure (Expr.isPos n)
      | false => pure (Expr.isPos 1))]

/-- Bridge (batched): consecutive liftGens grouped into one lift. -/
@[specialize] def bridgeMultiBranchBatched [Bridge.Gen G] [Bridge.GenFor Nat (fun _ => True)]
    (initSize : Nat) : Bridge.BacktrackGen G Expr :=
  Bridge.backtrack
    [(10, fun () => do
      let (a, _, _, _, _) ← Bridge.BacktrackGen.liftGen (do
        let a ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let b ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let c ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let d ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let e ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        pure (a, b, c, d, e))
      if a + 1 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (10, fun () => do
      let (a, _, _, _, _) ← Bridge.BacktrackGen.liftGen (do
        let a ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let b ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let c ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let d ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let e ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        pure (a, b, c, d, e))
      if a + 2 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (10, fun () => do
      let (a, _, _, _, _) ← Bridge.BacktrackGen.liftGen (do
        let a ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let b ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let c ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let d ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let e ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        pure (a, b, c, d, e))
      if a + 3 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (10, fun () => do
      let (a, _, _, _, _) ← Bridge.BacktrackGen.liftGen (do
        let a ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let b ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let c ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let d ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        let e ← (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
        pure (a, b, c, d, e))
      if a + 4 == 999 then pure (Expr.lit a)
      else Bridge.BacktrackGen.fail),
     (1, fun () => do
      let n ← Bridge.BacktrackGen.liftGen (Bridge.GenFor.gen (P := fun _ => True) : G Nat)
      match ← Bridge.BDecOpt.decOpt (P := ¬(n = 0)) initSize with
      | true => pure (Expr.isPos n)
      | false => pure (Expr.isPos 1))]

end StressBacktrack

#eval do
  let iters := 10000
  IO.println s!""
  IO.println s!"=== Stress Backtrack: 5 branches, 4 always fail after work, {iters} iters ==="

  let t0 ← IO.monoMsNow
  for _ in List.range iters do
    try let _ ← Plausible.Gen.run (StressBacktrack.legacyMultiBranch 5) 10 catch _ => pure ()
  let t1 ← IO.monoMsNow

  let t2 ← IO.monoMsNow
  for _ in List.range iters do
    try
      let _ ← Plausible.Gen.run
        (Bridge.BacktrackGen.toPlausibleGen
          (StressBacktrack.bridgeMultiBranch (G := Plausible.Gen) 5)) 10
    catch _ => pure ()
  let t3 ← IO.monoMsNow

  let t4 ← IO.monoMsNow
  for _ in List.range iters do
    try
      let _ ← Plausible.Gen.run
        (Bridge.BacktrackGen.toPlausibleGen
          (StressBacktrack.bridgeMultiBranchBatched (G := Plausible.Gen) 5)) 10
    catch _ => pure ()
  let t5 ← IO.monoMsNow

  let legacyMs := t1 - t0
  let bridgeMs := t3 - t2
  let batchedMs := t5 - t4
  let ratio := if legacyMs == 0 then "∞" else s!"{(bridgeMs * 100) / legacyMs}%"
  let ratioBatched := if legacyMs == 0 then "∞" else s!"{(batchedMs * 100) / legacyMs}%"
  IO.println s!"  legacy={legacyMs}ms, bridge={bridgeMs}ms ({ratio}), bridge-batched={batchedMs}ms ({ratioBatched})"

/-! ## IR inspection

To check newtype erasure and specialization, uncomment and build separately:
  set_option trace.compiler.ir.result true in
  def inspectIR : Plausible.Gen Expr :=
    Bridge.BacktrackGen.toPlausibleGen (Bridge.genHasType (G := Plausible.Gen) 3 .nat 3)
-/

end BridgeBenchmark
