import Specimen.DeriveConstrainedProducer
import Plausible.Gen

/-!
# Weight Function and Modifier Distribution Tests

Tests that changing the weight function or applying a modifier produces
measurably different distributions. Uses Between (a Nat range relation)
since the number of recursive steps directly determines the output value,
making the weight's effect on distribution clearly measurable.
-/

open Plausible Scoring Schedules

-- ============================================================
-- Six copies of Between, one per configuration, since an instance is per relation:
-- A balanced weights, B flat weights, C base-heavy weights, D the triple-recursive modifier,
-- E recursion-heavy weights, F the default weights D's modifier is applied on top of.
-- ============================================================

inductive BetweenA : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, BetweenA lo hi lo
  | there : ∀ lo hi n, BetweenA (lo + 1) hi n → BetweenA lo hi n

inductive BetweenB : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, BetweenB lo hi lo
  | there : ∀ lo hi n, BetweenB (lo + 1) hi n → BetweenB lo hi n

inductive BetweenC : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, BetweenC lo hi lo
  | there : ∀ lo hi n, BetweenC (lo + 1) hi n → BetweenC lo hi n

inductive BetweenD : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, BetweenD lo hi lo
  | there : ∀ lo hi n, BetweenD (lo + 1) hi n → BetweenD lo hi n

inductive BetweenE : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, BetweenE lo hi lo
  | there : ∀ lo hi n, BetweenE (lo + 1) hi n → BetweenE lo hi n

inductive BetweenF : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, BetweenF lo hi lo
  | there : ∀ lo hi n, BetweenF (lo + 1) hi n → BetweenF lo hi n

-- ============================================================
-- Section 1: Balanced weights (default)
-- ============================================================

set_option specimen.weightFn "Scoring.balancedCtorWeight" in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual
  (fun (lo hi : Nat) => ∃ n, BetweenA lo hi n)

-- ============================================================
-- Section 2: Flat weights (recursive = base = 1)
-- ============================================================

set_option specimen.weightFn "Scoring.flatCtorWeight" in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual
  (fun (lo hi : Nat) => ∃ n, BetweenB lo hi n)

-- ============================================================
-- Section 3: Custom weight that heavily favors base case (here)
-- ============================================================

def heavyBaseWeight (_ctorName : Name) (_outputIndices : List Nat) (_deriveSort : DeriveSort)
    (_scoreBadness : Nat) (isRec : Bool) (size : Nat) (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  if isRec then (if size == 0 then 0 else 1) else 20

initialize Scoring.registerWeightFn `heavyBaseWeight heavyBaseWeight ``heavyBaseWeight

set_option specimen.weightFn "heavyBaseWeight" in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual
  (fun (lo hi : Nat) => ∃ n, BetweenC lo hi n)

-- ============================================================
-- Section 4: Modifier that triples recursive constructor weight
-- ============================================================

def tripleRecModifier (baseWeight : Nat) (_ctorName : Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  if isRec then baseWeight * 3 else baseWeight

#eval Scoring.registerWeightModifier `tripleRecModifier tripleRecModifier ``tripleRecModifier

set_option specimen.weightModifier "tripleRecModifier" in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual
  (fun (lo hi : Nat) => ∃ n, BetweenD lo hi n)

-- ============================================================
-- Section 5: Custom weight that heavily favors recursion (there), the mirror of heavyBaseWeight
-- ============================================================

def heavyRecWeight (_ctorName : Name) (_outputIndices : List Nat) (_deriveSort : DeriveSort)
    (_scoreBadness : Nat) (isRec : Bool) (size : Nat) (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  if isRec then (if size == 0 then 0 else 20) else 1

initialize Scoring.registerWeightFn `heavyRecWeight heavyRecWeight ``heavyRecWeight

set_option specimen.weightFn "heavyRecWeight" in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual
  (fun (lo hi : Nat) => ∃ n, BetweenE lo hi n)

-- ============================================================
-- Section 6: The default weights, with no modifier
--
-- The control for section 4: a modifier scales whatever the active weight function returns, so the
-- modifier's effect only shows against the same weight function without it.
-- ============================================================

set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual
  (fun (lo hi : Nat) => ∃ n, BetweenF lo hi n)

-- ============================================================
-- Section 7: Sample and check distribution relationships
--
-- Between lo hi n generates n in [lo, hi]. The generated value minus lo
-- equals the number of `there` steps taken. So the average (n - lo)
-- directly reflects how often the recursive constructor is chosen.
-- ============================================================

/-- Any fixed value works. The point is that the averages below come from a reproducible stream
    instead of the ambient RNG, whose state at this point depends on whatever ran before. -/
private def sampleSeed : Nat := 20261020

/-- Draws behind each average. The configurations compared below differ by factors, so a few thousand
    draws place each average far from its neighbours. -/
private def sampleTrials : Nat := 2000

/-- Sampling size.

    Large enough that the size-sensitive weights separate from the size-blind ones. `balancedCtorWeight`
    weighs recursion `size / numRec` against a constant `4` for the base case, so at a small size the
    first step is nearly a coin flip and the averages of balanced and flat weights land within a few
    percent of each other, which is not a difference a test can rest on. At 20 the early steps weigh
    about 20 to 4 and the two separate by a factor of three. `Between` does not bound `hi`, so the
    offsets are free to grow with the size. -/
private def sampleSize : Nat := 20

/-- Each comparison below must hold by at least this factor, not merely in order, so that a weight
    change which flattens a distribution fails rather than squeaking through. Every comparison here
    was measured at 2.8 or better across 14 seeds. -/
private def minFactor : Float := 2.0

/-- Average of `n - lo` over `sampleTrials` draws of `gen`, taken from one seeded stream, or an
    error naming `label` if there is no average to report.

    A missing measurement is an error rather than a zero: zero is a plausible-looking average that
    satisfies most of the orderings asserted below, so a generator that produced nothing at all would
    read as a pass.

    One stream rather than a seeded run per draw: reseeding every draw correlates its first value
    across draws, and that value is what picks the constructor, so the average would stop reflecting
    the weights. The run size cycles over `sampleSize` to `sampleSize + 10`, so each average spans
    sizes. -/
private def avgOffset (label : String) (gen : Nat → Gen Nat) (lo : Nat) :
    Except String Float :=
  let loop : Gen (Nat × Nat) := do
    let mut totalOffset : Nat := 0
    let mut successes : Nat := 0
    for i in [:sampleTrials] do
      try
        let n ← Gen.resize (fun _ => sampleSize + i % 11) (gen sampleSize)
        totalOffset := totalOffset + (n - lo)
        successes := successes + 1
      catch _ => pure ()
    return (totalOffset, successes)
  match (runRandWith sampleSeed loop).run (ULift.up sampleSize) with
  | .error (.genError msg) => .error s!"FAIL: {label}: the seeded stream failed: {msg}"
  | .ok (_, 0) => .error s!"FAIL: {label}: all {sampleTrials} draws failed, no average to compare"
  | .ok (totalOffset, successes) => .ok (totalOffset.toFloat / successes.toFloat)

/-- Throws unless `lo` is smaller than `hi` by `minFactor`. -/
private def assertFactor (loName : String) (lo : Float) (hiName : String) (hi : Float) : IO Unit :=
  unless lo * minFactor ≤ hi do
    throw <| IO.userError
      s!"FAIL: expected {hiName} ({hi}) to be at least {minFactor}x {loName} ({lo})"

/-- info: PASS -/
#guard_msgs in
#eval do
  let lo := 0
  let avgBalanced ← IO.ofExcept <| avgOffset "balanced"
    (fun sz => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => BetweenA lo 20 n) sz) lo
  let avgFlat ← IO.ofExcept <| avgOffset "flat"
    (fun sz => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => BetweenB lo 20 n) sz) lo
  let avgHeavyBase ← IO.ofExcept <| avgOffset "heavyBase"
    (fun sz => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => BetweenC lo 20 n) sz) lo
  let avgTripleRec ← IO.ofExcept <| avgOffset "tripleRec"
    (fun sz => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => BetweenD lo 20 n) sz) lo
  let avgHeavyRec ← IO.ofExcept <| avgOffset "heavyRec"
    (fun sz => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => BetweenE lo 20 n) sz) lo
  let avgDefault ← IO.ofExcept <| avgOffset "default"
    (fun sz => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => BetweenF lo 20 n) sz) lo

  -- Weight functions, in order of how much weight recursion carries. Each step is a factor, so the
  -- chain brackets every configuration between two others that differ from it visibly.
  assertFactor "heavyBase" avgHeavyBase "flat" avgFlat
  assertFactor "flat" avgFlat "balanced" avgBalanced
  assertFactor "balanced" avgBalanced "heavyRec" avgHeavyRec
  -- The modifier, against the same weight function without it.
  assertFactor "default" avgDefault "tripleRec" avgTripleRec

  IO.println "PASS"
