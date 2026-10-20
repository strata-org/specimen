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
-- Define 4 copies of Between to get separate instances
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
-- Section 5: Sample and check distribution relationships
--
-- Between lo hi n generates n in [lo, hi]. The generated value minus lo
-- equals the number of `there` steps taken. So the average (n - lo)
-- directly reflects how often the recursive constructor is chosen.
-- ============================================================

/-- Any fixed value works. The point is that the averages below come from a reproducible stream
    instead of the ambient RNG, whose state at this point depends on whatever ran before. -/
private def sampleSeed : Nat := 20261020

/-- Draws behind each average, large enough that the narrowest of the three gaps compared below,
    flat against balanced at about 8%, stands clear of the sampling spread. -/
private def sampleTrials : Nat := 5000

/-- Average of `n - lo` over `sampleTrials` draws of `gen`, taken from one seeded stream, or an
    error naming `label` if there is no average to report.

    A missing measurement is an error rather than a zero: zero is a plausible-looking average that
    satisfies most of the orderings asserted below, so a generator that produced nothing at all would
    read as a pass.

    One stream rather than a seeded run per draw: reseeding every draw correlates its first value
    across draws, and that value is what picks the constructor, so the average would stop reflecting
    the weights. The run size cycles over `size` to `size + 10`, so each average spans sizes. -/
private def avgOffset (label : String) (gen : Nat → Gen Nat) (lo : Nat) (size : Nat := 8) :
    Except String Float :=
  let loop : Gen (Nat × Nat) := do
    let mut totalOffset : Nat := 0
    let mut successes : Nat := 0
    for i in [:sampleTrials] do
      try
        let n ← Gen.resize (fun _ => size + i % 11) (gen size)
        totalOffset := totalOffset + (n - lo)
        successes := successes + 1
      catch _ => pure ()
    return (totalOffset, successes)
  match (runRandWith sampleSeed loop).run (ULift.up size) with
  | .error (.genError msg) => .error s!"FAIL: {label}: the seeded stream failed: {msg}"
  | .ok (_, 0) => .error s!"FAIL: {label}: all {sampleTrials} draws failed, no average to compare"
  | .ok (totalOffset, successes) => .ok (totalOffset.toFloat / successes.toFloat)

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

  -- heavyBase should produce values closer to lo (fewer recursive steps)
  unless avgHeavyBase < avgBalanced do
    throw <| IO.userError s!"FAIL: Expected heavyBase ({avgHeavyBase}) < balanced ({avgBalanced})"
  -- tripleRec modifier should produce values further from lo (more recursive steps)
  unless avgTripleRec > avgBalanced do
    throw <| IO.userError s!"FAIL: Expected tripleRec ({avgTripleRec}) > balanced ({avgBalanced})"
  -- flat should produce values closer to lo than balanced (no size-boosting of rec)
  unless avgFlat < avgBalanced do
    throw <| IO.userError s!"FAIL: Expected flat ({avgFlat}) < balanced ({avgBalanced})"

  IO.println "PASS"
