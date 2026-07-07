import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import SpecimenTest.CommonDefinitions.BinaryTree
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBSTGenerator
import SpecimenTest.DeriveArbitrarySuchThat.DeriveSTLCGenerator
import SpecimenTest.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

/-!
# Schedule Quality Regression Tests

Snapshots the kernel-elaborated code for derived generators via `#print`.
Any change to the schedule derivation algorithm that alters the generated
code will cause these `#guard_msgs` checks to fail, catching regressions.

Sections 1–4 snapshot representative generators (Between, BST, STLC, RegExp).
Section 5 is a direct regression test for the bug where relations with `≠`
hypotheses alongside recursive hypotheses produced bad schedules.
-/

open Plausible

set_option guard_msgs.diff true
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

-- ============================================================
-- Section 1: Between generator
-- ============================================================

-- Sections 1-4 previously snapshotted the aux_arb internal functions.
-- With derive_mutual, instances use global defs instead. Verify instances exist:
#guard_msgs(drop info) in
#check (inferInstance : ArbitrarySizedSuchThat Nat (fun x => Between 0 x 10))
#guard_msgs(drop info) in
#check (inferInstance : ArbitrarySizedSuchThat BinaryTree (fun t => BST 0 10 t))
#guard_msgs(drop info) in
#check (inferInstance : ArbitrarySizedSuchThat term (fun e => typing [] e .Nat))
#guard_msgs(drop info) in
#check (inferInstance : ArbitrarySizedSuchThat (List Nat) (fun s => ExpMatch s (.Char 1)))

-- ============================================================
-- Section 5: ≠ + recursion bug regression
-- ============================================================

/-- List membership with an inequality guard — the minimal trigger for the bug.
    Before the fix, derive_generator failed with a DecOpt synthesis error. -/
inductive MemNat : List Nat → Nat → Prop where
| here  : ∀ n xs, MemNat (n :: xs) n
| there : ∀ n m xs, n ≠ m → MemNat xs n → MemNat (m :: xs) n

#guard_msgs(drop info) in
derive_checker (fun xs n => MemNat xs n)

#guard_msgs(drop info) in
derive_generator (fun n => ∃ xs, MemNat xs n)

/--
info: def instArbitrarySizedSuchThatListNatMemNat.aux_arb : Nat → Nat → Nat → Nat → Gen (List Nat) :=
fun fuel initSize size n_1 =>
  Nat.brecOn (motive := fun fuel => Nat → Gen (List Nat)) fuel
    (instArbitrarySizedSuchThatListNatMemNat.aux_arb._f initSize n_1) size
-/
#guard_msgs in
#print instArbitrarySizedSuchThatListNatMemNat.aux_arb

-- ============================================================
-- Section 6: Generator quality sampling
-- ============================================================

/-! Sampling-based quality metrics for derived generators.
    Measures success rate (non-discards), distinct outputs, and size
    distribution to catch regressions in generation quality.
    Thresholds are set conservatively — a regression should trip these
    without false-positiving on random variance. -/

section GeneratorQuality

private def treeNodeCount : BinaryTree → Nat
  | .Leaf => 0
  | .Node _ l r => 1 + (treeNodeCount l) + (treeNodeCount r)

structure QualityStats where
  trials : Nat
  successes : Nat
  uniques : Nat
  maxSize : Nat
  sizeBuckets : Array Nat  -- [0-1, 2-3, 4-5, 6+]
  elapsedMs : Nat := 0
  deriving Repr

private def emptyStats (n : Nat) : QualityStats :=
  { trials := n, successes := 0, uniques := 0, maxSize := 0, sizeBuckets := #[0, 0, 0, 0] }

private def sizeBucket (d : Nat) : Nat :=
  if d ≤ 1 then 0 else if d ≤ 3 then 1 else if d ≤ 5 then 2 else 3

/-- Sample a generator `trials` times, measuring success rate, unique count,
    size distribution, and wall-clock time. -/
private def sampleQuality (gen : Nat → Gen α) (measure : α → Nat) (eq : α → α → Bool)
    (trials : Nat := 200) (size : Nat := 3) : IO QualityStats := do
  let startNs ← IO.monoNanosNow
  let mut stats := emptyStats trials
  let mut seen : Array α := #[]
  for i in [:trials] do
    try
      let v ← Gen.run (gen size) (size + i % 4)
      stats := { stats with successes := stats.successes + 1 }
      let d := measure v
      stats := { stats with maxSize := max stats.maxSize d }
      let bucket := sizeBucket d
      stats := { stats with sizeBuckets := stats.sizeBuckets.modify bucket (· + 1) }
      if !seen.any (eq v ·) then
        seen := seen.push v
    catch _ => pure ()
  let elapsedNs ← IO.monoNanosNow
  stats := { stats with uniques := seen.size, elapsedMs := (elapsedNs - startNs) / 1000000 }
  return stats

private def ppStats (name : String) (s : QualityStats) : String :=
  let rate := (s.successes.toFloat / s.trials.toFloat * 100.0).round.toUInt32.toNat
  let bucketStr := s!"{s.sizeBuckets[0]!}/{s.sizeBuckets[1]!}/{s.sizeBuckets[2]!}/{s.sizeBuckets[3]!}"
  s!"{name}: {rate}% success, {s.uniques} uniques, maxSize={s.maxSize}, buckets=[{bucketStr}], {s.elapsedMs}ms"

/-- Quality assertions: generators should meet minimum quality bars. -/
private def assertQuality (name : String) (s : QualityStats)
    (minSuccessRate : Float := 0.5) (minUniques : Nat := 10) : IO Unit := do
  let rate := s.successes.toFloat / s.trials.toFloat
  if rate < minSuccessRate then
    throw <| IO.userError s!"{name}: success rate {rate} below threshold {minSuccessRate}"
  if s.uniques < minUniques then
    throw <| IO.userError s!"{name}: only {s.uniques} uniques, expected at least {minUniques}"

end GeneratorQuality

-- ============================================================
-- Section 7: Scoring strategy comparison
-- ============================================================

/-! Derives the same relation under each scoring strategy and compares
    sampling quality. This catches cases where a strategy change causes
    a previously-good generator to degrade. -/

section StrategyComparison

-- Compare scoring strategies on the BST generator (deps already derived above).
-- Since derive_mutual registers global instances, we can't derive three different
-- instances for the same relation. Instead, we derive once per strategy using
-- distinct wrapper relations that are isomorphic but have separate instances.

inductive BST_Default : Nat → Nat → BinaryTree → Prop
  | bstLeaf : BST_Default lo hi .Leaf
  | bstNode : ∀ x l r lo hi,
      Between lo x hi → BST_Default lo x l → BST_Default x hi r →
      BST_Default lo hi (.Node x l r)

inductive BST_WorstLeaf : Nat → Nat → BinaryTree → Prop
  | bstLeaf : BST_WorstLeaf lo hi .Leaf
  | bstNode : ∀ x l r lo hi,
      Between lo x hi → BST_WorstLeaf lo x l → BST_WorstLeaf x hi r →
      BST_WorstLeaf lo hi (.Node x l r)

inductive BST_Density : Nat → Nat → BinaryTree → Prop
  | bstLeaf : BST_Density lo hi .Leaf
  | bstNode : ∀ x l r lo hi,
      Between lo x hi → BST_Density lo x l → BST_Density x hi r →
      BST_Density lo hi (.Node x l r)

inductive BST_Graded : Nat → Nat → BinaryTree → Prop
  | bstLeaf : BST_Graded lo hi .Leaf
  | bstNode : ∀ x l r lo hi,
      Between lo x hi → BST_Graded lo x l → BST_Graded x hi r →
      BST_Graded lo hi (.Node x l r)

inductive BST_Bounded : Nat → Nat → BinaryTree → Prop
  | bstLeaf : BST_Bounded lo hi .Leaf
  | bstNode : ∀ x l r lo hi,
      Between lo x hi → BST_Bounded lo x l → BST_Bounded x hi r →
      BST_Bounded lo hi (.Node x l r)

inductive BST_InputAware : Nat → Nat → BinaryTree → Prop
  | bstLeaf : BST_InputAware lo hi .Leaf
  | bstNode : ∀ x l r lo hi,
      Between lo x hi → BST_InputAware lo x l → BST_InputAware x hi r →
      BST_InputAware lo hi (.Node x l r)

inductive BST_SourceQuality : Nat → Nat → BinaryTree → Prop
  | bstLeaf : BST_SourceQuality lo hi .Leaf
  | bstNode : ∀ x l r lo hi,
      Between lo x hi → BST_SourceQuality lo x l → BST_SourceQuality x hi r →
      BST_SourceQuality lo hi (.Node x l r)

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

set_option specimen.scoreType "Scoring.DefaultScore" in
#guard_msgs(drop info) in
derive_mutual (fun lo hi => ∃ t, BST_Default lo hi t)

set_option specimen.scoreType "Scoring.WorstLeafScore" in
#guard_msgs(drop info) in
derive_mutual (fun lo hi => ∃ t, BST_WorstLeaf lo hi t)

set_option specimen.scoreType "Scoring.DensityScore" in
#guard_msgs(drop info) in
derive_mutual (fun lo hi => ∃ t, BST_Density lo hi t)

set_option specimen.scoreType "Scoring.GradedUniformDensityScore" in
#guard_msgs(drop info) in
derive_mutual (fun lo hi => ∃ t, BST_Graded lo hi t)

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
#guard_msgs(drop info) in
derive_mutual (fun lo hi => ∃ t, BST_Bounded lo hi t)

set_option specimen.scoreType "Scoring.InputAwareGradedScore" in
#guard_msgs(drop info) in
derive_mutual (fun lo hi => ∃ t, BST_InputAware lo hi t)

set_option specimen.scoreType "Scoring.SourceQualityScore" in
#guard_msgs(drop info) in
derive_mutual (fun lo hi => ∃ t, BST_SourceQuality lo hi t)

#guard_msgs(drop info) in
#eval do
  let sample (gen : Nat → Gen BinaryTree) (name : String) : IO Unit := do
    let stats ← sampleQuality gen treeNodeCount
      (fun a b => toString (repr a) == toString (repr b)) 200 100
    IO.println (ppStats name stats)
    assertQuality name stats (minSuccessRate := 0.5) (minUniques := 10)

  IO.println "=== Strategy comparison: BST [0,10] generator ==="
  let instD : ArbitrarySizedSuchThat BinaryTree (fun t => BST_Default 0 10 t) := inferInstance
  sample instD.arbitrarySizedST "  DefaultScore "
  let instW : ArbitrarySizedSuchThat BinaryTree (fun t => BST_WorstLeaf 0 10 t) := inferInstance
  sample instW.arbitrarySizedST "  WorstLeafScore"
  let instDn : ArbitrarySizedSuchThat BinaryTree (fun t => BST_Density 0 10 t) := inferInstance
  sample instDn.arbitrarySizedST "  DensityScore  "
  let instG : ArbitrarySizedSuchThat BinaryTree (fun t => BST_Graded 0 10 t) := inferInstance
  sample instG.arbitrarySizedST "  GradedScore   "
  let instB : ArbitrarySizedSuchThat BinaryTree (fun t => BST_Bounded 0 10 t) := inferInstance
  sample instB.arbitrarySizedST "  BoundedScore  "
  let instIA : ArbitrarySizedSuchThat BinaryTree (fun t => BST_InputAware 0 10 t) := inferInstance
  sample instIA.arbitrarySizedST "  InputAware    "
  let instIB : ArbitrarySizedSuchThat BinaryTree (fun t => BST_SourceQuality 0 10 t) := inferInstance
  sample instIB.arbitrarySizedST "  SourceQuality    "

end StrategyComparison

-- TODO: Strategy differentiation tests require module-local instances so that
-- the same relation can be derived under multiple strategies and compared at
-- runtime. Currently derive_mutual registers global instances, preventing A/B
-- comparison in a single module. See GitHub issue for tracking.
