import Specimen.Interp
import SpecimenTest.CommonDefinitions.BinaryTree

/-!
# Learning a whole generator from its discards

`BSTInterpTest` tunes one constructor. This exercises the closure-wide loop, whose three interesting
claims are:

1. **Blame crosses call frames.** When `BST.BstNode` discards because `Between[1]` cannot satisfy its
   premise, the raw profile blames `BstNode`'s `SuchThat` step — and `rootCauses` pushes that down to
   the `≤` check inside `Between[1]` that is actually failing.
2. **The objective is a property of the generator, not of one constructor.** Closure-wide discards, not
   the root's success rate, which `backtrack` pins at 100% regardless.
3. **The search stops at a fixpoint, not a budget.** `ClosureRisk.isIdeal` holds when every remaining
   rejection is *irreducible* — so a generator that discards three quarters of its work is correctly
   left alone when no ordering could have done better, and one that discards a tenth avoidably is
   fixed.

Sampling is `IO`-seeded, so the assertions are on invariants and on which plan wins, never on counts.
-/

open Plausible Schedules Specimen Specimen.Interp

namespace SpecimenTest.InterpLearn

derive_relspec Between
derive_relspec BST

/-- Both relations, for the closure to draw on. -/
def specs : List RelSpec := [betweenRelSpec, bstRelSpec]

/-- `BST` generating its tree. -/
def bstKey : SpecKey :=
  { inductiveName := ``BST, outputIndices := [2], deriveSort := .Generator }

/-- `Between` generating its middle argument — the mode `BstNode` calls. -/
def betweenKey : SpecKey :=
  { inductiveName := ``Between, outputIndices := [1], deriveSort := .Generator }

/-- Decides `Between lo x hi`, standing in for a derived `DecOpt`. -/
def betweenDec (lo x hi : Nat) : Bool := lo < x && x < hi

/-- Leaves only; every schedule is derived through the book. -/
def leaves : InterpEnv :=
  ((({} : InterpEnv).withArbitrary ``Nat Nat).withDecidable2 ``LE.le (fun a b : Nat => a ≤ b))
    |>.addChecker ``Between (checker3 betweenDec)

/-- `BST.BstNode` as data. -/
def node : CtorSpec := (ctorSpecOf? specs bstKey ``BST.BstNode).getD default

/-- The schedule the compile-time pipeline derives, for comparison. -/
def expectedBstNode : Schedule :=
  ([ .SuchThat [(`x, none)]
       (.NonRec (``Between, [.Unknown `a_1, .Unknown `x, .Unknown `b_1])) .Generator
   , .SuchThat [(`l, none)] (.Rec `aux_bst [.Unknown `a_1, .Unknown `x]) .Generator
   , .SuchThat [(`r, none)] (.Rec `aux_bst [.Unknown `x, .Unknown `b_1]) .Generator
   ], .ProducerSchedule .Generator
        [.Ctor ``BinaryTree.Node [.Unknown `x, .Unknown `l, .Unknown `r]])

/-- A deliberately bad starting book: generate the pivot blind, then test it. -/
def badBook : PlanBook :=
  ({} : PlanBook).set bstKey ``BST.BstNode [.inst `x, .use 0, .use 1, .use 2]

/-- The empty book, i.e. whatever `deriveClosureWith` chooses by itself. -/
def defaultBook : PlanBook := {}

/-- Whether a lowering produced exactly this schedule. -/
def lowersTo (r : Except PlanError Schedule) (s : Schedule) : Bool :=
  match r with
  | .ok s' => s' == s
  | .error _ => false

/-! ## An avoidable rejection is found, blamed, and removed -/

-- The bad book is not ideal, and its one avoidable rejection is the `Between` check.
/-- info: (false, 1, "checking") -/
#guard_msgs in
#eval match leaves.deriveClosureWith specs [bstKey] badBook with
  | .error _ => (true, 0, "")
  | .ok env =>
    let risk := env.closureRisk specs (specs.map RelSpec.inductiveName)
    (risk.isIdeal, risk.avoidableTargets.length, densityRender risk.worstDensity)

-- Measured, the discards are real and land on `BstNode`'s `Between` premise — locally, since the
-- check rejects on its own account rather than inheriting from a callee.
/-- info: (true, "BST[2] as Generator", `BST.BstNode, "Between lo x hi", 0) -/
#guard_msgs in
#eval show IO (Bool × String × Lean.Name × String × Nat) from do
  match leaves.deriveClosureWith specs [bstKey] badBook with
  | .error _ => return (false, "", .anonymous, "", 0)
  | .ok env => do
    let st ← env.closureStats bstKey 4 [toVal 0, toVal 6] 200
    match (st.rootCauses env specs badBook).head? with
    | none => return (false, "", .anonymous, "", 0)
    | some b =>
      return (st.discards > 0, renderSpecKey b.key, b.ctorName,
        renderPremise specs b.key b.ctorName b.premiseIdx, b.depth)

-- Learning from the bad book reaches zero closure discards, and the plan it settles on is the one the
-- compile-time pipeline derives. The final round reports the fixpoint rather than exhausting rounds.
/-- info: (true, true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool × Bool) from do
  let (book, trace) ← leaves.learnSchedules specs bstKey 4 [toVal 0, toVal 6]
    (n := 150) (rounds := 4) (start := badBook)
  let accepted := trace.filter LearnStep.accepted
  let startedBad :=
    match (trace.head?.bind LearnStep.stats) with
    | some s => s.discards > 0
    | none => false
  let endedClean :=
    match (accepted.getLast?.bind LearnStep.stats) with
    | some s => s.discards == 0
    | none => false
  let winner :=
    match book.find? bstKey ``BST.BstNode with
    | some p => lowersTo (reschedule bstRelSpec bstKey node p) expectedBstNode
    | none => false
  let stoppedAtFixpoint := (trace.getLast?.map (fun t => t.note.startsWith "ideal")).getD false
  return (startedBad, endedClean, winner, stoppedAtFixpoint)

/-! ## Blame crosses call frames

    `BST 5 6` admits no pivot: there is no `x` with `5 < x < 6`. So `BstNode`'s very first step —
    `[x] ← Between a₁ x b₁` — fails every time, and the raw profile can only say "the `SuchThat`
    failed". The failure is really the `≤` check inside `Between[1]`. -/

-- Raw: all of `BstNode`'s discards sit on step 0, the `SuchThat`, which no mutation of `BstNode` can
-- fix.
/-- info: (`BST.BstNode, [0]) -/
#guard_msgs in
#eval show IO (Lean.Name × List Nat) from do
  match leaves.deriveClosureWith specs [bstKey] defaultBook with
  | .error _ => return (.anonymous, [])
  | .ok env => do
    let st ← env.closureStats bstKey 5 [toVal 5, toVal 6] 100
    match (st.perCtor.filter (fun t => t.1 == bstKey && t.2.2.discards > 0)).head? with
    | none => return (.anonymous, [])
    | some (_, ctor, p) =>
      return (ctor, (p.perStep.filter (fun s => s.discards > 0)).map StepDiscards.stepIdx)

-- Pushed down: the blame names `Between[1]`'s own steps instead, the heaviest being the `≤` check that
-- can never hold for a pivot strictly between 5 and 6. Two things make this a real redirection rather
-- than a coincidence: nothing is blamed on `BST[2]` at all, and the total blame *exceeds* what
-- `Between[1]` discarded on its own — the difference is exactly `BstNode`'s inherited share.
/-- info: (true, "Between[1] as Generator", "le Nat instLENat n m", true) -/
#guard_msgs in
#eval show IO (Bool × String × String × Bool) from do
  match leaves.deriveClosureWith specs [bstKey] defaultBook with
  | .error _ => return (false, "", "", false)
  | .ok env => do
    let st ← env.closureStats bstKey 5 [toVal 5, toVal 6] 100
    let causes := st.rootCauses env specs defaultBook
    let betweenLocal := (st.perCtor.filter (fun t => t.1 == betweenKey)).foldl
      (fun acc t => acc + t.2.2.discards) 0
    let totalBlamed := causes.foldl (fun acc t => acc + t.discards) 0
    match causes.head? with
    | none => return (false, "", "", false)
    | some b =>
      return (causes.all (fun t => t.key != bstKey), renderSpecKey b.key,
        renderPremise specs b.key b.ctorName b.premiseIdx, totalBlamed > betweenLocal)

/-! ## A generator that wastes most of its work, correctly left alone

    Three quarters of the closure's attempts are discarded at `BST 5 6`, and not one of them is
    avoidable: `Between` must check `≤`, and nothing produces a `Nat` satisfying it. The search says so
    and stops, rather than thrashing through orderings that cannot help. -/

/-- info: (true, true, 1) -/
#guard_msgs in
#eval show IO (Bool × Bool × Nat) from do
  match leaves.deriveClosureWith specs [bstKey] defaultBook with
  | .error _ => return (false, false, 0)
  | .ok env => do
    let st ← env.closureStats bstKey 5 [toVal 5, toVal 6] 100
    let risk := env.closureRisk specs (specs.map RelSpec.inductiveName)
    let (_, trace) ← leaves.learnSchedules specs bstKey 5 [toVal 5, toVal 6] (n := 100) (rounds := 3)
    -- Wasteful, ideal anyway, and the loop used exactly one round to say so.
    return (st.discardPerMille > 500, risk.isIdeal,
      (trace.filter (fun t => t.note.startsWith "ideal")).length)

/-! ## Phase two: the weights, not the plans

    No plan makes bigger trees. How often the recursive constructor is chosen over the base one is the
    weight function's business, and `balancedCtorWeight` — the pipeline's default — gives a base
    constructor a flat `4 * quality` against a recursive one's `size' * quality`, so the recursion
    probability is `size' / (size' + 4)`: 43% at `size' = 3`, and never a coin flip below 4. That, plus
    `numRecCalls = 2` halving the budget at every level, is why an untuned `BST` at size 4 averages
    barely two nodes.

    So phase two tunes an affine adjustment over that weighting — the shape
    `Scoring.CtorWeightModifier` already has — rather than replacing it. -/

-- The zero a recursive constructor gets at `size = 0` is what stops recursion at the bottom of the
-- budget, so it has to survive any tweak.
--
-- The `addend` cases are the ones that matter and were missing: with a multiplier alone, zero survives
-- any plausible arithmetic, so a form that adds before clamping still passed. `Nat.max (Nat.min base 1)
-- (base * mul / 1000 + addend)` returns the *addend* at base 0 — and Cedar's tuned book carries an
-- `addend := 8` arm, so a recursive constructor was reachable at `size = 0`, held back only by fuel.
/-- info: [0, 0, 0, 1, 16, 160, 168] -/
#guard_msgs in
#eval
  [ ({ mulPerMille := 16000 } : WeightTweak).apply 0        -- zero is a fixed point
  , ({ mulPerMille := 1000, addend := 8 } : WeightTweak).apply 0   -- …addend must not resurrect it
  , ({ mulPerMille := 0, addend := 99 } : WeightTweak).apply 0     -- …nor a large one
  , ({ mulPerMille := 0 } : WeightTweak).apply 16           -- …and nothing else collapses to zero
  , ({} : WeightTweak).apply 16                             -- identity
  , ({ mulPerMille := 10000 } : WeightTweak).apply 16
  , ({ mulPerMille := 10000, addend := 8 } : WeightTweak).apply 16 ]

-- The untuned generator is small for a reason that has nothing to do with its schedule: at `size' = 3`
-- the base constructor outweighs the recursive one 16 to 12.
/-- info: [(0, 16, 0), (1, 16, 4), (3, 16, 12), (4, 16, 16), (8, 16, 32)] -/
#guard_msgs in
#eval [0, 1, 3, 4, 8].map (fun s =>
  (s, balancedCtorWeight ``BST.BstLeaf [2] .Generator 0 false 0 1 1 0,
      balancedCtorWeight ``BST.BstNode [2] .Generator 0 true s 1 1 2))

-- Tuning towards a reachable goal moves the mean size a long way without giving back any discards, and
-- the tweaks land on the recursive constructors — the only ones whose weight is a free parameter.
/-- info: (true, true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool × Bool) from do
  let g ← leaves.learnGenerator specs bstKey 8 [toVal 0, toVal 1000] (n := 300) (rounds := 4)
    (goal := some { targetCenti := 1000 }) (start := badBook)
  let accepted := g.weightTrace.filter WeightStep.accepted
  let baseSize :=
    match (g.weightTrace.head?.bind WeightStep.stats) with
    | some s => s.root.avgOutputSizeCenti
    | none => 0
  let finalSize :=
    match (accepted.getLast?.bind WeightStep.stats) with
    | some s => s.root.avgOutputSizeCenti
    | none => 0
  let stillClean :=
    match (accepted.getLast?.bind WeightStep.stats) with
    | some s => s.discards == 0
    | none => false
  -- Only recursive constructors were touched.
  let onlyRec := g.weights.effective.all (fun e =>
    e.1.1 == ``BST.BstNode || e.1.1 == ``Between.BetweenS)
  return (finalSize > baseSize + 200, stillClean, onlyRec, g.weights.effective.length > 0)

-- And an unreachable goal is reported as unreachable rather than left to look like convergence.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match leaves.deriveClosureWith specs [bstKey] defaultBook with
  | .error _ => return false
  | .ok env => do
    -- No weighting gives a mean of 500 nodes at size 4.
    let (_, trace) ← env.tuneWeights specs bstKey defaultBook
      { targetCenti := 50000 } 4 [toVal 0, toVal 1000] (n := 100) (passes := 1)
    return (trace.getLast?.map (fun t => t.note.startsWith "closest reachable")).getD false

/-! ## Reproducibility

    `Plausible.Gen.run` draws its seed from the global generator, so two measurements of the same
    schedule disagree — by more, for average output size, than the effects the tuner is looking for.
    `runSeeded` fixes the seed, which makes a comparison *paired*: every candidate faces the same draws,
    so a difference between them is a difference between the schedules. `defaultSeeds` uses three, so a
    candidate cannot win on one lucky path.

    The consequence worth having is that a whole tuning run is now deterministic. -/

-- One seed, twice, is exactly equal; a different seed is not; and unseeded is neither.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  match leaves.deriveClosureWith specs [bstKey] defaultBook with
  | .error _ => return (false, false)
  | .ok env => do
    let a ← env.sample bstKey 8 [toVal 0, toVal 1000] 200 0 (seed := some 42)
    let b ← env.sample bstKey 8 [toVal 0, toVal 1000] 200 0 (seed := some 42)
    let c ← env.sample bstKey 8 [toVal 0, toVal 1000] 200 0 (seed := some 43)
    return (a.avgOutputSizeCenti == b.avgOutputSizeCenti,
            a.avgOutputSizeCenti != c.avgOutputSizeCenti)

-- And the tuner is deterministic: same seeds, same weight book, same accepted steps.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match leaves.deriveClosureWith specs [bstKey] defaultBook with
  | .error _ => return false
  | .ok env => do
    let run := fun (_ : Unit) => env.tuneWeights specs bstKey defaultBook
      { targetCenti := 1000 } 8 [toVal 0, toVal 1000] (n := 150) (passes := 2)
    let (wb₁, t₁) ← run ()
    let (wb₂, t₂) ← run ()
    let shape := fun (t : List WeightStep) =>
      (t.filter WeightStep.accepted).map (fun st => (st.ctorName, st.tweak, st.gapCenti))
    return wb₁.entries == wb₂.entries && shape t₁ == shape t₂

/-! ## Coverage, the other thing weights control

    Size is not the only distributional property a weighting decides. Cedar's hand-tuned
    `favorHasTag` modifier boosts `record`, `hasTagTt` and `unaryAppIsEmpty` and *suppresses*
    `binaryAppEqLitSame` — all in response to a coverage histogram showing those constructors sparse or
    flooding. A tuner that measures only discards and mean size cannot see any of that: two schedules
    can discard nothing and average the same size while producing wildly different shapes.

    So `RunStats.ctorCounts` counts constructor occurrences in successful outputs, and `CoverageGoal`
    lets a caller pin the shares that matter as floors and ceilings. Sparse by design — a constructor
    with no band is unconstrained. -/

-- Counting is per-occurrence, over the whole output tree, not per sample.
/-- info: (true, true, 999) -/
#guard_msgs in
#eval show IO (Bool × Bool × Nat) from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return (false, false, 0)
  | .ok env => do
    let s ← env.sample bstKey 8 [toVal 0, toVal 1000] 200 0 (seed := some 42)
    let node := s.sharePerMille ``BinaryTree.Node
    let leaf := s.sharePerMille ``BinaryTree.Leaf
    -- A binary tree of `n` internal nodes has `n + 1` leaves, so leaves always outnumber nodes; and
    -- the two shares account for everything, since `Nat` labels are literals, not constructors —
    -- `999` rather than `1000` because each share truncates on integer division.
    return (leaf > node, node > 0, node + leaf)

-- A band reports how far a share sits outside it, and nothing when inside.
/-- info: [0, 0, 0, 150, 200] -/
#guard_msgs in
#eval
  let floor : CoverageBand := { ctorName := `X, minPerMille := 300 }
  let ceiling : CoverageBand := { ctorName := `X, maxPerMille := 500 }
  [ floor.miss 300, floor.miss 900, ceiling.miss 500
  , floor.miss 150      -- 150 below the floor
  , ceiling.miss 700 ]  -- 200 above the ceiling

-- The goal sums misses across bands, and names the worst for reporting.
/-- info: (268, some (`BinaryTree.Node, 268)) -/
#guard_msgs in
#eval show IO (Nat × Option (Lean.Name × Nat)) from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return (0, none)
  | .ok env => do
    let s ← env.sample bstKey 8 [toVal 0, toVal 1000] 200 0 (seed := some 42)
    -- `Node` sits at 332‰ at this size and seed, so a 600‰ floor misses by 268; `Leaf`'s ceiling of
    -- 800‰ is satisfied at 667‰, contributing nothing.
    let goal : CoverageGoal := { bands :=
      [ { ctorName := ``BinaryTree.Node, minPerMille := 600 }
      , { ctorName := ``BinaryTree.Leaf, maxPerMille := 800 } ] }
    return goal.miss s

-- And a weight tweak moves the share in the direction the band asks for: boosting the recursive
-- constructor raises `Node`'s share, which is the lever a coverage goal pulls.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return false
  | .ok env => do
    let boosted := env.withWeightBook
      (({} : WeightBook).set ``BST.BstNode [2] .Generator { mulPerMille := 16000 })
    let a ← env.sample bstKey 8 [toVal 0, toVal 1000] 200 0 (seed := some 42)
    let b ← boosted.sample bstKey 8 [toVal 0, toVal 1000] 200 0 (seed := some 42)
    return b.sharePerMille ``BinaryTree.Node > a.sharePerMille ``BinaryTree.Node

/-! ## Moving a premise only where it can matter

    A premise's position is only meaningful relative to premises it shares a variable with. Moving it
    past an independent one cannot change which variables are bound where, so every premise keeps its
    polarity and every call keeps its callee mode: the same schedule, with two independent steps
    commuted. `SearchTree.getNeighbors`/`splitIntoChunks` call the non-commuting premises **anchors**,
    and the compile-time pipeline has always enumerated orderings per connected component
    (`enumSchedulesChunked` over `sccGroups`) rather than over all `n!`.

    So a blind permutation is the wrong move generator, and worse, `permutationsUpTo` *truncates* — at
    `LubRecord`'s 14 premises it keeps 24 of 14! and can lose the best ordering unseen. Component-wise
    enumeration is smaller **and** complete: what it omits provably lowers to a schedule it keeps. -/

-- `BST.BstNode`'s three premises all share variables (`Between lo x hi`, `BST lo x l`, `BST x hi r`
-- pairwise share `lo`/`x`/`hi`), so they are one component and nothing can be reduced — the point being
-- that this case is no *worse* than the blind enumeration it replaces.
/-- info: (3, [[`lo, `x, `hi], [`lo, `x, `l], [`x, `hi, `r]], [[1, 2], [0, 2], [0, 1]], [[0, 1, 2]]) -/
#guard_msgs in
#eval
  let n := node.hypotheses.length
  ( n
  , (List.range n).map (fun i => node.premiseVars i)
  , (List.range n).map (fun i => node.anchorsOf i)
  , node.premiseComponents )

-- One component ⇒ component-wise enumeration equals the blind one exactly.
/-- info: (6, 6) -/
#guard_msgs in
#eval ((componentOrderings node 24).length,
       (permutationsUpTo 24 (List.range node.hypotheses.length)).length)

-- Where premises are independent, the reduction is large. Four premises over four disjoint variables:
-- every one of the 4! orderings lowers to the same schedule up to commuting, so one ordering suffices.
-- Cedar's `Lub.record` is exactly this shape (4 premises, components `[1,1,1,1]`), and it takes
-- `plansOf` from 24 candidates to 4 — each of which would otherwise have cost a full measurement.
/-- info: ([[0], [1], [2], [3]], 1, 24) -/
#guard_msgs in
#eval
  let v := fun (s : Lean.Name) => ConstructorExpr.Unknown s
  let indep : CtorSpec :=
    { ctorName := `Indep
    , vars := [`a, `b, `c, `d].map (fun n => ({ name := n } : VarSpec))
    , hypotheses := [(`P, [v `a]), (`Q, [v `b]), (`R, [v `c]), (`S, [v `d])] }
  ( indep.premiseComponents
  , (componentOrderings indep 24).length
  , (permutationsUpTo 24 (List.range 4)).length )

-- `anchorMoves` emits one plan per anchor-delimited slot rather than one per position. With no anchors
-- it emits only front and back, since those two differ in how much work a rejection here throws away
-- even though the produced values are the same.
/-- info: (3, 2) -/
#guard_msgs in
#eval
  let v := fun (s : Lean.Name) => ConstructorExpr.Unknown s
  let indep : CtorSpec :=
    { ctorName := `Indep
    , vars := [`a, `b, `c, `d].map (fun n => ({ name := n } : VarSpec))
    , hypotheses := [(`P, [v `a]), (`Q, [v `b]), (`R, [v `c]), (`S, [v `d])] }
  let declared := fun (k : Nat) => (List.range k).map PlanStep.use
  ( (Plan.anchorMoves node (declared 3) 0).length      -- two anchors ⇒ 3 slots
  , (Plan.anchorMoves indep (declared 4) 0).length )   -- no anchors ⇒ front and back only

-- `plansOf` deduplicates on the *lowered schedule*, not the plan. Distinct plans routinely lower to the
-- same schedule, and measuring one twice is the most expensive thing the search can do — 115s a go on
-- Cedar. The prune is definitional, so nothing that could rank differently is dropped.
/-- info: true -/
#guard_msgs in
#eval
  let scheds := (plansOf bstRelSpec bstKey node 24).filterMap (fun (_, r) =>
    match r with | .ok s => some s | .error _ => none)
  scheds.zipIdx.all (fun (s, i) => !((scheds.take i).any (fun s' => s' == s)))

/-! ## Affording the measurement on a big closure

    `ProfileBudget` allocates attempts from measured cost instead of giving every constructor the same
    `n`. On Cedar's `HasType[0,4]` closure that is the difference between 17 minutes and 38 seconds per
    `closureStats`, because per-attempt cost there spans 1600× across 946 mode×constructor pairs.

    BST is far too uniform to show the saving, so what is pinned here is the part that has to hold for
    the saving to be *usable*: the allocation is frozen, so a measurement stays bit-identical across
    calls; the default budget is inert; and the floor keeps every pair observed. -/

-- Default-constructed, a budget changes nothing: `attemptsFor` returns the caller's `n` for every
-- pair, which is what keeps every existing call site behaving as it did.
/-- info: (false, 100, 0, 0) -/
#guard_msgs in
#eval
  let b : ProfileBudget := {}
  (b.isCalibrated, b.attemptsFor bstKey ``BST.BstNode 100, b.predictedUs, b.costs.length)

-- But a *calibrated* budget does not defer to the caller for a pair it has no row for: it gives it
-- `minAttempts`. A missing row means a mode some candidate plan newly invented, which is precisely
-- where cost is unknown — and `fallback` is the caller's `n`, the largest count in play. Deferring
-- would hand the maximum attempt count to the one mode nobody has measured, and would unbalance the
-- comparison the search depends on: the candidate would spend more attempts on its new modes than
-- the baseline ever did. Same rule as `enumWidthOf`: unknown cost is assumed expensive.
/-- info: (7, 2, 100) -/
#guard_msgs in
#eval
  let costs : List PairCost := [{ key := bstKey, ctorName := ``BST.BstLeaf, usPerAttempt := 10 }]
  let b := ProfileBudget.allocate costs (totalUs := 1000000) (maxAttempts := 7) (minAttempts := 2)
  ( b.attemptsFor bstKey ``BST.BstLeaf 100      -- measured: its allocation
  , b.attemptsFor bstKey ``BST.BstNode 100      -- calibrated but unmeasured: the floor, not 100
  , ({} : ProfileBudget).attemptsFor bstKey ``BST.BstNode 100 )  -- uncalibrated: defers

-- Allocation, cheapest first: the cheap pair takes its `maxAttempts` and the expensive one is funded
-- from what it left behind, down to the floor. With a 1s total, a 10us pair affords all 100 attempts
-- (1ms) while a 500ms pair gets the floor of 2 — the reverse order would have let the expensive pair
-- drain the budget before the cheap one was measured at all.
/-- info: (100, 2, true) -/
#guard_msgs in
#eval
  let costs : List PairCost :=
    [ { key := bstKey, ctorName := ``BST.BstLeaf, usPerAttempt := 10 }
    , { key := bstKey, ctorName := ``BST.BstNode, usPerAttempt := 500000 } ]
  let b := ProfileBudget.allocate costs (totalUs := 1000000) (maxAttempts := 100) (minAttempts := 2)
  ( b.attemptsFor bstKey ``BST.BstLeaf 0
  , b.attemptsFor bstKey ``BST.BstNode 0
  , b.isCalibrated )

-- The floor beats the budget. A pair that is never profiled reports no discards, which reads exactly
-- like a pair that discards nothing — so `minAttempts` is honoured even when it overruns `totalUs`,
-- and `predictedUs` reports the overrun rather than hiding it.
/-- info: (3, 3, 3000000) -/
#guard_msgs in
#eval
  let costs : List PairCost :=
    [ { key := bstKey, ctorName := ``BST.BstLeaf, usPerAttempt := 500000 }
    , { key := bstKey, ctorName := ``BST.BstNode, usPerAttempt := 500000 } ]
  let b := ProfileBudget.allocate costs (totalUs := 1000) (maxAttempts := 100) (minAttempts := 3)
  ( b.attemptsFor bstKey ``BST.BstLeaf 0
  , b.attemptsFor bstKey ``BST.BstNode 0
  , b.predictedUs )  -- 6 attempts × 500ms, well past the 1ms asked for

-- A calibrated budget is measured from a clock, but only once: the allocation is then frozen, so two
-- measurements under the same budget and seed agree exactly. This is what the paired-seed comparison
-- in `learnSchedules` needs, and what a live wall-clock budget would have destroyed — the attempt
-- count would drift with machine load and every rate derived from it would drift too.
/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return (false, false, false)
  | .ok env => do
    let inputs := [toVal 0, toVal 1000]
    let budget ← env.calibratedBudget 6 inputs (totalUs := 2000000) (maxAttempts := 40)
    let a ← env.closureStats bstKey 6 inputs 40 (some 7) budget
    let b ← env.closureStats bstKey 6 inputs 40 (some 7) budget
    return ( budget.isCalibrated
           , a.attempts == b.attempts
           , a.discardPerMille == b.discardPerMille )

-- Every pair in the closure is allocated something, and no pair exceeds `maxAttempts`. Both matter:
-- a missing pair is silently invisible to blame attribution, and an over-allocated one is the cost
-- the budget exists to bound.
/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return (false, false, false)
  | .ok env => do
    let pairs := env.relations.toList.foldl (fun acc p => acc + p.2.allSchedules.length) 0
    let budget ← env.calibratedBudget 6 [toVal 0, toVal 1000] (maxAttempts := 40)
    return ( budget.attempts.length == pairs
           , budget.attempts.all (fun (_, _, a) => a ≥ 2 && a ≤ 40)
           , budget.costs.all (fun c => c.usPerAttempt ≥ 1) )

-- A cost table is size-specific, and silently allocating from the wrong size is worse than failing:
-- `size` is the generation depth budget, so per-attempt cost climbs steeply with it. The budget
-- records the size it was measured at and `closureStats` refuses a mismatch.
/-- info: (6, true) -/
#guard_msgs in
#eval show IO (Nat × Bool) from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return (0, false)
  | .ok env => do
    let inputs := [toVal 0, toVal 1000]
    let budget ← env.calibratedBudget 6 inputs (maxAttempts := 20)
    -- Same size: fine. Different size: refused, rather than allocating from numbers that do not apply.
    let _ ← env.closureStats bstKey 6 inputs 20 (some 7) budget
    let refused ← (do let _ ← env.closureStats bstKey 12 inputs 20 (some 7) budget; pure false)
      |>.catchExceptions (fun _ => pure true)
    return (budget.size, refused)

-- `workUs` is the cost statistic `enumWalked` cannot supply. `enumCosts` covers only `.Enumerator`
-- modes and is measured once per mode, so on the Cedar run it read a constant 785 while wall-clock
-- went 13s → 208s: generator cost is invisible to it. `workUs`/`wastedUs` are recorded by
-- `closureStats` from the budget that shaped it, and are `0` without a cost model rather than
-- silently wrong — which is what makes the fallback in `wastePerMille` decidable.
/-- info: (true, true, false, 0) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool × Nat) from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return (false, false, false, 0)
  | .ok env => do
    let inputs := [toVal 0, toVal 1000]
    let budget ← env.calibratedBudget 6 inputs (maxAttempts := 40)
    let s ← env.closureStats bstKey 6 inputs 40 (some 7) budget
    let plain ← env.closureStats bstKey 6 inputs 40 (some 7)
    return ( s.workUs > 0, s.hasCostModel
           , plain.hasCostModel, plain.workUs )  -- no budget ⇒ no cost model, not a wrong one

-- With no cost model `wastePerMille` *is* `discardPerMille`, so an uncalibrated run ranks exactly as
-- it did before work entered the objective. This is what keeps every pre-existing trace intact.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return false
  | .ok env => do
    let s ← env.closureStats bstKey 6 [toVal 0, toVal 1000] 40 (some 7)
    return s.wastePerMille == s.discardPerMille && s.objective.1 == s.discardPerMille

-- And with a cost model it is a genuinely different number: waste weights each discard by what it
-- cost, so it only coincides with the count-based rate when every pair costs the same. Both are
-- proper rates, so both stay inside 1000.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  match leaves.deriveClosure specs [bstKey] with
  | .error _ => return (false, false)
  | .ok env => do
    let inputs := [toVal 0, toVal 1000]
    let budget ← env.calibratedBudget 6 inputs (maxAttempts := 40)
    let s ← env.closureStats bstKey 6 inputs 40 (some 7) budget
    return (s.wastePerMille ≤ 1000, s.wastedUs ≤ s.workUs)

/-! ## Rule paths

`withRulePaths` records paths through the *rules* rather than through the generated value, and it does so
from a path threaded down the interpreter on every constructor attempt — whether or not anything is
recording. That made the construction worth being careful about: it is held newest-first and truncated to
`rulePathDepth` on the way down, so the cost per attempt is a cons rather than an O(depth) append.

This pins the two properties that truncation could plausibly have broken: recorded paths are at most
`rulePathDepth` long, and they read root-first (the same direction `renderPath` prints). -/
/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  match leaves.deriveClosureWith specs [bstKey] ({} : PlanBook) with
  | .error _ => return (false, false, false)
  | .ok env => do
    let (_, paths) ← withRulePaths do
      let _ ← env.sample bstKey 4 [toVal 0, toVal 6] 40 0 (some 7)
    return (!paths.isEmpty,
      paths.all (fun p => p.length ≤ Specimen.Interp.rulePathDepth),
      -- Every recorded path starts at a constructor of the root relation, which is what "root-first"
      -- means here: reversing the internal newest-first order must put the outermost rule at the head.
      paths.all (fun p => match p.head? with
        | some n => specs.any (fun r => r.ctors.any (fun c => c.ctorName == n))
        | none => false))

/-! ## Accepting on coverage

Under `.coverage`, acceptance needs a real coverage gain — a strict superset of paths, or more distinct
paths — and never speed alone, whose 5% margin sits inside wall-clock noise. The net case is the one the
old strict-superset gate refused: more paths overall, one lost. -/
def withPaths (ps : List (List Lean.Name)) : ClosureStats :=
  { root := { kPathsSeen := ps.map (fun p => (p, 1)) } }

/-- info: (true, false, false, true) -/
#guard_msgs in
#eval
  let a := withPaths [[`x], [`y], [`z]]
  let b := withPaths [[`x], [`y]]
  let net := withPaths [[`x], [`z], [`w]]   -- loses `y`, gains `z` and `w`
  (coverageGain a b, coverageGain b a, coverageGain a a, coverageGain net b)

end SpecimenTest.InterpLearn
