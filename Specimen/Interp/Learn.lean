import Specimen.Interp.Runner
import Specimen.Interp.CheckEnum

/-!
# Learning a whole generator from measurements

`InterpEnv.tunePlan` hill-climbs one constructor of one mode. That is enough to show the idea and not
enough to be the idea: a generator is every constructor of every mode in the closure, and the
constructor whose discards you can see is often not the one at fault.

This module closes those two gaps.

## Blame that crosses call frames

The interpreter attributes a discard to the step that caused it, and `blaming` re-tags a sub-producer's
failure with the *calling* step's index, so each frame reports where its own attempt died. Good for the
caller, useless for the culprit: if `BST.BstNode` discards because `Between[1]` is a poor generator, the
caller's profile blames `[x] ← Between a₁ x b₁` and no mutation of `BstNode`'s premises will help.

`rootCauses` follows the discards down. A `SuchThat` step's blame is *redirected* to the mode it calls
— the static call edge is already known (`StepRisk.viaCallee`) — and the walk continues until it
reaches a step that genuinely rejects on its own: a `Check` or a `Match`. What comes back is a ranked
list of `(mode, constructor, premise)` triples, which is what a mutation can act on.

## An objective that is a property of the generator

The top-level success rate is the wrong thing to optimise, and not by a little: `backtrack` falls
through to another constructor whenever one rejects, so a `BST` generator reports 100% success no
matter how bad `BstNode` is — it just returns `Leaf` more often. `ClosureStats` measures instead the
discards summed over *every* constructor of *every* mode, against the average size of what the root
produces. That falls when a schedule stops throwing work away and when it stops collapsing to base
cases, which is what "better generator" means here.

## Knowing when to stop

Not every rejection is a defect. `Between`'s `n ≤ m` check is irreducible: nothing produces a `Nat`
satisfying `≤`, so no ordering removes it. `estimateRisk` already separates those from the avoidable
ones, so the search has a real fixpoint rather than a round budget — **stop when every rejecting step
in the closure is irreducible**. `ClosureRisk.isIdeal` is that test.

This is ideal in a precise and limited sense: *nothing is discarded that a different plan could have
avoided*. It says nothing about the output *distribution* — a discard-free generator can still be
badly skewed — and no local search over plans could certify that without a target measure to compare
against.
-/

open Lean Plausible Schedules

namespace Specimen.Interp

/-- The `CtorSpec` for one constructor of one mode, looked up in the specs. -/
def ctorSpecOf? (specs : List RelSpec) (key : SpecKey) (ctorName : Name) : Option CtorSpec :=
  (specs.find? (fun r => r.inductiveName == key.inductiveName)).bind
    (fun r => r.ctors.find? (fun c => c.ctorName == ctorName))

/-- How a blamed premise reads, for reports. -/
def renderPremise (specs : List RelSpec) (key : SpecKey) (ctorName : Name)
    (premiseIdx : Option Nat) : String :=
  match premiseIdx with
  | none => "<conclusion match>"
  | some i =>
    match ctorSpecOf? specs key ctorName with
    | some c => (c.hypotheses[i]?).elim s!"premise #{i}" ppHypothesisExpr
    | none => s!"premise #{i}"

/-! ## Static risk over the whole closure -/

/-- Every registered mode's every constructor, with its estimated risk. -/
structure ClosureRisk where
  /-- `(mode, constructor, risk)`, in registration order. -/
  perCtor : List (SpecKey × Name × ScheduleRisk) := []
  deriving Repr

namespace ClosureRisk

/-- Every rejecting step anywhere in the closure that a different plan could remove, worst first.
    These are the search's targets; when the list is empty there is nothing left to fix. -/
def avoidableTargets (r : ClosureRisk) : List (SpecKey × Name × StepRisk) :=
  let all := r.perCtor.flatMap (fun (key, ctor, risk) =>
    (risk.steps.filter StepRisk.avoidable).map (fun s => (key, ctor, s)))
  -- Heaviest first: a rejection that throws away more work is the more valuable one to remove.
  all.foldl (fun acc t =>
    let rec ins : List (SpecKey × Name × StepRisk) → List (SpecKey × Name × StepRisk)
      | [] => [t]
      | u :: us => if t.2.2.wasted > u.2.2.wasted then t :: u :: us else u :: ins us
    ins acc) []

/-- Whether every remaining rejection is irreducible — the search's fixpoint.

    Not "nothing rejects": `Between` must check `≤`, and a schedule that must reject is not a schedule
    that could be improved. -/
def isIdeal (r : ClosureRisk) : Bool := r.avoidableTargets.isEmpty

/-- The worst density anywhere in the closure. -/
def worstDensity (r : ClosureRisk) : Density :=
  r.perCtor.foldl (fun acc (_, _, risk) => densityWorse acc risk.density) .Total

/-- A one-line summary. -/
def renderLine (r : ClosureRisk) : String :=
  let n := r.avoidableTargets.length
  s!"{r.perCtor.length} constructor(s) across the closure · worst {densityRender r.worstDensity} \
    · {n} avoidable rejection(s)"

end ClosureRisk

/-- Estimates the risk of every constructor of every registered mode. -/
def InterpEnv.closureRisk (env : InterpEnv) (specs : List RelSpec := [])
    (derivable : List Name := []) : ClosureRisk :=
  { perCtor := env.relations.toList.flatMap (fun (p : SpecKey × RelSchedule) =>
      p.2.allSchedules.map (fun (ctor, sched) =>
        (p.1, ctor, env.estimateRisk p.1 sched specs derivable))) }

/-! ## Measured discards over the whole closure -/

/-- What a whole closure actually does, measured. -/
structure ClosureStats where
  /-- Per-constructor discard profiles, one per constructor of every registered mode. -/
  perCtor : List (SpecKey × Name × CtorProfile) := []
  /-- Sampling the root mode from the top, for output size. -/
  root : RunStats := {}
  /-- What each *enumerator* mode's enumeration costs to walk: `(mode, cost)`.

      A checker pays this per step that consults the mode — `enumeratingOpt` applies the check to
      every element — and no density or discard figure reveals it: an enumerator that always produces
      is `Total` whether it yields one candidate or ten thousand. Empty when the closure has no
      enumerator modes, which is the case for a pure generator closure. -/
  enumCosts : List (SpecKey × EnumCost) := []
  /-- Microseconds of generation work this measurement represents: each pair's attempts weighted by
      its measured per-attempt cost. `0` when the measurement ran without a calibrated
      `ProfileBudget`, which is the signal that there is no cost model to reason with. -/
  workUs : Nat := 0
  /-- Of that work, the microseconds thrown away: each pair's *discards* weighted by the same cost.
      This is what a discard actually costs, as opposed to how many there were. -/
  wastedUs : Nat := 0
  /-- Wall-clock microseconds the **root** sample took, for `usPerSuccess`.

      Measured rather than modelled because this is the number a user of the generator experiences, and
      because on Cedar it turned out to be the only one that matters: four accepted plans improved
      `wastePerMille` by 16‰ and moved throughput by **0** (90/sec at size 4, both before and after).
      Root success there is 100%, so `backtrack` absorbs every per-constructor rejection cheaply against
      the interpretation cost of the successful path — which dominates. -/
  rootUs : Nat := 0
  deriving Repr, Inhabited

namespace ClosureStats

/-- Discards summed over every constructor of every mode. -/
def discards (s : ClosureStats) : Nat :=
  s.perCtor.foldl (fun acc (_, _, p) => acc + p.discards) 0

/-- Attempts summed the same way, **excluding those that hit interpreter misconfiguration**.

    An attempt that died on a missing leaf or a type-wrong input measured nothing: it neither succeeded
    nor was discarded by the schedule. Counting it would deflate the discard rate and inflate the work.
    This matters in practice because `closureStats` profiles each mode on the *root's* inputs, and for a
    mode of unrelated arity those are the wrong values — a leaf checker handed a `Capabilities` where it
    wanted an `ActionSchema` reports a shape error rather than answering `false`. On Cedar's closure that
    was 33 of 587 generator pairs. -/
def attempts (s : ClosureStats) : Nat :=
  s.perCtor.foldl (fun acc (_, _, p) => acc + (p.attempts - min p.attempts p.interpErrors)) 0

/-- Closure-wide discard rate in per mille, counting every discard equally. -/
def discardPerMille (s : ClosureStats) : Nat :=
  if s.attempts == 0 then 1000 else s.discards * 1000 / s.attempts

/-- Whether this measurement carries a cost model, i.e. ran under a calibrated `ProfileBudget`. -/
def hasCostModel (s : ClosureStats) : Bool := s.workUs > 0

/-- **The primary objective**: the fraction of generation work that was thrown away, in per mille.

    `discardPerMille` counts discards; this weights each one by what it cost. The two differ by a lot,
    for two independent reasons.

    First, a discard is not a unit of work. An attempt that fails on its first premise and one that
    fails after generating a whole `TypeEnv` both count as one discard, and on Cedar's `HasType` closure
    per-attempt cost spans **1600×** — from ~0.05ms to 603ms. Counting them equally tells the search
    that trading one expensive discard for two cheap ones is a regression, when it is a large win.

    Second, and more insidiously: `discardPerMille` is a *pooled* rate, `Σdiscards / Σattempts`, so each
    pair's influence on it is proportional to its attempt count. Under a flat `n` every pair counted
    equally. Under a `ProfileBudget` the cheap pairs get 100 attempts and the expensive ones get the
    floor of 2 — so the budget that made the measurement affordable also made the objective ~50× more
    sensitive to the pairs where a discard is *cheapest*. Exactly backwards, and invisible unless the
    weighting is made explicit. Weighting by cost removes the allocation from the objective entirely:
    two allocations of the same closure agree on `wastePerMille` even though they disagree on
    `discardPerMille`.

    Falls back to `discardPerMille` with no cost model, so an uncalibrated run ranks exactly as it did
    before this existed. -/
def wastePerMille (s : ClosureStats) : Nat :=
  if !s.hasCostModel then s.discardPerMille else s.wastedUs * 1000 / s.workUs

/-- Generation work per successful root sample. Normalised because the raw total scales with the
    allocation, which is not a property of the schedule. -/
def workPerSuccess (s : ClosureStats) : Nat :=
  if s.root.successes == 0 then s.workUs else s.workUs / s.root.successes

/-- **Microseconds per successful root sample** — measured throughput, inverted so lower is better.

    A generator with no successes is worst, not free. -/
def usPerSuccess (s : ClosureStats) : Nat :=
  if s.root.successes == 0 then 1000000000 else s.rootUs / s.root.successes

/-- Total enumeration elements a checker would walk across the closure — the cost that discards do
    not capture. -/
def enumWalked (s : ClosureStats) : Nat :=
  s.enumCosts.foldl (fun acc p => acc + p.2.walked) 0

/-- Whether any enumeration hit its cap, so `enumWalked` is a lower bound. -/
def enumTruncated (s : ClosureStats) : Bool :=
  s.enumCosts.any (fun p => p.2.truncated)

/-- Interpreter misconfiguration seen anywhere. Anything but `0` invalidates the rest. -/
def interpErrors (s : ClosureStats) : Nat :=
  s.perCtor.foldl (fun acc (_, _, p) => acc + p.interpErrors) 0

/-- Enumeration elements walked per successful root sample — the cost that discards do not capture.

    Normalised, because the raw total scales with `n` and with the number of enumerator modes, neither
    of which is a property of the schedule. `0` when the closure has no enumerator modes, which is the
    case for a pure generator closure and correctly makes this dimension inert there. -/
def enumPerSuccess (s : ClosureStats) : Nat :=
  if s.enumCosts.isEmpty then 0
  else if s.root.successes == 0 then s.enumWalked
  else s.enumWalked / s.root.successes

/-- Ranking key, lower is better.

    1. **Discard rate**, the work thrown away outright.
    2. **Enumeration walked per success.** A checker pays for every element of every sub-enumeration it
       consults (`enumeratingOpt` applies the check to each one), so two plans can discard identically
       while one makes the checker sift ten times as many candidates. Density cannot see this — an
       enumerator that always produces is `Total` whether it yields one candidate or ten thousand — so
       without this dimension the search is blind to the dominant cost of a checker closure.
    3. **Output size**, preferring *larger*, since a generator that collapses to base cases discards
       nothing and produces nothing of interest.

    Discards rank above enumeration because a discard wastes work already done, whereas a long
    enumeration is work that at least might succeed.

    Work enters through dimension 1 rather than as a fourth key, which would be theatre: the ordering is
    lexicographic and `wastePerMille` ties only by coincidence, so a fourth key would essentially never
    be consulted. Cost has to weight the dimension that already decides, or it does not participate. -/
def objective (s : ClosureStats) : Nat × Nat × Nat :=
  (s.wastePerMille, s.enumPerSuccess, 100000 - min 100000 s.root.avgOutputSizeCenti)

/-- Lexicographic comparison on `objective`. -/
def better (a b : ClosureStats) : Bool :=
  let (a₁, a₂, a₃) := a.objective
  let (b₁, b₂, b₃) := b.objective
  if a₁ != b₁ then a₁ < b₁ else if a₂ != b₂ then a₂ < b₂ else a₃ < b₃

/-- A one-line summary. -/
def renderLine (s : ClosureStats) : String :=
  let enum :=
    if s.enumCosts.isEmpty then ""
    else s!" · enum walked {s.enumWalked}{if s.enumTruncated then "+" else ""}"
  -- Both rates when there is a cost model, because the gap between them is the interesting part.
  let waste :=
    if !s.hasCostModel then ""
    else s!" · waste {s.wastePerMille / 10}.{s.wastePerMille % 10}% \
      ({s.wastedUs / 1000}/{s.workUs / 1000}ms)"
  s!"discards {s.discardPerMille / 10}.{s.discardPerMille % 10}% ({s.discards}/{s.attempts})\
    {waste} · root {s.root.renderLine}{enum}"

end ClosureStats

/-- Which objective a search optimises.

    `waste` is `(wastePerMille, enumPerSuccess, −size)`: the fraction of generation *work* thrown away.
    It is the right question when the aim is "which premise is wasting effort", and it is what
    `rootCauses` attributes against.

    `throughput` is `(usPerSuccess, −size)`: measured microseconds per successful root sample. Use it
    when the aim is "make the generator fast", which is usually the actual aim. On Cedar the two
    disagree completely — four plans that improved `waste` by 16‰ left throughput bit-identical — because
    root success is 100% and `backtrack` absorbs per-constructor rejections against an interpretation
    cost that dominates. `throughput` is also **~15× cheaper to measure**, since it needs only the root
    sample (2.2s) and not a 587-pair closure profile (32s).

    Default stays `waste` so existing traces are unchanged; pass `throughput` deliberately. -/
inductive ObjectiveKind where
  /-- Fraction of generation work discarded. -/
  | waste
  /-- Measured microseconds per successful root sample. -/
  | throughput
  /-- Distinct k-paths reached, with cost only as a tie-break. See `betterBy`. -/
  | coverage
  deriving Repr, BEq, Inhabited

/-- Whether `a` reaches every shape `b` does. The containment half of coverage, which is what makes a
    regression a *fact* rather than a threshold judgement. -/
def coversAtLeast (a b : ClosureStats) : Bool :=
  b.root.kPathsSeen.all (fun p => a.root.kPathsSeen.any (fun q => q.1 == p.1))

/-- Whether `a` reaches at least as many *reliably-reached* shapes as `b` — paths seen more than once,
    gained against lost.

    Net, not absolute, and the absolute version was measured to be incoherent. `keepsRepeatedPaths` used
    to demand that no repeated path be dropped at all; swept over 72 single-tweak candidates on Cedar with
    input dispatch enabled, **the set it allowed and the set that gained any coverage were disjoint** — 26
    passed the gate and gained nothing, 5 gained (up to +81 paths) and every one of those dropped some
    repeated path. `andShort ×8000‰` took 336 → 417 paths and was refused for losing 23. A gate that
    forbids every move that does anything is not conservative, it is broken.

    Why the absolute form fails, and why it fails *worse* the more you measure: a reweighting always
    reshuffles which shapes a finite sample hits repeatedly, and the number of paths seen more than once
    grows with the sample size — so "lose none of them" tightens as `n` rises. (That also refutes an
    earlier plan of mine to fix the gate by raising `n`.) Input dispatch makes it harsher again, because
    cutting absorbed failures 775‰ → 371‰ leaves fewer retries and a tighter distribution: 166 of 336
    baseline paths were repeated under dispatch.

    Counting both directions keeps what the gate was for — a candidate cannot quietly trade away shapes it
    reaches dependably — while allowing trades that come out ahead. Singletons are ignored on both sides:
    measured at n = 120/300/1250, singleton losses held at 26/26/30 while everything else grew, which is
    what chance looks like. -/
def keepsRepeatedPaths (a b : ClosureStats) : Bool :=
  let repeatedOf := fun (s : ClosureStats) => s.root.kPathsSeen.filter (fun p => p.2 > 1)
  let ra := repeatedOf a
  let rb := repeatedOf b
  let lost := (rb.filter (fun p => !ra.any (fun q => q.1 == p.1))).length
  let gained := (ra.filter (fun p => !rb.any (fun q => q.1 == p.1))).length
  gained >= lost

/-- Whether `a` reaches strictly more than `b`: it covers everything `b` covers and something more, or it
    reaches more distinct k-paths. The acceptance test for `.coverage`, where speed must never decide on
    its own: the 5% margin in `fasterThan` sits inside wall-clock noise on Cedar-sized samples, and two
    runs of the same search accepted different "faster" plans. -/
def coverageGain (a b : ClosureStats) : Bool :=
  (coversAtLeast a b && !coversAtLeast b a) || a.root.kPathCount > b.root.kPathCount

/-- The wall-clock comparison, with its noise margin.

    A **margin**, not a strict inequality. `usPerSuccess` is wall-clock, and the honest noise floor is
    what decides whether a difference means anything: repeated timings of the *same* environment agree
    to ~0.2%, but across environments and system load the spread is a few percent. Without a margin the
    search laundered that into the book — it accepted two plans that measured 87/sec → 85/sec, i.e.
    slightly *worse*, with byte-identical coverage. 5% is comfortably above the observed spread and
    still well below any effect worth having. -/
def fasterThan (a b : ClosureStats) : Bool :=
  let faster := a.usPerSuccess * 100 < b.usPerSuccess * 95
  let sameSpeed := a.usPerSuccess * 100 >= b.usPerSuccess * 95
                   && b.usPerSuccess * 100 >= a.usPerSuccess * 95
  -- Only break a tie on output size when the speeds are indistinguishable, so a bigger output is never
  -- bought with a real slowdown.
  faster || (sameSpeed && a.root.avgOutputSizeCenti > b.root.avgOutputSizeCenti)

/-- `better` under a chosen objective.

    `.coverage` exists because **every cost measure rewards generating less.** Measured on Cedar's
    `unaryAppIsTrue`, pre-generating the discarded capability variable `oc7` cut time per sample
    3.0× (690µs → 228µs) and absorbed failures 2.5× (679‰ → 270‰) by stopping the rule from firing
    at all: `backtrack` answered from the base cases instead. Time, waste and acceptance all called
    that an improvement. k-path coverage called it what it was — 159 paths → 49, with **zero** paths
    gained, a strict subset — and named what was lost (`unaryApp > is > mk`, `hasAttr > record > cons`,
    `binaryApp > sub`).

    So reach dominates and cost only breaks ties. Containment first, because sets can be incomparable:
    a candidate that gains two paths and loses one is not obviously better, and only the containment
    test distinguishes that from a genuine gain. When neither contains the other the count decides,
    then speed. -/
def betterBy (k : ObjectiveKind) (a b : ClosureStats) : Bool :=
  match k with
  | .waste => a.better b
  | .throughput => fasterThan a b
  | .coverage =>
    let aCovers := coversAtLeast a b
    let bCovers := coversAtLeast b a
    if aCovers && !bCovers then true
    else if bCovers && !aCovers then false
    else if a.root.kPathCount != b.root.kPathCount then a.root.kPathCount > b.root.kPathCount
    else fasterThan a b


/-! ## Affording the measurement

    A fixed attempt count per constructor is the wrong shape once the closure is big, because the cost
    of one attempt is not remotely uniform. Measured on Cedar's `HasType[0,4]` closure (145 modes, 946
    mode×constructor pairs, size 4), `closureStats` is linear in `n` at `≈1.0s + 10.3s·n`, so the
    default `n = 100` takes **17 minutes** and a three-seed `closureStatsOver` takes about **52**. That
    is not a slow interpreter: 99% of the time sits in *five* modes and 58% in one
    (`HasType[0,3,4] as Generator`, ~79ms per attempt, because output index 3 is the `TypeEnv` and so
    that mode generates the whole type environment unconstrained), against ~0.05ms per attempt for the
    other 142 modes — a 1600× spread. Spending 100 attempts on both ends of that range is the defect.

    So the attempt count is *allocated* from measured cost. Two properties matter more than the saving:

    1. **The allocation is frozen, not recomputed.** A wall-clock *budget* — "profile each mode for
       200ms" — would let the attempt count wobble from run to run, and with it every rate derived from
       it, which would break the paired-seed comparison the search depends on (`defaultSeeds` exists so
       that every candidate faces identical sample paths). Instead cost is measured **once**, up front,
       and the resulting per-pair attempt counts are frozen into a `ProfileBudget` that baseline and
       every candidate share. Comparisons stay exactly reproducible; only the calibration is timed.
    2. **Every pair keeps a floor of attempts.** A pair that is never profiled reports no discards,
       which reads identically to a pair that discards nothing — and the expensive modes are precisely
       the ones worth watching. `minAttempts` is honoured even when it overruns `totalUs`. -/

/-- What one `(mode, constructor)` pair costs to profile, in microseconds per attempt. -/
structure PairCost where
  /-- The mode. -/
  key : SpecKey
  /-- The constructor of that mode. -/
  ctorName : Name
  /-- Measured microseconds for one attempt, floored at 1 so it can divide. -/
  usPerAttempt : Nat
  deriving Repr, Inhabited

/-- A frozen allocation of profiling attempts across a closure.

    Default-constructed it is **inert**: `attempts` is empty, so every pair falls back to the caller's
    `n` and `closureStats` behaves exactly as it did before. Build a real one with
    `InterpEnv.calibratedBudget`. -/
structure ProfileBudget where
  /-- Attempts per `(mode, constructor)`, frozen. Empty means "use the caller's `n` everywhere". -/
  attempts : List (SpecKey × Name × Nat) := []
  /-- The measurement the allocation came from. Kept because it is the cost model
      `ClosureStats.workUs` reports against, and because it is the interesting half of the report. -/
  costs : List PairCost := []
  /-- The `size` the costs were measured at. A cost table is only meaningful at the size it was taken
      at — per-attempt cost climbs steeply with size, since size is the generation depth budget — so
      `closureStats` refuses a calibrated budget from a different size rather than allocating from
      numbers that do not apply. `0` on an uncalibrated budget, which is never consulted. -/
  size : Nat := 0
  /-- The floor the allocation was built with, and what an *unmeasured* pair is given. -/
  minAttempts : Nat := 2
  /-- The cap the allocation was built with. -/
  maxAttempts : Nat := 100
  deriving Repr, Inhabited

namespace ProfileBudget

/-- Attempts allocated to a pair.

    An uncalibrated budget knows nothing and defers to the caller's `fallback`. A *calibrated* budget
    that has no row for a pair does **not** defer: it gives the pair `minAttempts`.

    That asymmetry is deliberate and is the same rule `enumWidthOf` follows for an unregistered mode.
    A pair missing from a calibrated table is a mode some candidate plan has newly invented — exactly
    the situation where cost is unknown — and `fallback` is the caller's `n`, the *largest* count in
    play. Deferring would hand the maximum attempt count to the one mode whose cost nobody has
    measured, and would also unbalance the comparison: the candidate would be measured with more
    attempts on its new modes than the baseline ever spent. Unknown cost must be assumed expensive. -/
def attemptsFor (b : ProfileBudget) (key : SpecKey) (ctorName : Name) (fallback : Nat) : Nat :=
  if b.attempts.isEmpty then fallback
  else match b.attempts.find? (fun (k, c, _) => k == key && c == ctorName) with
    | some (_, _, a) => a
    | none => b.minAttempts

/-- Measured cost of one attempt of a pair, or `none` if unmeasured. -/
def costFor (b : ProfileBudget) (key : SpecKey) (ctorName : Name) : Option Nat :=
  (b.costs.find? (fun c => c.key == key && c.ctorName == ctorName)).map PairCost.usPerAttempt

/-- Whether this budget carries an allocation at all. -/
def isCalibrated (b : ProfileBudget) : Bool := !b.attempts.isEmpty

/-- Microseconds this allocation is predicted to cost, from the frozen cost model. -/
def predictedUs (b : ProfileBudget) : Nat :=
  b.attempts.foldl (fun acc (k, c, a) => acc + a * (b.costFor k c).getD 1) 0

/-- Insertion sort ascending on cost, tie-broken on the rendered pair so the order — and hence the
    allocation — does not depend on `HashMap` iteration order. -/
private def sortByCost (costs : List PairCost) : List PairCost :=
  let lt := fun (x y : PairCost) =>
    if x.usPerAttempt != y.usPerAttempt then x.usPerAttempt < y.usPerAttempt
    else renderSpecKey x.key ++ toString x.ctorName < renderSpecKey y.key ++ toString y.ctorName
  let rec ins (x : PairCost) : List PairCost → List PairCost
    | [] => [x]
    | y :: ys => if lt x y then x :: y :: ys else y :: ins x ys
  costs.foldl (fun acc x => ins x acc) []

/-- Spreads `totalUs` over the measured pairs, cheapest first.

    Cheapest first is what makes one pass enough: a cheap pair takes its `maxAttempts` and hands the
    unspent remainder of its equal share back to the pairs behind it, so the expensive tail is funded
    from everything the cheap head did not need. Going the other way, the expensive pairs would drain
    the budget before the cheap ones — which cost almost nothing — got their full count. -/
def allocate (costs : List PairCost) (totalUs : Nat) (maxAttempts : Nat := 100)
    (minAttempts : Nat := 2) (size : Nat := 0) : ProfileBudget :=
  let sorted := sortByCost costs
  let rec go (remaining left : Nat) (cs : List PairCost)
      (acc : List (SpecKey × Name × Nat)) : List (SpecKey × Name × Nat) :=
    match cs with
    | [] => acc
    | c :: rest =>
      let share := if left == 0 then 0 else remaining / left
      let cost := Nat.max 1 c.usPerAttempt
      -- The floor wins over the budget: an unobserved pair looks exactly like a clean one.
      let a := Nat.max minAttempts (Nat.min maxAttempts (share / cost))
      go (remaining - Nat.min remaining (a * cost)) (left - 1) rest
        (acc ++ [(c.key, c.ctorName, a)])
  { attempts := go totalUs sorted.length sorted [], costs := costs, size := size
  , minAttempts := minAttempts, maxAttempts := maxAttempts }

/-- The allocation and the cost model behind it, costliest pairs first. -/
def render (b : ProfileBudget) (top : Nat := 8) : String :=
  if !b.isCalibrated then "[interp] profile budget: uncalibrated (every pair gets the caller's n)"
  else
    let sorted := (sortByCost b.costs).reverse
    let head :=
      s!"[interp] profile budget: {b.attempts.length} pairs at size {b.size} · predicted \
        {b.predictedUs / 1000}ms · total attempts \
        {b.attempts.foldl (fun acc (_, _, a) => acc + a) 0} · \
        unmeasured pairs get {b.minAttempts}"
    head ++ "\n" ++ "\n".intercalate ((sorted.take top).map (fun c =>
      let a := b.attemptsFor c.key c.ctorName 0
      s!"  {c.usPerAttempt}us/attempt × {a} = {c.usPerAttempt * a / 1000}ms  \
        {renderSpecKey c.key}/{c.ctorName}"))

end ProfileBudget

/-- Measures what each `(mode, constructor)` pair costs to profile, by profiling each one `probe`
    times and timing it.

    `probe` attempts, not one: a single attempt on a cheap pair is mostly the fixed cost of setting the
    profile up, and dividing that by one attributes it all to the attempt. Nanosecond resolution
    because the spread runs from tens of nanoseconds to hundreds of milliseconds and millisecond
    resolution rounds the cheap end to zero, which would then divide badly.

    This is the only timed measurement in the loop, and it runs once. -/
def InterpEnv.profileCosts (env : InterpEnv) (size : Nat) (inputs : List Val := [])
    (probe : Nat := 2) (seed : Option Nat := some 11) : IO (List PairCost) := do
  let probe := Nat.max 1 probe
  let mut out : List PairCost := []
  for (key, rel) in env.relations.toList do
    -- Generator modes only, matching `closureStats`: timing a checker mode through the generator
    -- interpreter measures how fast it raises `interpError`, and allocates attempts to a pair that
    -- cannot use them.
    if key.deriveSort != .Generator then continue
    let arity := rel.inputPositions.length
    let ins :=
      if inputs.length == arity then inputs
      else if inputs.length > arity then inputs.take arity
      else inputs ++ (List.replicate (arity - inputs.length) (inputs.headD (.lit (.natVal 0))))
    for (ctor, _) in rel.allSchedules do
      let t0 ← IO.monoNanosNow
      let _ ← env.profileCtor key ctor size ins probe seed
      let dt := (← IO.monoNanosNow) - t0
      out := out ++ [{ key := key, ctorName := ctor,
                       usPerAttempt := Nat.max 1 (dt / 1000 / probe) }]
  return out

/-- Calibrates and allocates in one step: the budget to hand every `closureStats` call in a run.

    `totalUs` is a target, not a guarantee — `minAttempts` overrides it, so a closure whose floor alone
    exceeds the target will exceed it. `ProfileBudget.predictedUs` says what the allocation actually
    comes to. -/
def InterpEnv.calibratedBudget (env : InterpEnv) (size : Nat) (inputs : List Val := [])
    (totalUs : Nat := 30000000) (maxAttempts : Nat := 100) (minAttempts : Nat := 2)
    (probe : Nat := 2) (seed : Option Nat := some 11) : IO ProfileBudget := do
  let costs ← env.profileCosts size inputs probe seed
  return ProfileBudget.allocate costs totalUs maxAttempts minAttempts size

/-! ### Why the cost model has to reach the objective

    `enumWalked` looks like it already measures this and does not. `enumCosts` is populated only for
    modes whose `deriveSort` is `.Enumerator`, and it is measured once per mode rather than once per
    attempt — on the Cedar run it read a constant 785 while wall-clock went from 13s to 208s. Every
    expensive mode there is a Generator, so generator cost is invisible to it.

    `ClosureStats.workUs`/`wastedUs` are recorded by `closureStats` from whatever budget shaped it, and
    `wastePerMille` turns them into the primary objective. See `wastePerMille` for the two reasons
    counting discards is not good enough — the 1600× cost spread, and the fact that a pooled rate
    inherits its weighting from the allocation. -/

/-- Measures every constructor of every registered mode, plus the root from the top.

    Each mode is profiled on the root's inputs where the arities agree, and on the root's inputs
    truncated or padded otherwise — a mode of a different arity cannot be handed the root's arguments.
    Modes whose inputs cannot be supplied are profiled with none, which is what an entry point with no
    inputs does anyway.

    `budget`, if calibrated, replaces `n` per pair; `n` still governs the root sample and any pair the
    budget does not mention. -/
def InterpEnv.closureStats (env : InterpEnv) (rootKey : SpecKey) (size : Nat)
    (inputs : List Val := []) (n : Nat := 100) (seed : Option Nat := none)
    (budget : ProfileBudget := {}) (profilePairs : Bool := true) : IO ClosureStats := do
  -- A cost table is only valid at the size it was measured at: `size` is the generation depth budget,
  -- so per-attempt cost climbs steeply with it, and allocating from numbers taken at another size
  -- silently produces an allocation that means nothing. Refuse rather than mislead.
  if budget.isCalibrated && budget.size != size then
    throw (IO.userError s!"[interp] profile budget was calibrated at size {budget.size} but this \
      measurement is at size {size}; per-attempt cost is size-dependent, so recalibrate with \
      `InterpEnv.calibratedBudget {size}`")
  -- Only a generator root can be *sampled*. Sampling a checker root would ask `interpRel` for values
  -- from a schedule that produces none, and every attempt would count as a discard — a fabricated
  -- 100% discard rate that says nothing about the closure.
  let t0 ← IO.monoNanosNow
  let root ←
    if rootKey.deriveSort == .Generator then env.sample rootKey size inputs n 1 seed
    else pure {}
  let rootUs := ((← IO.monoNanosNow) - t0) / 1000
  let mut per := []
  -- Accumulated here rather than derived later, so the cost model that produced a measurement travels
  -- with it. A `ClosureStats` is compared long after the budget that shaped it is out of scope.
  let mut workUs := 0
  let mut wastedUs := 0
  -- Skipping the pair profile is what makes the `throughput` objective cheap: it needs only the root
  -- sample. On Cedar that is 2.2s against 32s for all 587 generator pairs. Blame attribution still needs
  -- the profile, so a search takes it once per round rather than once per candidate.
  for (key, rel) in (if profilePairs then env.relations.toList else []) do
    -- **Generator modes only.** `profileCtor` runs the generator interpreter, and `interpRel` rightly
    -- refuses a checker or enumerator schedule — its steps mean different things. Profiling one anyway
    -- turns every attempt into an `interpError`, which then reads as a 100% discard rate for a mode that
    -- is in fact fine: on Cedar's `HasType` closure that was 78 of 993 pairs and 3082 fabricated errors,
    -- enough to move the closure-wide objective. The root sampling above declines for the same reason.
    -- An enumerator mode's cost is captured by `enumCosts` below instead; a checker mode's is not
    -- captured at all, which is a real gap but strictly better than inventing a number for it.
    if key.deriveSort != .Generator then continue
    -- A mode takes one input per value-level input position. The root's inputs fit the root; for
    -- another mode, reuse as many as fit and fall back to the first input for the rest, which keeps
    -- the profile in the same neighbourhood rather than at some arbitrary default.
    let arity := rel.inputPositions.length
    let ins :=
      if inputs.length == arity then inputs
      else if inputs.length > arity then inputs.take arity
      else inputs ++ (List.replicate (arity - inputs.length) (inputs.headD (.lit (.natVal 0))))
    for (ctor, _) in rel.allSchedules do
      let p ← env.profileCtor key ctor size ins (budget.attemptsFor key ctor n) seed
      let cost := (budget.costFor key ctor).getD 0
      -- Misconfigured attempts measured nothing; see `ClosureStats.attempts`.
      workUs := workUs + (p.attempts - min p.attempts p.interpErrors) * cost
      wastedUs := wastedUs + p.discards * cost
      per := per ++ [(key, ctor, p)]
  -- Enumeration cost, for the modes that have one. Measured once per mode rather than per
  -- constructor: `enumerate` concatenates the constructors' contributions, so the cost is a property
  -- of the mode.
  let mut costs := []
  for (key, rel) in (if profilePairs then env.relations.toList else []) do
    if key.deriveSort == .Enumerator then
      let arity := rel.inputPositions.length
      let ins :=
        if inputs.length == arity then inputs
        else if inputs.length > arity then inputs.take arity
        else inputs ++ (List.replicate (arity - inputs.length) (inputs.headD (.lit (.natVal 0))))
      costs := costs ++ [(key, env.enumCost key size ins)]
  return { perCtor := per, root := root, enumCosts := costs
         , workUs := workUs, wastedUs := wastedUs, rootUs := rootUs }

/-- Merges two measurements, as if the attempts had been one batch. -/
def ClosureStats.merge (a b : ClosureStats) : ClosureStats where
  perCtor := (a.perCtor.zip b.perCtor).map (fun (x, y) =>
    (x.1, x.2.1, { x.2.2 with
      attempts := x.2.2.attempts + y.2.2.attempts
      successes := x.2.2.successes + y.2.2.successes
      outOfFuel := x.2.2.outOfFuel + y.2.2.outOfFuel
      interpErrors := x.2.2.interpErrors + y.2.2.interpErrors
      unattributed := x.2.2.unattributed + y.2.2.unattributed
      perStep := (x.2.2.perStep.zip y.2.2.perStep).map (fun (p, q) =>
        { p with discards := p.discards + q.discards }) }))
  root := a.root.merge b.root
  enumCosts := a.enumCosts
  -- Both scale with attempts, which merge sums, so summing keeps `wastePerMille` a valid pooled rate
  -- across seeds.
  workUs := a.workUs + b.workUs
  wastedUs := a.wastedUs + b.wastedUs
  rootUs := a.rootUs + b.rootUs

/-- Measures a closure over several seeds and merges the results.

    A single fixed seed measures one sample path, which a candidate can win by suiting. Several fixed
    seeds keep the comparison paired — every candidate faces the same paths — while making it much
    harder to win by luck. -/
def InterpEnv.closureStatsOver (env : InterpEnv) (rootKey : SpecKey) (size : Nat)
    (inputs : List Val := []) (n : Nat := 100) (seeds : List Nat := [])
    (budget : ProfileBudget := {}) (profilePairs : Bool := true) : IO ClosureStats := do
  match seeds with
  | [] => env.closureStats rootKey size inputs n none budget profilePairs
  | s :: rest =>
    let mut acc ← env.closureStats rootKey size inputs n (some s) budget profilePairs
    for s' in rest do
      acc := acc.merge (← env.closureStats rootKey size inputs n (some s') budget profilePairs)
    return acc

/-- An `EnumWidthModel` with its leaf widths measured from this environment rather than assumed.

    The estimate is only as good as its leaf numbers, and a wrong leaf number propagates
    multiplicatively through every product. Measuring beats guessing, and measuring leaves is cheap. -/
def InterpEnv.calibratedWidthModel (env : InterpEnv) (size : Nat)
    (base : EnumWidthModel := {}) : EnumWidthModel :=
  { base with leaves := env.calibrateLeafWidths size ++ base.leaves }

/-! ## Blame that crosses call frames -/

/-- A place a mutation could act: a premise of a constructor of a mode, and how many discards are
    attributed to it once inherited blame has been pushed down. -/
structure BlameTarget where
  /-- The mode the culprit lives in. -/
  key : SpecKey
  /-- The constructor. -/
  ctorName : Name
  /-- The premise a mutation can move, if the rejecting step came from one. `none` for a prologue
      `Match`, which no ordering can move. -/
  premiseIdx : Option Nat
  /-- Discards attributed here after redirection. -/
  discards : Nat
  /-- How many `SuchThat` edges were followed to get here. `0` means the blame was local. -/
  depth : Nat
  deriving Repr, Inhabited

/-- The step of `sched` at `idx`, if there is one. -/
private def stepAt? (sched : Schedule) (idx : Nat) : Option ScheduleStep := sched.1[idx]?

/-- Redirects one constructor's per-step discards to where they really originate.

    A `Check` or `Match` rejects on its own account, so its discards stay. A `SuchThat`'s discards came
    from inside the mode it calls, so they are pushed into that mode's *worst* constructor and the walk
    continues. `fuel` bounds the descent, which matters because the mode graph has cycles. -/
private partial def redirect (env : InterpEnv) (stats : ClosureStats) (specs : List RelSpec)
    (book : PlanBook) (key : SpecKey) (ctorName : Name) (idx : Nat) (count : Nat) (depth : Nat)
    (fuel : Nat) : List BlameTarget :=
  let localTarget := fun (_ : Unit) =>
    -- Which premise emitted this step, so a mutation has something to move. Read from the provenance
    -- recorded when the installed schedule was lowered. Re-lowering `book.planFor` instead got a
    -- *different* plan whenever lowering had repaired a booked order, picked the first resolvable plan,
    -- or worked from an instantiated spec — and then named the wrong premise, or none. Re-lowering is
    -- kept only for a schedule that never had a plan (hand-registered, or loaded from compiled code).
    let fromProvenance := fun (p : CtorProvenance) =>
      match (p.origins[idx]?).bind id with
      | some (.use i) => some i
      | _ => none
    let reLowered := fun (_ : Unit) =>
      match specs.find? (fun r => r.inductiveName == key.inductiveName), ctorSpecOf? specs key ctorName with
      | some rel, some c =>
        match rescheduleLowered rel key c (book.planFor rel key c) with
        | .error _ => none
        | .ok low =>
          match low.originOf idx with
          | some (.use i) => some i
          | _ => none
      | _, _ => none
    let premise :=
      match env.relations[key]? with
      | some rs =>
        match rs.provenanceOf? ctorName with
        | some p => fromProvenance p
        | none => if rs.provenance.isEmpty then reLowered () else none
      | none => reLowered ()
    [{ key := key, ctorName := ctorName, premiseIdx := premise, discards := count,
       depth := depth : BlameTarget }]
  match fuel with
  | 0 => localTarget ()
  | fuel' + 1 =>
    match env.relations[key]? with
    | none => localTarget ()
    | some rel =>
      match (rel.ctorSchedule? ctorName).bind (fun s => stepAt? s idx) with
      | none => localTarget ()
      | some step =>
        match step with
        | .Check .. | .Match .. | .Unconstrained .. => localTarget ()
        | .SuchThat .. =>
          match stepDepKey? step with
          | none => localTarget ()   -- a `Rec`/`MutRec` self-call: the blame belongs here
          | some callee =>
            -- Push the blame into the callee's worst constructor, if it is one we measured.
            let calleeProfiles := stats.perCtor.filter (fun (k, _, _) => k == callee)
            let worst := calleeProfiles.foldl (fun acc t =>
              match acc with
              | none => some t
              | some u => if t.2.2.discards > u.2.2.discards then some t else acc) none
            match worst with
            | none => localTarget ()
            | some (_, calleeCtor, prof) =>
              if prof.discards == 0 then localTarget ()
              else
                -- Split the inherited count across the callee's own rejecting steps, in proportion.
                let rejecting := prof.perStep.filter (fun s => s.discards > 0)
                if rejecting.isEmpty then localTarget ()
                else
                  rejecting.flatMap (fun s =>
                    redirect env stats specs book callee calleeCtor s.stepIdx
                      (count * s.discards / Nat.max 1 prof.discards) (depth + 1) fuel')

/-- Where the closure's discards really come from, heaviest first.

    Inherited blame is pushed down through `SuchThat` edges, so a `BstNode` that only looks bad because
    `Between[1]` is bad reports `Between[1]` instead. -/
def ClosureStats.rootCauses (stats : ClosureStats) (env : InterpEnv) (specs : List RelSpec)
    (book : PlanBook) (fuel : Nat := 8) : List BlameTarget :=
  let raw := stats.perCtor.flatMap (fun (key, ctor, prof) =>
    (prof.perStep.filter (fun s => s.discards > 0)).flatMap (fun s =>
      redirect env stats specs book key ctor s.stepIdx s.discards 0 fuel))
  -- Merge targets that landed on the same premise, then rank by weight.
  let merged := raw.foldl (fun acc t =>
    match acc.find? (fun u => u.key == t.key && u.ctorName == t.ctorName
        && u.premiseIdx == t.premiseIdx) with
    | some u => acc.map (fun v =>
        if v.key == t.key && v.ctorName == t.ctorName && v.premiseIdx == t.premiseIdx then
          { v with discards := u.discards + t.discards } else v)
    | none => acc ++ [t]) []
  merged.foldl (fun acc t =>
    let rec ins : List BlameTarget → List BlameTarget
      | [] => [t]
      | u :: us => if t.discards > u.discards then t :: u :: us else u :: ins us
    ins acc) []

/-- Renders the blame, heaviest first. -/
def renderBlame (specs : List RelSpec) (targets : List BlameTarget) : String :=
  let one := fun (t : BlameTarget) =>
    let premise := renderPremise specs t.key t.ctorName t.premiseIdx
    let via := if t.depth == 0 then "" else s!" (inherited, {t.depth} frame(s) down)"
    s!"  {t.discards}×  {renderSpecKey t.key} / {t.ctorName}: {premise}{via}"
  if targets.isEmpty then "[interp] no discards to attribute"
  else s!"[interp] discards by origin:\n" ++ "\n".intercalate (targets.map one)

/-! ## Phase two: tuning the weights

    A plan search cannot make trees bigger. Every plan in the previous section produces the same
    *shape* of value; how often the recursive constructor is chosen over the base one is decided by the
    weight function, which is not part of a plan at all. So the two are tuned in sequence, and in this
    order — the plan determines which constructors exist and what they call, so re-weighting midway
    through the plan search would confound the two effects.

    The knob is deliberately an **affine adjustment to the existing weighting**, not a replacement for
    it. `Scoring.CtorWeightModifier` is exactly that shape — it receives the computed base weight as
    its first argument and returns an adjusted one, and `DeriveConstrainedProducer` emits
    `modifier (weightFn …) …` when one is registered. Tuning a multiplier and an offset over
    `balancedCtorWeight` therefore lands on something the compile-time pipeline can express verbatim,
    which a hand-rolled replacement weight function would not.

    One invariant is not negotiable. `balancedCtorWeight` returns `0` for a recursive constructor at
    `size = 0`, and that zero is what stops recursion at the bottom of the budget. A tweak that turned
    it into anything else would break termination, so `WeightTweak.apply` preserves zero. -/

/-- An affine adjustment to a constructor's computed weight: `base * mulPerMille / 1000 + addend`.

    Integer arithmetic throughout, so a tuned generator is reproducible and the result is a plain
    `Nat` the emitted code can compute. -/
structure WeightTweak where
  /-- Multiplier in per mille. `1000` is unchanged. -/
  mulPerMille : Nat := 1000
  /-- Additive offset, applied after the multiplier. -/
  addend : Nat := 0
  deriving Repr, Inhabited, BEq

namespace WeightTweak

/-- Whether this tweak changes anything. -/
def isIdentity (t : WeightTweak) : Bool := t.mulPerMille == 1000 && t.addend == 0

/-- Applies the tweak, preserving zero.

    A zero weight means "this constructor is unavailable at this size", which for a recursive
    constructor at `size = 0` is what guarantees termination. Scaling it up would reintroduce
    unbounded recursion, so zero is a fixed point. -/
def apply (t : WeightTweak) (base : Nat) : Nat :=
  -- `Nat.min base 1 * …` rather than `if base == 0 then 0 else …`: the two agree pointwise
  -- (`min 0 1 = 0` absorbs the product, and `min base 1 = 1` for `base ≥ 1`) but this form is a single
  -- arithmetic expression instead of a branch.
  --
  -- The zero must be absorbed **multiplicatively**. `Nat.max (Nat.min base 1) (base * mul / 1000 + addend)`
  -- looks equivalent and is not: at `base = 0` it returns `addend`, not 0. Cedar's tuned book carries an
  -- `addend := 8` arm, so that form gave a recursive constructor weight 8 at `size = 0` — exactly the
  -- fixed point that stops recursion — and the run survived only on `Gen`'s fuel.
  --
  -- That matters for the *emitted* counterpart. `precomputeWeight` folds a weight expression under the
  -- runtime `size` binder, and a recursive constructor's base weight is itself size-dependent
  -- (`if size' = 0 then 0 else max 1 size' * 4`). Wrapping that in another `if` produced a nested
  -- conditional that `simp` could not collapse — it could not prove `base == 0 ↔ size' = 0` — so the
  -- emitted code evaluated two branches plus a `max` and a multiply on every branch construction:
  --
  --   if ¬size' = 0 → max 1 size' * 2 = 0 then 0
  --   else Nat.max 1 ((if size' = 0 then 0 else max 1 size' * 2) * 16000 / 1000)
  --
  -- The branch-free form leaves a residual comparable to the untweaked weight instead of double it.
  -- Note what is *not* claimed: a size-dependent weight can never fold to a literal, so "a tuned book
  -- costs nothing at runtime" is only true of the base constructors, whose weight has `size = 0`
  -- substituted. The goal here is parity with the untuned weight, not elimination.
  Nat.min base 1 * Nat.max 1 (base * t.mulPerMille / 1000 + t.addend)

/-- Rendering for reports. -/
def render (t : WeightTweak) : String :=
  if t.isIdentity then "×1" else s!"×{t.mulPerMille}‰+{t.addend}"

end WeightTweak

/-- Tweaks per constructor, keyed the way `CtorWeightFn` sees a constructor: its name together with the
    mode's output indices and derive sort, which is enough to tell two modes of one relation apart. -/
structure WeightBook where
  /-- `((ctorName, outputIndices, deriveSort), tweak)`. -/
  entries : List ((Name × List Nat × DeriveSort) × WeightTweak) := []
  deriving Repr, Inhabited

namespace WeightBook

/-- The tweak for a constructor, identity if none is recorded. -/
def find (b : WeightBook) (ctorName : Name) (outputIndices : List Nat) (deriveSort : DeriveSort) :
    WeightTweak :=
  match b.entries.find? (fun e => e.1.1 == ctorName && e.1.2.1 == outputIndices
      && e.1.2.2 == deriveSort) with
  | some e => e.2
  | none => {}

/-- Records a tweak, replacing any previous one for the same constructor. -/
def set (b : WeightBook) (ctorName : Name) (outputIndices : List Nat) (deriveSort : DeriveSort)
    (t : WeightTweak) : WeightBook :=
  { entries := ((ctorName, outputIndices, deriveSort), t) ::
      b.entries.filter (fun e =>
        !(e.1.1 == ctorName && e.1.2.1 == outputIndices && e.1.2.2 == deriveSort)) }

/-- Only the entries that change something. -/
def effective (b : WeightBook) : List ((Name × List Nat × DeriveSort) × WeightTweak) :=
  b.entries.filter (fun e => !e.2.isIdentity)

end WeightBook

/-- The weight function `base` with a `WeightBook` layered over it — the runtime counterpart of
    registering a `Scoring.CtorWeightModifier`. -/
def tweakedWeightFn (base : CtorWeightFn) (b : WeightBook) : CtorWeightFn :=
  fun ctorName outputIndices deriveSort badness isRec size numBase numRec numRecCalls =>
    (b.find ctorName outputIndices deriveSort).apply
      (base ctorName outputIndices deriveSort badness isRec size numBase numRec numRecCalls)

/-- Emits the book as a `Scoring.CtorWeightModifier`, the hook the compile-time pipeline already has.

    `CtorWeightModifier` receives `(base, ctorName, outputIndices, deriveSort, badness, isRec, size,
    numBase, numRec, numRecCalls)`, so it is keyed on exactly what a `WeightBook` is keyed on. That
    matters: tuning routinely picks the *same constructor at two different modes with different tweaks*,
    and a ctor-name-only hook would collapse those.

    The emitted arms replicate `WeightTweak.apply`, both guards included. `base == 0` is a fixed point
    because a zero weight is what stops a recursive constructor being chosen at size 0 — i.e. what makes
    generation terminate. `Nat.max 1` is what stops a small weight flooring to zero under integer
    division and silently deleting a branch: `×250‰` on a weight of 1 would otherwise become 0.

    `precomputeWeight` unfolds the modifier and folds closed `Name`/`Nat` matches with `decide := true`,
    so this costs nothing at runtime — it collapses to literals at elaboration.

    Register the result with `Scoring.registerWeightModifier` and select it with
    `set_option specimen.weightModifier`. -/
def WeightBook.toModifierSource (b : WeightBook) (defName : String := "tunedWeightModifier") :
    String :=
  let srtLit := fun (srt : DeriveSort) => match srt with
    | .Generator => "Schedules.DeriveSort.Generator"
    | .Enumerator => "Schedules.DeriveSort.Enumerator"
    | .Checker => "Schedules.DeriveSort.Checker"
    | .Theorem => "Schedules.DeriveSort.Theorem"
  let arm := fun ((ctor, outs, srt), tw) =>
    let outsLit := "[" ++ ", ".intercalate (outs.map toString) ++ "]"
    -- Mirrors `WeightTweak.apply`'s branch-free form; see its docstring for why.
    let body :=
      if tw.addend == 0 then
        "Nat.min base 1 * Nat.max 1 (base * " ++ toString tw.mulPerMille ++ " / 1000)"
      else
        "Nat.min base 1 * Nat.max 1 (base * " ++ toString tw.mulPerMille ++ " / 1000 + "
          ++ toString tw.addend ++ ")"
    "  | ``" ++ toString ctor ++ ", " ++ outsLit ++ ", " ++ srtLit srt ++ " => " ++ body
  let arms := b.effective.map arm
  if arms.isEmpty then
    "-- " ++ defName ++ ": the tuned book is empty; no modifier needed.\n"
      ++ "def " ++ defName ++ " : Scoring.CtorWeightModifier := Scoring.idWeightModifier"
  else
    "\n".intercalate
      ([ "/-- Generated from a tuned `WeightBook` by `WeightBook.toModifierSource`. -/"
       , "def " ++ defName ++ " (base : Nat) (ctor : Lean.Name) (outs : List Nat)"
       , "    (srt : Schedules.DeriveSort) (_badness : Nat) (_isRec : Bool) (_size : Nat)"
       , "    (_numBase _numRec _numRecCalls : Nat) : Nat :="
       , "  -- `Nat.min base 1 *` keeps zero a fixed point — that is what makes recursion terminate at"
       , "  -- size 0 — without a branch `precomputeWeight` cannot fold through. It must multiply: taking"
       , "  -- `Nat.max (Nat.min base 1) (…)` instead returns the addend at base 0."
       , "  match ctor, outs, srt with" ]
       ++ arms
       ++ [ "  | _, _, _ => base"
          , ""
          , "initialize Scoring.registerWeightModifier `" ++ defName ++ " " ++ defName
              ++ " ``" ++ defName ])

/-- The environment with a weight book applied. -/
def InterpEnv.withWeightBook (env : InterpEnv) (b : WeightBook) : InterpEnv :=
  { env with weightFn := tweakedWeightFn env.weightFn b }

/-! ### What to aim the weights at

    Phase one has a target it can reach and recognise — zero avoidable discards. Phase two does not:
    there is no canonical output size *or* output distribution, only the one you want. So the objective
    is stated explicitly, as one or both of a mean-size target and a per-constructor coverage target,
    and the search is constrained never to trade discards for either.

    The coverage target follows Cedar's own hand-tuning pattern: name the constructors whose
    representation matters and say what proportion each should occupy. Constructors not named are
    unconstrained. Both floors (this ctor is under-represented, boost it) and ceilings (this one is
    flooding, suppress it) are supported, because Cedar's `favorHasTag` does both. -/

/-- A soft bound on how often a named constructor should appear among total occurrences. -/
structure CoverageBand where
  /-- The constructor whose share is bounded. -/
  ctorName : Name
  /-- Lower bound on its share, in per mille (0 disables). -/
  minPerMille : Nat := 0
  /-- Upper bound on its share, in per mille (1000 disables). -/
  maxPerMille : Nat := 1000
  deriving Repr, Inhabited

/-- What a coverage-aware objective looks like: a list of bands. Names outside the list are ignored,
    so the target is *sparse* — you only pin what you care about. -/
structure CoverageGoal where
  /-- The per-constructor bands. -/
  bands : List CoverageBand := []
  /-- Floor on distinct k-paths reached (`RunStats.kPathCount`). `0` disables it.

      This is the coverage measure that works, and the bands are its k=1 shadow. Measured on Cedar by
      sweeping `callExt`'s weight: the band view scores `×16000‰` best because it maximises `call`
      *occurrences* (34, and 76 distinct constructors), while k-paths say `×250‰` is better — 318
      paths against 283 — because piling size budget into extension calls stops the generator building
      other shapes. A share-of-occurrences target cannot see that; a path count can.

      Set it above anything reachable to make the objective "maximise paths": the gap then falls
      monotonically with every path gained, and the trace reports how close it got. -/
  minPaths : Nat := 0
  /-- Tolerance in per mille, matching `SizeGoal.toleranceCenti`'s role: a candidate must clear it to
      be believed. A small but non-zero default because sample-mean noise on per-mille shares is not
      zero even under paired seeds. -/
  tolerancePerMille : Nat := 5
  deriving Repr, Inhabited

/-- Per-mille share of one constructor across every measured success. `n / N` when the count is `n`
    and the total is `N`, in per mille. `0` when nothing was measured. -/
def RunStats.sharePerMille (s : RunStats) (ctorName : Name) : Nat :=
  let total := s.totalCtorOccurrences
  if total == 0 then 0 else
    let n := ((s.ctorCounts.find? (fun p => p.1 == ctorName)).getD (default, 0)).2
    n * 1000 / total

/-- How badly a measured share misses its band, in per mille — `0` when the share is inside. -/
def CoverageBand.miss (b : CoverageBand) (share : Nat) : Nat :=
  if share < b.minPerMille then b.minPerMille - share
  else if share > b.maxPerMille then share - b.maxPerMille
  else 0

/-- Total miss across a goal's bands, and the worst individual miss for reporting.

    Summed rather than maxed: three constructors each 10‰ off should outrank one that is 10‰ off, so
    a candidate that helps most bands wins over one that helps only the worst. -/
def CoverageGoal.miss (g : CoverageGoal) (s : RunStats) : Nat × Option (Name × Nat) :=
  -- The path floor is added to the band misses rather than replacing them, so a caller can ask for
  -- both. With `bands := []` it is the whole objective.
  let pathMiss := if s.kPathCount < g.minPaths then g.minPaths - s.kPathCount else 0
  let seed : Nat × Option (Name × Nat) :=
    (pathMiss, if pathMiss == 0 then none else some (`«k-paths», pathMiss))
  g.bands.foldl (fun (tot, worst) b =>
    let m := b.miss (s.sharePerMille b.ctorName)
    let worst' := match worst with
      | none => if m == 0 then none else some (b.ctorName, m)
      | some (_, w) => if m > w then some (b.ctorName, m) else worst
    (tot + m, worst')) seed

/-! ### What to aim the weights at (size) -/

/-- What phase two is trying to achieve, on the size axis. A coverage goal is separate
    (`CoverageGoal`); `tuneWeights` takes both. -/
structure SizeGoal where
  /-- The mean `Val.size` wanted, in hundredths — the same units as
      `RunStats.avgOutputSizeCenti`. -/
  targetCenti : Nat
  /-- How much the closure-wide discard rate (per mille) may rise in exchange. `0` forbids any
      regression, which is the honest default: a bigger value that costs more work to find is not
      obviously better. -/
  discardSlackPerMille : Nat := 0
  /-- How much closer to the target a candidate must get before it is believed, in the same hundredths.

      This is a *noise floor*, not a preference. `avgOutputSizeCenti` is a sample mean over `n` draws,
      so two identical schedules differ by a few hundredths run to run; without a threshold the search
      cheerfully "improves" by chasing that, and reports a tweak on a constructor whose weight has no
      bearing on output size at all.

      `runSeeded` pairs the comparison, so two *identical* schedules agree exactly and this can be
      small. Not zero, though: a different plan consumes the random stream in a different order, so the
      same seed does not mean the same draws are used for the same purposes. It covers that residual,
      not the spread of an unpaired sample mean. -/
  toleranceCenti : Nat := 5
  deriving Repr, Inhabited

/-- How far a measurement is from the goal, in the same hundredths as `avgOutputSizeCenti`.

    `none` means *inadmissible*: the candidate is misconfigured. Discard regression is now handled
    separately in `tuneWeights`, since a pure coverage tune sometimes needs to accept a small discard
    rise to reach an under-represented shape. -/
def SizeGoal.gapCenti (g : SizeGoal) (_baseline : ClosureStats) (s : ClosureStats) : Option Nat :=
  if s.interpErrors != 0 then none
  else
    let got := s.root.avgOutputSizeCenti
    some (if got ≥ g.targetCenti then got - g.targetCenti else g.targetCenti - got)

/-- The candidate adjustments tried for each constructor, as a coordinate-descent ladder.

    Mostly multiplicative, because weight only matters as a *ratio* against the other constructors:
    doubling a recursive constructor's weight is the meaningful move, adding 1 to it is not. The range
    has to be wide to be useful. Under `balancedCtorWeight` a recursive constructor weighs
    `size' * quality` against a base constructor's flat `4 * quality`, so the recursion probability is
    `size' / (size' + 4)` — 43% at `size' = 3`. Multiplying by `k` makes it `k·size' / (k·size' + 4)`,
    so reaching 90% at that size takes `k ≈ 12`, well past a doubling.

    The two entries with an `addend` exist because at small `size'` no multiplier helps much: `size' = 1`
    gives a recursive weight of `quality`, and scaling a small number is still a small number, whereas
    an offset lifts it clear of the base constructor's constant. -/
def weightLadder : List WeightTweak :=
  [ { mulPerMille := 16000 }, { mulPerMille := 8000 }, { mulPerMille := 4000 }
  , { mulPerMille := 2000, addend := 8 }, { mulPerMille := 2000 }
  , { mulPerMille := 1000, addend := 8 }, { mulPerMille := 1000 }
  , { mulPerMille := 500 }, { mulPerMille := 250 } ]

/-- The seeds a comparison is paired over by default. Three is enough that a candidate cannot win on
    one lucky path, and few enough that a pass stays affordable. Arbitrary constants; any fixed set
    does, so long as every candidate sees the same one. -/
def defaultSeeds : List Nat := [11, 2029, 90210]

/-- One step of the weight search, kept for the report. -/
structure WeightStep where
  /-- Round number; `0` is the untweaked baseline. -/
  round : Nat
  /-- The constructor adjusted, if any. -/
  ctorName : Option Name := none
  /-- The tweak tried. -/
  tweak : WeightTweak := {}
  /-- Whether it became the new incumbent. -/
  accepted : Bool := false
  /-- What it measured, when it could be measured. -/
  stats : Option ClosureStats := none
  /-- Distance from the size target, when the candidate was admissible. See `SizeGoal.gapCenti`. -/
  gapCenti : Option Nat := none
  /-- What happened, in words. -/
  note : String := ""

/-- Renders a weight-tuning trace. -/
def renderWeights (trace : List WeightStep) : String :=
  let one := fun (t : WeightStep) =>
    let mark := if t.accepted then "✔" else " "
    let who := match t.ctorName with
      | some c => s!"{c} {t.tweak.render}"
      | none => "baseline"
    let score := match t.stats with
      | some s =>
        let m := match t.gapCenti with
          | some m => s!"off by {renderCenti m}"
          | none => "rejected (discards regressed)"
        s!"avg size {renderCenti s.root.avgOutputSizeCenti} · \
          discards {s.discardPerMille / 10}.{s.discardPerMille % 10}% · {m}"
      | none => t.note
    s!"{mark} r{t.round}  {who}  {score}"
  "[interp] weight tuning:\n" ++ "\n".intercalate (trace.map one)

/-- Tunes the weights of a *fixed* closure towards a size goal, by coordinate descent over an affine
    adjustment per recursive constructor.

    Only recursive constructors are adjusted: a base constructor's weight is what a recursive one is
    measured against, so scaling both is a no-op, and scaling the base alone is the same move with the
    sign flipped. The closure is rebuilt for each candidate but the *plans* never change, so nothing
    here can reintroduce a discard that phase one removed — and the goal refuses any candidate whose
    discard rate rises beyond its slack regardless. -/
def InterpEnv.tuneWeights (env : InterpEnv) (specs : List RelSpec) (rootKey : SpecKey)
    (book : PlanBook) (goal : SizeGoal) (size : Nat) (inputs : List Val := []) (n : Nat := 100)
    (passes : Nat := 2) (limit : Nat := 24) (seeds : List Nat := defaultSeeds)
    (coverage : CoverageGoal := {}) (budget : ProfileBudget := {}) (fuel : Nat := 400)
    (deriveCheckers : Bool := true) :
    IO (WeightBook × List WeightStep) := do
  -- `fuel := 400`, not 64. 64 was inherited from `deriveClosure`'s default and **cannot build Cedar's
  -- closure at all** — "mode closure did not settle within 64 derivations" — so the first measurement
  -- failed and the whole search returned "cannot build" without trying a single candidate.
  --
  -- `budget` is now unused. Kept in the signature so callers that pass one still compile; the
  -- objective no longer profiles per constructor, so there is nothing to allocate attempts to.
  let _ := budget
  -- **The closure is derived once, not per candidate.** A `WeightBook` changes no schedule — it only
  -- rescales branch weights via `withWeightBook` — so every candidate in the search would derive a
  -- byte-identical closure. Measured at 702ms against 3474 candidates per pass, that was 41 minutes of
  -- pure repetition.
  let builtOnce ←
    match env.deriveClosureWith specs [rootKey] book limit fuel deriveCheckers with
    | .error e => pure (.error e : Except String InterpEnv)
    | .ok raw => pure (.ok raw.publishInterpretedCheckers)
  -- Measures one weight book. Returns the stats plus the **absorbed-failure rate**, which replaces
  -- `ClosureStats.discardPerMille` as the regression guard.
  --
  -- Why: `closureStatsOver` profiles every constructor of every mode (155 modes, ~950 pairs on Cedar)
  -- to build per-step discard histograms, and `tuneWeights` reads exactly three numbers out of the
  -- result — output size and coverage, both from the *root* sample, and `discardPerMille`, one scalar.
  -- Measured, that profile costs **28.1s** against **42ms** for the root sample alone, a 670x tax to
  -- compute a single guard value. `withRetryLog` recovers the same signal from the root run for free
  -- (750‰ absorbed against the profile's 796‰ discard), because it counts the branch failures
  -- `backtrack` absorbs as they happen.
  --
  -- Consequence: the retry counter is load-bearing during tuning, not diagnostic. `withRetryLog`
  -- enables it around each measurement and restores it afterwards.
  let measure := fun (wb : WeightBook) => do
    match builtOnce with
    | .error e => return (.error e : Except String (ClosureStats × Nat))
    | .ok raw =>
      let built := raw.withWeightBook wb
      match built.validate with
      | .error report => return .error report
      | .ok () =>
        let (root, log) ← withRetryLog do
          let mut acc : RunStats := {}
          for seed in seeds do
            acc := acc.merge (← built.sample rootKey size inputs n 0 (some seed))
          return acc
        -- A weight book under which sampling reaches interpreter misconfiguration is not a candidate
        -- worth ranking: the absorbed rate and paths it reports were measured on a broken closure.
        -- Refused with the first place it went wrong, which is what someone fixing it needs.
        if root.interpErrors > 0 then
          let where_ := match log.firstInternal with
            | some (k, c, m) => s!"first in {c} @ {renderSpecKey k}: {m}"
            | none => root.firstInterpError.getD "no message recorded"
          return .error s!"{root.interpErrors} sample(s) hit interpreter misconfiguration, {where_}"
        return .ok ({ root := root }, log.failPerMille)
  -- The recursive constructors of every **generator** mode. Two filters, both load-bearing.
  --
  -- Recursive only: a base constructor's weight is what a recursive one is measured against, so
  -- scaling both is a no-op and scaling the base alone is the same move with the sign flipped.
  --
  -- Generators only: `EnumeratorCombinators.enumerate` concatenates its alternatives and
  -- `DecOpt.checkerBacktrack` tries all of them, so neither consults a weight function — a tweak on a
  -- checker or enumerator mode is simply inert. Cedar's own hand-tuned modifier says this in as many
  -- words: "boosting `Lub.record` is inert ... because `Lub` is scheduled as a CHECK (not a generator)
  -- in the derive". Without this filter a pass spends most of its samples proving that.
  let targets : List (Name × List Nat × DeriveSort) ←
    match env.deriveClosureWith specs [rootKey] book limit fuel deriveCheckers with
    | .error _ => pure []
    | .ok built => pure (built.relations.toList.flatMap (fun (p : SpecKey × RelSchedule) =>
        if p.1.deriveSort != .Generator then [] else
          p.2.bucketedSchedules.2.map (fun (ctor, _) =>
            (ctor, p.1.outputIndices, p.1.deriveSort))))
  let mut wb : WeightBook := {}
  let mut trace : List WeightStep := []
  let mut baseline : Option ClosureStats := none
  let mut baseAbsorbed : Nat := 0
  match ← measure wb with
  | .error e => return (wb, [{ round := 0, note := s!"cannot build: {e}" }])
  | .ok (s, absorbed) =>
    baseline := some s
    baseAbsorbed := absorbed
    let step : WeightStep :=
      { round := 0, accepted := true, stats := some s, gapCenti := goal.gapCenti s s,
        note := "baseline" }
    trace := [step]
  let some base := baseline | return (wb, trace)
  -- Two axes, two tolerances, kept separate. Combining them into a scalar is tempting and the wrong
  -- move: size miss is centi, coverage miss is per-mille summed over bands, they need not scale
  -- comparably, and pretending they do makes the noise floor either paranoid on one axis or generous
  -- on the other. Instead a candidate is admissible if *neither* axis regresses beyond its tolerance,
  -- and preferred if the strict improvement is on the axis the caller cares about — coverage when a
  -- coverage goal was supplied, size otherwise.
  let sizeInPlay := goal.toleranceCenti < 1000000
  let combined := fun (g : Option Nat) (cov : Nat) => g.map (fun sz =>
    if sizeInPlay then sz + cov else cov)
  let (baseCov, _) := coverage.miss base.root
  let mut bestGap := (combined (goal.gapCenti base base) baseCov).getD 1000000
  -- Tolerance is the axis-in-play's tolerance, not the max: mixing centi and per-mille under `max`
  -- would make one axis paranoid whenever the other's tolerance was large.
  let tolerance := if sizeInPlay then goal.toleranceCenti else coverage.tolerancePerMille
  for pass in List.range passes do
    let mut improved := false
    for t in targets do
      let (ctorName, outputIndices, deriveSort) := t
      for cand in weightLadder do
        if cand == wb.find ctorName outputIndices deriveSort then continue
        let wb' := wb.set ctorName outputIndices deriveSort cand
        match ← measure wb' with
        | .error e =>
          let step : WeightStep :=
            { round := pass + 1, ctorName := some ctorName, tweak := cand,
              note := s!"unbuildable: {e}" }
          trace := trace ++ [step]
        | .ok (s', absorbed') =>
          -- Guard on absorbed failures rather than the per-constructor discard rate: same signal,
          -- measured during the root sample instead of by profiling 950 mode-constructor pairs.
          let discardOK := absorbed' ≤ baseAbsorbed + goal.discardSlackPerMille
          -- A reweighting may drop a shape the incumbent saw once — that is sampling noise, and
          -- forbidding it would reject every candidate. It may not drop one the incumbent saw twice or
          -- more: measured, those losses survive 10x more sampling and so are a real distribution
          -- shift, not chance.
          let keepsReach := keepsRepeatedPaths s' base
          let (cov', _) := coverage.miss s'.root
          let gap := combined (goal.gapCenti base s') cov'
          -- Believe an improvement only if it clears the noise floor. Discard regression rejects the
          -- candidate outright, whether or not the composite gap improved.
          let accept := discardOK && keepsReach && match gap with
            | some m => m + tolerance < bestGap
            | none => false
          let step : WeightStep :=
            { round := pass + 1, ctorName := some ctorName, tweak := cand,
              accepted := accept, stats := some s', gapCenti := gap }
          trace := trace ++ [step]
          if accept then
            wb := wb'
            bestGap := gap.getD bestGap
            improved := true
    if !improved then break
  -- Say so when the goal was never in reach, rather than leaving a plateau to be read as convergence.
  if bestGap > tolerance then
    let step : WeightStep :=
      { round := passes + 1, accepted := false,
        note := s!"closest reachable is {renderCenti bestGap} off target — no \
          weighting at this size gets there; raise the size or lower the target" }
    trace := trace ++ [step]
  return (wb, trace)

/-! ## The loop -/

/-- One round of the search, kept for the report. -/
structure LearnStep where
  /-- Round number; `0` is the starting book. -/
  round : Nat
  /-- What the round was aimed at, if anything. -/
  target : Option BlameTarget
  /-- The plan tried, when a candidate was tried. -/
  plan : Option Plan := none
  /-- Whether it became the new incumbent. -/
  accepted : Bool := false
  /-- What it measured, when it could be measured. -/
  stats : Option ClosureStats := none
  /-- What happened, in words. -/
  note : String := ""

/-- Renders a search trace. -/
def renderLearn (specs : List RelSpec) (trace : List LearnStep) : String :=
  let one := fun (t : LearnStep) =>
    let mark := if t.accepted then "✔" else " "
    let score := match t.stats with
      | some s => s.renderLine
      | none => t.note
    let aim := match t.target with
      | none => ""
      | some b =>
        let premise := renderPremise specs b.key b.ctorName b.premiseIdx
        s!"\n      aim: {renderSpecKey b.key} / {b.ctorName} · {premise} ({b.discards}×)"
    let plan := match t.plan with
      | none => ""
      | some p => s!"\n      plan: " ++ "; ".intercalate (p.map (fun (st : PlanStep) =>
          match st with | .use i => s!"use {i}" | .inst v => s!"{v} ← arbitrary"))
    s!"{mark} r{t.round}  {score}{aim}{plan}"
  "[interp] learning trace:\n" ++ "\n".intercalate (trace.map one)

/-- Candidate plans for one constructor, risk-ranked and aimed at a blamed premise.

    Two sources, in this order: every ordering ranked by `estimateRisk` (which is free, and much less
    myopic than stepping), then the mutations `mutationsFor` proposes around the blamed premise (which
    can reach plans the enumeration capped away). The current plan is dropped, since re-measuring it
    would waste a round. -/
def learnCandidates (env : InterpEnv) (rel : RelSpec) (key : SpecKey) (c : CtorSpec)
    (current : Plan) (blamedPremise : Option Nat) (specs : List RelSpec) (derivable : List Name)
    (width : Nat := 4) (limit : Nat := 24) : List Plan :=
  let ranked := (rankPlansByRisk env rel key c limit specs derivable).filterMap (fun (p, r, _) =>
    match r with
    | .ok _ => some p
    | .error _ => none)
  let aimed := match blamedPremise with
    | some i => mutationsFor c current [i]
    | none => []
  -- `aimed` first, and the order matters: `learnSchedules` accepts the *first* candidate that measures
  -- better and stops. `aimed` comes from `rootCauses` — measured evidence about which premise threw the
  -- work away — while `ranked` is `ScheduleRisk`'s guess. Letting the guess go first means a marginal
  -- risk-ranked plan can be accepted before the evidence-driven mutation is ever measured, which is
  -- exactly the failure mode of letting an unvalidated surrogate decide. Risk still orders what follows.
  (aimed ++ ranked.take width).foldl (fun acc p =>
    if p == current || acc.contains p then acc else acc ++ [p]) []

/-- Whether a mutation could plausibly remove this blame — the test that keeps the search from spending
    rounds on premises no ordering can fix.

    Measurement says *where* the work goes; that is not the same as *what a reordering can do about it*.
    Two kinds of blamed premise are immovable:

* an equality against a **function application** (`(decimal s) = some d`): the schedule cannot invert
  `decimal` to produce `s`, so the premise is generate-and-test however it is ordered. Cedar's
  `ValidDecimal`/`ValidIP` are exactly this, and they head the measured blame list.
* a check on a relation nothing can *produce*: with no producing mode available, demotion is the only
  option and the check has to stay.

Everything else is fair game. This is the surrogate used for what it is legitimately good at — a
necessary condition on actionability — rather than as the objective, which is the distinction that keeps
`ScheduleRisk` from deciding anything. -/
def BlameTarget.actionable (t : BlameTarget) (env : InterpEnv) (specs : List RelSpec)
    (derivable : List Name) : Bool :=
  match t.premiseIdx with
  | none => false  -- a prologue `Match`: no premise to move.
  | some i =>
    match (ctorSpecOf? specs t.key t.ctorName).bind (fun c => c.hypotheses[i]?) with
    | none => false
    | some (relName, args) =>
      if relName == ``Eq || relName == ``Ne then
        -- Invertible only if neither side is a function application.
        !args.any (fun a => match a with | .FuncApp .. => true | _ => false)
      else env.canProduce derivable relName

/-- Learns a whole generator: measure the closure, find where the discards really originate, try
    risk-ranked alternatives for that constructor, keep what measures better, repeat.

    Stops when `ClosureRisk.isIdeal` holds — every remaining rejection is irreducible — or when no
    candidate improves anywhere, or after `rounds` rounds. Returns the winning book together with the
    trace, because the trace is where the insight is.

    `env` supplies only the leaves; every schedule is derived from `specs` through the book, so a
    candidate that needs a mode nobody derived gets it.

    `deriveCheckers` defaults to `true` here, unlike on `deriveClosure` itself. A plan search varies
    **polarity**: moving a premise later is exactly what turns it into a `Check`, so a checker for a
    relation this environment only *generates* is needed by construction. Left `false`, every candidate
    that demotes anything comes back unbuildable — on Cedar's `HasType` closure that was all of them, 57
    missing-checker issues before a single measurement. -/
def InterpEnv.learnSchedules (env : InterpEnv) (specs : List RelSpec) (rootKey : SpecKey)
    (size : Nat) (inputs : List Val := []) (n : Nat := 100) (rounds : Nat := 6)
    (width : Nat := 4) (limit : Nat := 24) (start : PlanBook := {})
    (seeds : List Nat := defaultSeeds) (budget : ProfileBudget := {}) (fuel : Nat := 64)
    (deriveCheckers : Bool := true) (targetsPerRound : Nat := 6)
    (objectiveKind : ObjectiveKind := .waste) (pinnableOnly : Bool := false)
    (prepare : InterpEnv → InterpEnv := id) :
    IO (PlanBook × List LearnStep) := do
  let derivable := specs.map RelSpec.inductiveName
  -- Builds the closure for a book and measures it, or explains why it cannot be measured.
  -- Under `throughput`, a candidate is judged by the root sample alone, so the 587-pair profile is
  -- skipped: 2.2s instead of 32s on Cedar. Blame still needs the profile, which is taken for every
  -- *incumbent*: the starting one, and each accepted candidate.
  -- An accepted candidate was measured without it, so it is re-measured once with the profile before
  -- becoming the incumbent (see the acceptance below); otherwise every later round falls back to static
  -- `avoidableTargets`, as it did on Cedar before.
  let profileFor := fun (full : Bool) => full || objectiveKind == .waste
  let measureWith := fun (full : Bool) (b : PlanBook) => do
    match env.deriveClosureWith specs [rootKey] b limit fuel deriveCheckers with
    | .error e => return (.error e : Except String (InterpEnv × ClosureStats))
    -- A derived `Checker` mode is invisible to a *generator*'s `Check` step until it is published as a
    -- name-keyed leaf, so publish before measuring; otherwise every demoting candidate reports
    -- "no checker registered" for a checker sitting in its own closure. See
    -- `InterpEnv.publishInterpretedCheckers`.
    | .ok builtRaw =>
      -- `prepare` makes each candidate closure sample like the generator that will ship — the compiled
      -- weights and instance-backed leaves (`DeriverChoice.withCompiledWeights`, `withInstanceLeaves`).
      -- Without it every candidate is measured on the interpreter's defaults, which on Cedar reached three
      -- times the distinct paths the compiled generator did, and an order "learned" that way did nothing
      -- once pinned.
      let built := (prepare builtRaw).publishInterpretedCheckers
      match built.validate with
      | .error report => return .error report
      | .ok () =>
      return .ok (built,
        ← built.closureStatsOver rootKey size inputs n seeds budget (profileFor full))
  let measure := measureWith true
  let mut book := start
  let mut trace : List LearnStep := []
  let mut best : Option ClosureStats := none
  let mut builtEnv : Option InterpEnv := none
  match ← measure book with
  | .error e =>
    return (book, [{ round := 0, target := none, note := s!"cannot build: {e}" }])
  | .ok (built, s) =>
    best := some s
    builtEnv := some built
    trace := [{ round := 0, target := none, accepted := true, stats := some s,
                note := "starting book" }]
  -- Constructors already shown to have no better plan; do not aim at them again.
  let mut exhausted : List (SpecKey × Name × Option Nat) := []
  for round in List.range rounds do
    let some incumbent := best | break
    let some current := builtEnv | break
    let risk := current.closureRisk specs derivable
    if risk.isIdeal then
      let step : LearnStep :=
        { round := round + 1, target := none, note := s!"ideal: {risk.renderLine}" }
      trace := trace ++ [step]
      break
    -- Aim at the heaviest measured origin whose constructor is not exhausted; fall back to the
    -- heaviest *static* avoidable rejection when nothing was measured (a rejection can be real yet
    -- unobserved at this size).
    -- Measured blame, restricted to premises a mutation could actually move. Without the
    -- `actionable` filter the search aims at the heaviest blame regardless, and on Cedar that is
    -- `ValidDecimal`/`ValidIP` — `Eq` against a function application, unfixable by any ordering — so
    -- three rounds and 14 candidates produced not one accepted change.
    let allCauses := (incumbent.rootCauses current specs book).filter (fun t =>
      !exhausted.contains (t.key, t.ctorName, t.premiseIdx) && t.premiseIdx.isSome)
    let causes := allCauses.filter (fun t => t.actionable current specs derivable)
    let staticTargets := risk.avoidableTargets.filter (fun (k, ctor, _) =>
      !exhausted.contains (k, ctor, none))
    -- Several targets per round, not one. A target that yields no improvement leaves the closure exactly
    -- as it was, so spending a whole round on it buys nothing: the round should keep descending the blame
    -- list until something improves. `rounds` therefore budgets *improvements*, and `targetsPerRound`
    -- bounds the work spent looking for each one. With one target per round, six rounds examined six of
    -- Cedar's sixty actionable targets — 10% — and every one of them failed.
    let ranked : List BlameTarget :=
      if !causes.isEmpty then causes
      else staticTargets.map (fun (k, ctor, _) =>
        { key := k, ctorName := ctor, premiseIdx := none, discards := 0, depth := 0 })
    if ranked.isEmpty then break
    let mut improved := false
    for aim in ranked.take targetsPerRound do
      if improved then break
      match specs.find? (fun r => r.inductiveName == aim.key.inductiveName) with
      | none => pure ()
      | some rel =>
        match rel.ctors.find? (fun k => k.ctorName == aim.ctorName) with
        | none => pure ()
        | some c =>
          -- Mutate the plan that is actually installed (after repair, or the resolvable choice), not the
          -- book's bare entry: the two differ for exactly the constructors blame most often names.
          let installed := (current.relations[aim.key]?).bind (·.provenanceOf? aim.ctorName)
          let current' := match installed with
            | some p => p.plan
            | none => book.planFor rel aim.key c
          let candidates :=
            learnCandidates current rel aim.key c current' aim.premiseIdx specs derivable width limit
          for cand in candidates do
            if improved then break
            -- A plan the compile-time deriver cannot be told to use — one with an elective `inst` — is
            -- worth nothing to a search whose output is a pin table, and measuring it costs a closure
            -- build. On Cedar the only "improvement" one run accepted was exactly such a plan.
            if pinnableOnly && (PlanBook.unpinnableInsts rel aim.key c cand).isSome then
              trace := trace ++ [{ round := round + 1, target := some aim, plan := some cand,
                                   note := "skipped: elective inst, cannot be pinned" }]
              continue
            let b' := book.set aim.key aim.ctorName cand
            match ← measureWith (objectiveKind == .waste) b' with
            | .error e =>
              trace := trace ++ [{ round := round + 1, target := some aim, plan := some cand,
                                   note := s!"unbuildable: {e}" }]
            | .ok (built', s') =>
              -- Better, and not *newly* misconfigured. Demanding `interpErrors == 0` instead is right
              -- only when a missing leaf is their one source: `closureStats` profiles every mode on the
              -- *root's* inputs, so a mode of unrelated arity always reports some, and Cedar's closure
              -- sits at a background 1282. That bar is then unsatisfiable, and rejects even a genuine
              -- improvement (waste 441‰ against 443‰) among 306 candidates over 30 targets. What
              -- matters is that a candidate did not introduce errors the incumbent did not have.
              --
              -- Coverage non-regression is unconditional, not part of the objective. Under `.waste` or
              -- `.throughput` a candidate that stops a rule firing scores as a large *improvement*
              -- (Cedar's `unaryAppIsTrue`: 3.0× faster, 2.5× less waste, 110 k-paths gone and none
              -- gained), so leaving this to the objective means whichever objective is selected can be
              -- gamed the same way. A plan that no longer reaches a shape the incumbent reached is not a
              -- trade-off to weigh — it is inadmissible. `.coverage` additionally *ranks* by reach.
              --
              -- The root sample is compared too. The per-pair profile above is only taken under
              -- `.waste`, so under `.coverage` and `.throughput` a candidate's `interpErrors` was always 0
              -- and the guard saw nothing; since `backtrackInterp` re-throws misconfiguration, a root
              -- attempt that reaches a broken rule now counts as one, and that is what this reads.
              --
              -- Under `.coverage` the reach gate is the *net* one (`keepsRepeatedPaths`: no loss of a
              -- reliably-reached path without a matching gain) and acceptance needs a real coverage gain.
              -- The strict superset stays for the other objectives, which can be gamed by a rule that
              -- stops firing. Under `.coverage` the strict superset refused every net gain — on Cedar
              -- 130 paths against the incumbent's 126, and faster, was refused for losing one path — and
              -- `betterBy`'s speed tie-break accepted plans on wall-clock noise alone.
              let reachOK := match objectiveKind with
                | .coverage => keepsRepeatedPaths s' incumbent && coverageGain s' incumbent
                | _ => coversAtLeast s' incumbent
              let accept := betterBy objectiveKind s' incumbent
                && s'.interpErrors <= incumbent.interpErrors
                && s'.root.interpErrors <= incumbent.root.interpErrors
                && reachOK
              trace := trace ++ [{ round := round + 1, target := some aim, plan := some cand,
                                   accepted := accept, stats := some s' }]
              if accept then
                book := b'
                best := some s'
                builtEnv := some built'
                improved := true
                -- Under `.coverage`/`.throughput` the candidate was measured without the per-pair profile,
                -- so the new incumbent has no measured blame and every later round would fall back to
                -- static targets. Re-measure it once, with the profile. (Observed on Cedar before this:
                -- after one acceptance, rounds 2–4 had nothing measured to aim at.)
                if !profileFor false then
                  match ← measure b' with
                  | .ok (built'', s'') =>
                    best := some s''
                    builtEnv := some built''
                  | .error _ => pure ()
          -- Exhaustion is per *premise*, not per constructor: a constructor with several blamed premises
          -- has several independent things a mutation could act on, and writing all of them off because
          -- the heaviest one failed is how a search stops looking at a place it has barely examined.
          if !improved then
            exhausted := exhausted ++ [(aim.key, aim.ctorName, aim.premiseIdx)]
  return (book, trace)

/-! ## Both phases

    Plans first, then weights. The order is not a preference: a plan changes which constructors exist
    and which specs they call, so the set of things a weight tweak applies to is not even fixed until
    the plan search has settled. Doing it the other way round would tune weights for a closure that
    then changes underneath them. -/

/-- What a full run produced. -/
structure LearnedGenerator where
  /-- The plan chosen per constructor per mode. -/
  plans : PlanBook
  /-- The affine weight adjustment per recursive constructor. -/
  weights : WeightBook
  /-- Phase-one trace: which premise was blamed and what moving it did. -/
  planTrace : List LearnStep := []
  /-- Phase-two trace: which constructor was reweighted and what it cost. -/
  weightTrace : List WeightStep := []
  deriving Inhabited

/-- Rebuilds the closure this run learned. -/
def InterpEnv.buildLearned (env : InterpEnv) (specs : List RelSpec) (rootKey : SpecKey)
    (g : LearnedGenerator) (limit : Nat := 24) : Except String InterpEnv :=
  (env.deriveClosureWith specs [rootKey] g.plans limit).map (·.withWeightBook g.weights)

/-- Learns a generator end to end: remove the avoidable discards, then shape the output size.

    Phase one stops at `ClosureRisk.isIdeal` — every remaining rejection irreducible. Phase two is
    given an explicit `SizeGoal`, because there is no canonical output size to converge on, only the
    one you ask for; passing `none` skips it and leaves the weighting at the pipeline's default. -/
def InterpEnv.learnGenerator (env : InterpEnv) (specs : List RelSpec) (rootKey : SpecKey)
    (size : Nat) (inputs : List Val := []) (n : Nat := 100) (rounds : Nat := 6)
    (goal : Option SizeGoal := none) (width : Nat := 4) (passes : Nat := 2) (limit : Nat := 24)
    (start : PlanBook := {}) (seeds : List Nat := defaultSeeds) (coverage : CoverageGoal := {})
    (budget : ProfileBudget := {}) (fuel : Nat := 64) (deriveCheckers : Bool := true)
    (targetsPerRound : Nat := 6) : IO LearnedGenerator := do
  let (plans, planTrace) ←
    env.learnSchedules specs rootKey size inputs n rounds width limit start seeds budget fuel
      deriveCheckers
  match goal, coverage.bands.isEmpty with
  | none, true => return { plans := plans, weights := {}, planTrace := planTrace }
  | _, _ =>
    -- With no size goal, phase two runs against a *trivial* size target — mean 0 with a tolerance so
    -- large nothing ever clears it — so only the coverage half of the objective can move.
    --
    -- The discard slack is the caller's when a size goal was given (0 by default, i.e. no regression
    -- allowed). For a pure coverage run the fallback allows **50‰**: reaching an under-represented shape
    -- sometimes costs a few discards, because favouring `Node` over `Leaf` shifts more `Between` calls to
    -- bounds it may miss, and refusing any increase rejects those candidates outright.
    let effGoal : SizeGoal :=
      goal.getD { targetCenti := 0, discardSlackPerMille := 50, toleranceCenti := 1000000 }
    let (weights, weightTrace) ←
      env.tuneWeights specs rootKey plans effGoal size inputs n passes limit seeds coverage budget
        fuel deriveCheckers
    return { plans := plans, weights := weights, planTrace := planTrace,
             weightTrace := weightTrace }

/-- Renders both phases. -/
def renderLearned (specs : List RelSpec) (g : LearnedGenerator) : String :=
  renderLearn specs g.planTrace
    ++ (if g.weightTrace.isEmpty then "" else "\n\n" ++ renderWeights g.weightTrace)

end Specimen.Interp
