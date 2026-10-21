import Specimen.Interp.Bridge
import Specimen.Interp.Validate
import Specimen.Interp.Preschedule
import Specimen.Interp.CheckEnum

/-!
# Running schedule experiments

The point of interpreting schedules at runtime is to compare them. This module is the experiment
loop: sample a spec many times, classify the failures, and sweep the plans for a constructor to see
which one actually produces values.

* `InterpEnv.sample` — run a spec `n` times at one size and summarise.
* `InterpEnv.sampleSizes` — the same across a range of sizes, the way a test driver ramps size.
* `InterpEnv.sweepPlans` — for each candidate plan (`Specimen.Interp.plansOf`), re-derive the
  constructor's schedule, bring up the modes it needs, and measure it.

A sweep varies the *plan*, not the finished schedule's steps, because reordering premises changes
which variables each premise produces and hence which spec it calls — see
`Specimen.Interp.Preschedule`. Permuting steps cannot express those alternatives.

Everything here goes through `Specimen.Interp.interpRel`, so the numbers describe the schedules, not
a reimplementation of them.

## A note on the RNG

`Gen` is `StateT StdGen` over `Except`, so a thrown error rolls the PRNG back to where the attempt
began: a naive retry loop replays the identical failing draw. `attempt` calls `Gen.randSkip` on
failure, jumping to an independent stream so each attempt is a genuinely different input while
staying deterministic in the starting seed. (Inside a single run, `backtrack` retrying a branch
*does* roll the seed back — that is specimen's real behaviour, and interpreting it faithfully means
keeping it.)
-/

open Lean Plausible Schedules

namespace Specimen.Interp

/-- The message inside a `GenError`. -/
def errMsg : GenError → String
  | .genError m => m

/-! ## Reproducible runs

    `Plausible.Gen.run` draws its seed from the global `stdGenRef`, so two runs of the same generator
    see different draws. That is right for testing and wrong for *comparing*: a search that measures
    candidate A and candidate B on different draws is reading the difference between two sample means,
    and for a metric like average output size the run-to-run spread is easily larger than the effect
    being looked for.

    `runSeeded` fixes the seed instead, so a comparison is paired — every candidate faces the identical
    sequence of draws, and the difference between them is the difference between the *schedules*. This
    is the standard common-random-numbers trick, and it is the difference between a tuner that
    converges and one that banks noise.

    A fixed seed is not a free lunch: it measures one sample path, so a candidate can win by suiting
    that path. Vary the seed across a few values and require a candidate to win on all of them, which
    is what `seeds` in the tuning loop is for. -/

/-- Runs a generator at a size, with the seed given rather than drawn: `none` reproduces
    `Plausible.Gen.run`. -/
def runSeeded {α : Type} (seed : Option Nat) (g : Gen α) (size : Nat) : IO α :=
  match seed with
  | none => Gen.run g size
  | some s =>
    -- The lift replicates `Plausible.Gen.run`'s, including the `"Generation failure:"` prefix that
    -- `GeneratorCombinators.runChecked` strips back off, since Plausible's own is `private`.
    letI : MonadLift (ReaderT (ULift Nat) (Except GenError)) IO :=
      ⟨fun m =>
        match ReaderT.run m ⟨size⟩ with
        | .ok a => pure a
        | .error (.genError msg) => throw (IO.userError ("Generation failure:" ++ msg))⟩
    Plausible.runRandWith s g

/-- Runs a generator once, returning its failure instead of propagating it, and decorrelating the
    PRNG on failure so a subsequent attempt is a genuinely different input. -/
def attempt {α : Type} (g : Gen α) : Gen (Except GenError α) := do
  -- A failed attempt keeps no rule paths (see `pathMark`); the mark depends on the state so that it is
  -- taken per attempt.
  let st ← get
  tryCatchPaths st.down.1 (Except.ok <$> g) (fun e => do Gen.randSkip; return .error e)

/-- Runs a generator `n` times independently. -/
def attemptN {α : Type} (n : Nat) (g : Gen α) : Gen (List (Except GenError α)) :=
  (List.range n).mapM (fun _ => attempt g)

/-- Why an attempt failed. `interp` means the environment is misconfigured, not that the schedule is
    unproductive — always fix those first. -/
inductive FailureKind where
  /-- Fuel or size exhausted: inconclusive, might succeed at a larger size. -/
  | outOfFuel
  /-- Interpreter misconfiguration (a missing leaf, an unsupported step). -/
  | interp
  /-- A check failed or a pattern did not match: the schedule genuinely rejected this attempt. -/
  | rejected
  deriving Repr, BEq

/-- Classifies a failure. -/
def classifyFailure (e : GenError) : FailureKind :=
  if isInterpError e then .interp
  else if Gen.GenError.isInconclusive e then .outOfFuel
  else .rejected

/-- Renders a hundredths figure with two decimals, zero-padded.

    The padding is not cosmetic: without it `106` prints as `1.6`, which reads as a larger number than
    `114`'s `1.14` and inverts the comparison a reader is making. -/
def renderCenti (n : Nat) : String :=
  let frac := n % 100
  s!"{n / 100}.{if frac < 10 then "0" else ""}{frac}"

/-- Summary of a batch of attempts. -/
structure RunStats where
  /-- How many times the generator was run. -/
  attempts : Nat := 0
  /-- How many produced a value. -/
  successes : Nat := 0
  /-- Failures attributed to exhausted fuel or size. -/
  outOfFuel : Nat := 0
  /-- Failures attributed to interpreter misconfiguration. -/
  interpErrors : Nat := 0
  /-- Failures where the schedule rejected the attempt. -/
  rejected : Nat := 0
  /-- Summed `Val.size` over the successes, for an average output size. -/
  totalOutputSize : Nat := 0
  /-- The first misconfiguration message seen, which is what to fix. -/
  firstInterpError : Option String := none
  /-- The first few successes, kept for eyeballing. -/
  samples : List (List Val) := []
  /-- Counts of constructor names appearing anywhere in the successful outputs.

      This is what Cedar's hand-tuned `favorHasTag` weight modifier is a response to — it boosts
      `record`, `hasTagTt`, `unaryAppIsEmpty` and suppresses `binaryAppEqLitSame` in exactly the
      proportions the *coverage* histogram of the untuned generator warranted. Without measuring the
      histogram, a tuner cannot see the difference between two schedules that discard the same amount
      but produce very different distributions of output shapes. -/
  ctorCounts : List (Name × Nat) := []
  /-- The distinct k-paths (`Val.kPaths`) seen across all successes, at depth `kPathDepth`.

      This is the coverage target proper. `ctorCounts` is its k = 1 shadow and cannot express rule
      *interaction*: it scores a generator that only nests literals under each operator the same as
      one that nests every shape.

      Counts, not a bare set. The objective only cares whether a shape was reached at all, so
      `kPathCount` ignores them — but a *comparison* needs them: a path one book reached once in 120
      samples and another missed is almost certainly chance, while a path reached fifty times and then
      missed is a real distribution shift. Weight tuning is entitled to the first kind of loss (weights
      change the measure, not the support) and not obviously to the second, and the set view could not
      tell them apart. -/
  kPathsSeen : List (List Name × Nat) := []
  /-- The distinct rule paths (`withRulePaths`, depth `rulePathDepth`) of the derivations behind the
      successes. The other half of the coverage target: output paths cannot tell typing rules apart —
      Cedar's `andShort`, `andTtTt` and `andAnyAny` all build the same `Expr.and` node — so a change that
      makes one rule reachable is invisible to them unless its output shape is new. -/
  rulePathsSeen : List (List Name) := []
  deriving Repr, Inhabited

namespace RunStats

/-- Success rate in per mille, so reports stay integral and reproducible. -/
def successPerMille (s : RunStats) : Nat :=
  if s.attempts == 0 then 0 else s.successes * 1000 / s.attempts

/-- Average output size in hundredths of a constructor node. -/
def avgOutputSizeCenti (s : RunStats) : Nat :=
  if s.successes == 0 then 0 else s.totalOutputSize * 100 / s.successes

/-- Renders a per-mille figure as a percentage with one decimal. -/
private def pct (perMille : Nat) : String :=
  s!"{perMille / 10}.{perMille % 10}%"

/-- Renders a hundredths figure with two decimals. -/
private def centi (n : Nat) : String := renderCenti n

/-- Total constructor occurrences summed across successful outputs. -/
def totalCtorOccurrences (s : RunStats) : Nat :=
  s.ctorCounts.foldl (fun acc p => acc + p.2) 0

/-- Constructor counts sorted descending. -/
def sortedCtorCounts (s : RunStats) : List (Name × Nat) :=
  s.ctorCounts.foldl (fun acc p =>
    let rec ins : List (Name × Nat) → List (Name × Nat)
      | [] => [p]
      | q :: qs => if p.2 > q.2 then p :: q :: qs else q :: ins qs
    ins acc) []

/-- Coverage histogram, top-`n` heaviest first. -/
def renderCoverage (s : RunStats) (n : Nat := 20) : String :=
  let total := s.totalCtorOccurrences
  let head :=
    s!"[interp] coverage: {s.ctorCounts.length} distinct ctors, {total} occurrences across       {s.successes} success(es)"
  if s.ctorCounts.isEmpty then head
  else head ++ "\n" ++ "\n".intercalate ((s.sortedCtorCounts.take n).map (fun (nm, c) =>
    let pct := if total == 0 then 0 else c * 100 / total
    s!"  {c} ({pct}%)  {nm}"))

/-- A one-line summary. -/
def renderLine (s : RunStats) : String :=
  s!"{s.successes}/{s.attempts} ({pct s.successPerMille}) \
    · avg size {centi s.avgOutputSizeCenti} \
    · fuel {s.outOfFuel} · rejected {s.rejected} · interp {s.interpErrors}"

/-- A multi-line report, including the misconfiguration to fix and a few sample outputs. -/
def render (s : RunStats) : String :=
  let head := s!"[interp] {s.renderLine}"
  let err := match s.firstInterpError with
    | some m => s!"\n  ! misconfiguration: {m}"
    | none => ""
  let samples :=
    if s.samples.isEmpty then ""
    else "\n" ++ "\n".intercalate
      (s.samples.map (fun vs => "  · " ++ ", ".intercalate (vs.map toString)))
  head ++ err ++ samples

/-- Path depth for `kPathsSeen`.

    3 rather than 2 because 2 only says "this constructor can sit under that one", which the premise
    structure mostly determines anyway; 3 is the first depth that distinguishes *which* shape an
    operator's operand takes, which is what a schedule change actually moves. Higher is strictly more
    discriminating and strictly more expensive to saturate — at some depth every run looks equally
    incomplete and the measure stops ranking. -/
def kPathDepth : Nat := 3

/-- Unions two k-path sets. Linear scan; the sets are small (hundreds) and this runs once per
    success. -/
private def unionPaths (a b : List (List Name × Nat)) : List (List Name × Nat) :=
  b.foldl (fun acc (p, k) =>
    match acc.find? (fun q => q.1 == p) with
    | some _ => acc.map (fun q => if q.1 == p then (q.1, q.2 + k) else q)
    | none => acc ++ [(p, k)]) a

/-- Merges a batch of ctor-name occurrences into a running count list. Linear in the count list,
    which is fine for the low-hundreds of distinct constructor names a Cedar-scale closure has. -/
private def bumpCounts (counts : List (Name × Nat)) (names : List Name) : List (Name × Nat) :=
  names.foldl (fun acc n =>
    let rec go : List (Name × Nat) → List (Name × Nat)
      | [] => [(n, 1)]
      | (m, k) :: rest => if m == n then (m, k + 1) :: rest else (m, k) :: go rest
    go acc) counts

/-- Folds one attempt's outcome into the running summary. -/
def record (s : RunStats) (keepSamples : Nat) : Except GenError (List Val) → RunStats
  | .ok vals =>
    { s with
      attempts := s.attempts + 1
      successes := s.successes + 1
      totalOutputSize := s.totalOutputSize + (vals.map Val.size).foldl (· + ·) 0
      samples := if s.samples.length < keepSamples then s.samples ++ [vals] else s.samples
      -- Count coverage on every success, whether the sample was kept or dropped: coverage is what
      -- lets the tuner see which constructors the generator actually reaches.
      ctorCounts := bumpCounts s.ctorCounts (vals.flatMap Val.ctorNames)
      kPathsSeen := unionPaths s.kPathsSeen
        ((vals.flatMap (Val.kPaths kPathDepth)).map (fun p => (p, 1))) }
  | .error e =>
    match classifyFailure e with
    | .outOfFuel => { s with attempts := s.attempts + 1, outOfFuel := s.outOfFuel + 1 }
    | .rejected => { s with attempts := s.attempts + 1, rejected := s.rejected + 1 }
    | .interp =>
      { s with
        attempts := s.attempts + 1
        interpErrors := s.interpErrors + 1
        firstInterpError := s.firstInterpError.getD (errMsg e) }

/-- Summarises a list of outcomes. -/
def ofOutcomes (outcomes : List (Except GenError (List Val))) (keepSamples : Nat := 3) :
    RunStats :=
  outcomes.foldl (fun s o => s.record keepSamples o) {}

/-- Merges two summaries (samples from the first are kept first). -/
def merge (a b : RunStats) : RunStats where
  attempts := a.attempts + b.attempts
  successes := a.successes + b.successes
  outOfFuel := a.outOfFuel + b.outOfFuel
  interpErrors := a.interpErrors + b.interpErrors
  rejected := a.rejected + b.rejected
  totalOutputSize := a.totalOutputSize + b.totalOutputSize
  firstInterpError := a.firstInterpError.orElse (fun _ => b.firstInterpError)
  samples := a.samples ++ b.samples
  ctorCounts := b.ctorCounts.foldl (fun acc (n, k) => bumpCounts acc (List.replicate k n)) a.ctorCounts
  kPathsSeen := unionPaths a.kPathsSeen b.kPathsSeen
  rulePathsSeen :=
    let seen : Std.HashSet (List Name) := Std.HashSet.ofList a.rulePathsSeen
    a.rulePathsSeen ++ (b.rulePathsSeen.filter (!seen.contains ·))

/-- How many distinct k-paths were reached: the coverage score, higher is better.

    Unlike every cost measure, this one cannot be gamed by generating less — a generator that stops
    firing a rule loses the paths that rule built. -/
def kPathCount (s : RunStats) : Nat := s.kPathsSeen.length

/-- How many distinct rule paths the derivations reached. -/
def rulePathCount (s : RunStats) : Nat := s.rulePathsSeen.length

/-- The coverage target: distinct output k-paths plus distinct rule k-paths. -/
def coverage (s : RunStats) : Nat := s.kPathCount + s.rulePathCount

/-- The k-paths in `a` that `b` never reached. What a coverage regression *is*, concretely. -/
def kPathsLost (a b : RunStats) : List (List Name × Nat) :=
  a.kPathsSeen.filter (fun p => !b.kPathsSeen.any (fun q => q.1 == p.1))

/-- How many of `a`'s paths that `b` never reached were seen **only once** in `a`.

    The distinction the set view could not make. A path `a` hit once in 120 samples is almost certainly
    absent from `b` by chance; one `a` hit fifty times is a real distribution shift. Weight tuning is
    entitled to the first kind of loss — weights change the measure, not the support — and not obviously
    to the second. -/
def kPathsLostSingletons (a b : RunStats) : Nat :=
  ((kPathsLost a b).filter (fun p => p.2 == 1)).length

/-- Renders a k-path as `outer > inner > innermost`, short names only. -/
def renderPath (p : List Name) : String :=
  " > ".intercalate (p.map (fun n => (n.componentsRev.head?.getD n).toString))

/-- The coverage report: how many paths, and a sample of them. -/
def renderKPaths (s : RunStats) (n : Nat := 12) : String :=
  s!"[interp] {s.kPathCount} distinct {kPathDepth}-paths" ++
    (if s.kPathsSeen.isEmpty then ""
     else "\n" ++ "\n".intercalate ((s.kPathsSeen.take n).map (fun (p, k) =>
       s!"  {renderPath p} ×{k}")))

end RunStats

/-- Runs a spec `n` times at one size and summarises the outcomes. -/
def InterpEnv.sample (env : InterpEnv) (key : SpecKey) (size : Nat) (inputs : List Val := [])
    (n : Nat := 200) (keepSamples : Nat := 3) (seed : Option Nat := none) : IO RunStats := do
  -- Rule paths too, unless a caller is already recording them: the recorder is one module-level ref.
  if ← rulePathEnabledRef.get then
    let outcomes ← runSeeded seed (attemptN n (env.generate key size inputs)) size
    return RunStats.ofOutcomes outcomes keepSamples
  else
    let (outcomes, paths) ← withRulePaths (runSeeded seed (attemptN n (env.generate key size inputs)) size)
    return { RunStats.ofOutcomes outcomes keepSamples with rulePathsSeen := paths }

/-- Runs a spec across a range of sizes, the way a test driver ramps size, and returns the summary
    per size alongside the merged total. -/
def InterpEnv.sampleSizes (env : InterpEnv) (key : SpecKey) (sizes : List Nat)
    (inputs : List Val := []) (n : Nat := 100) (keepSamples : Nat := 2) :
    IO (List (Nat × RunStats) × RunStats) := do
  let mut per := []
  let mut total : RunStats := {}
  for size in sizes do
    let s ← env.sample key size inputs n keepSamples
    per := per ++ [(size, s)]
    total := total.merge s
  return (per, total)

/-! ## Where does it discard?

    A success rate says a schedule wastes 90% of its attempts; it does not say which step throws them
    away, and that is the actionable part. `profileCtor` runs one constructor's schedule with
    `runCtorOnce` — no `backtrack`, so nothing absorbs the failure — and reads the step index the
    interpreter attributed each discard to (`Specimen.Interp.rejectAt`).

    Measuring one constructor in isolation is the right conditioning: what you want to know is "given
    that this constructor was chosen, where does it fail?", not the marginal over a weighted choice
    among constructors. -/

/-- Discards attributed to one step of a schedule. -/
structure StepDiscards where
  /-- Index of the step in the schedule. -/
  stepIdx : Nat
  /-- The step, rendered. -/
  rendered : String
  /-- How many attempts died here. -/
  discards : Nat
  deriving Repr, Inhabited

/-- Where one constructor's schedule spends its attempts. -/
structure CtorProfile where
  /-- The constructor profiled. -/
  ctorName : Name
  /-- How many times its schedule was run. -/
  attempts : Nat := 0
  /-- How many produced a value. -/
  successes : Nat := 0
  /-- Attempts that ran out of fuel or size rather than being rejected. -/
  outOfFuel : Nat := 0
  /-- Attempts that hit interpreter misconfiguration. Fix these before reading anything else. -/
  interpErrors : Nat := 0
  /-- Discards that carried no step attribution. Should be 0; anything else means a failure escaped
      `blaming`. -/
  unattributed : Nat := 0
  /-- Per-step discard counts, in schedule order. -/
  perStep : List StepDiscards := []
  deriving Repr, Inhabited

namespace CtorProfile

/-- Total discards attributed to steps. -/
def discards (p : CtorProfile) : Nat :=
  p.perStep.foldl (fun acc s => acc + s.discards) 0

/-- Success rate in per mille. -/
def successPerMille (p : CtorProfile) : Nat :=
  if p.attempts == 0 then 0 else p.successes * 1000 / p.attempts

/-- `(stepIdx, discards)` pairs, for `Lowered.blame`. -/
def stepCounts (p : CtorProfile) : List (Nat × Nat) :=
  p.perStep.map (fun s => (s.stepIdx, s.discards))

end CtorProfile

/-- Runs one constructor's schedule `n` times and reports where the attempts went.

    Uses `InterpEnv.runCtorOnce`, so no `backtrack` sits between the failure and the report. -/
def InterpEnv.profileCtor (env : InterpEnv) (key : SpecKey) (ctorName : Name) (size : Nat)
    (inputs : List Val := []) (n : Nat := 200) (seed : Option Nat := none) : IO CtorProfile := do
  let some rel := env.relations[key]?
    | throw (IO.userError s!"[interp] no schedule registered for {renderSpecKey key}")
  let some (steps, _) := rel.ctorSchedule? ctorName
    | throw (IO.userError
        s!"[interp] {renderSpecKey key} has no schedule for constructor '{ctorName}'")
  let outcomes ← runSeeded seed (attemptN n (env.runCtorOnce key ctorName size inputs)) size
  let mut counts : List Nat := steps.map (fun _ => 0)
  let mut p : CtorProfile := { ctorName := ctorName, attempts := n }
  for o in outcomes do
    match o with
    | .ok _ => p := { p with successes := p.successes + 1 }
    | .error e =>
      if isInterpError e then p := { p with interpErrors := p.interpErrors + 1 }
      else if Gen.GenError.isInconclusive e then p := { p with outOfFuel := p.outOfFuel + 1 }
      else match rejectStepIdx? e with
        | some i =>
          counts := counts.zipIdx.map (fun (c, j) => if j == i then c + 1 else c)
        | none => p := { p with unattributed := p.unattributed + 1 }
  return { p with
    perStep := (steps.zipIdx.zip counts).map (fun ((step, i), c) =>
      { stepIdx := i, rendered := ppStep step, discards := c }) }

/-- Renders a profile: the schedule with a discard count against each step. -/
def renderProfile (p : CtorProfile) : String :=
  let head :=
    s!"[interp] {p.ctorName}: {p.successes}/{p.attempts} kept, {p.discards} discarded, \
      {p.outOfFuel} out of fuel, {p.interpErrors} misconfigured"
  let width := p.perStep.foldl (fun acc s => max acc (toString s.discards).length) 1
  let pad := fun (s : String) => "".pushn ' ' (width - min width s.length) ++ s
  let rows := p.perStep.map (fun s =>
    let share := if p.attempts == 0 then 0 else s.discards * 100 / p.attempts
    s!"  {pad (toString s.discards)} ({share}%)  {s.rendered}")
  head ++ (if rows.isEmpty then "" else "\n" ++ "\n".intercalate rows)

/-! ## Sweeping plans

    Sweeping means varying the *plan* — the order of a constructor's premises and which variables are
    generated unconstrained — and re-deriving the schedule for each, because that is the only kind of
    variation that means anything. Permuting a finished schedule's steps cannot express the
    interesting alternatives: it keeps every step's outputs and every callee's mode fixed, so it only
    ever commutes independent steps. See `Specimen.Interp.Preschedule`. -/

/-- Insertion sort, so the ranking does not depend on which `List.mergeSort` signature the toolchain
    ships. -/
private def sortBy {α : Type} (lt : α → α → Bool) (l : List α) : List α :=
  let rec insert (x : α) : List α → List α
    | [] => [x]
    | y :: ys => if lt x y then x :: y :: ys else y :: insert x ys
  l.foldl (fun acc x => insert x acc) []

/-- What became of one candidate plan. The three cases are genuinely different answers to "should I
    schedule it this way?", and collapsing them would hide the interesting one. -/
inductive PlanOutcome where
  /-- The plan is not a schedule at all: some premise would have to produce a variable it cannot.
      Nothing to measure. -/
  | rejected (reason : String)
  /-- The plan lowers to a schedule, but this environment cannot answer everything it calls — a mode
      no `RelSpec` covers, or a checker only a compile-time `DecOpt` derivation would provide.
      Reordering routinely does this: demoting a premise to a `Check` needs a *checker* for a
      relation you may only have a generator for. -/
  | unrunnable (sched : Schedule) (report : String)
  /-- The plan ran: sampled from the top, and profiled per step. -/
  | ran (sched : Schedule) (stats : RunStats) (profile : CtorProfile)

namespace PlanOutcome

/-- The schedule the plan lowered to, if it lowered. -/
def schedule? : PlanOutcome → Option Schedule
  | rejected _ => none
  | unrunnable s _ => some s
  | ran s _ _ => some s

/-- The top-level sample summary, if the plan ran. -/
def stats? : PlanOutcome → Option RunStats
  | ran _ s _ => some s
  | _ => none

/-- The per-step discard profile, if the plan ran. -/
def profile? : PlanOutcome → Option CtorProfile
  | ran _ _ p => some p
  | _ => none

/-- Ranking key, lower is better.

    The primary metric is the **discard rate of this constructor's own schedule**, not the top-level
    success rate. The two are very different, and only the first is a property of the schedule:
    `backtrack` falls through to another constructor when this one rejects, so the top-level success
    rate of a `BST` generator stays at 100% no matter how badly `BstNode` behaves — it just returns
    `Leaf` more often. Ranking on it would call a schedule that discards a fifth of its attempts
    indistinguishable from one that discards none.

    Ties break towards a *larger* average output, since a schedule that builds more structure per
    unit of size budget is doing more of the work asked of it. Then come plans that lowered but cannot
    run here, then plans that are not schedules at all. -/
def rank : PlanOutcome → Nat × Nat × Nat
  -- A plan whose own schedule hit interpreter misconfiguration ranks with the unrunnable ones: its
  -- `discards` can be 0 precisely *because* every attempt died internally, which would otherwise win.
  -- Keyed on the constructor's own profile only (`p`), not the top-level sample, which also reflects
  -- misconfiguration elsewhere in the closure that no choice of plan here can cause or fix.
  | ran _ s p =>
    if p.interpErrors > 0 then (1, 0, 0)
    else
      let discardPerMille := if p.attempts == 0 then 1000 else p.discards * 1000 / p.attempts
      (0, discardPerMille, 100000 - min 100000 s.avgOutputSizeCenti)
  | unrunnable .. => (1, 0, 0)
  | rejected _ => (2, 0, 0)

/-- Lexicographic comparison on `rank`. -/
def better (a b : PlanOutcome) : Bool :=
  let (a₁, a₂, a₃) := a.rank
  let (b₁, b₂, b₃) := b.rank
  if a₁ != b₁ then a₁ < b₁ else if a₂ != b₂ then a₂ < b₂ else a₃ < b₃

end PlanOutcome

/-- Measures one plan: lower it, bring up whatever modes its schedule calls, sample it from the top,
    and profile where its own schedule discards.

    Returns the outcome together with the premises the discards are attributed to, heaviest first —
    the input a mutation needs to be aimed at something rather than random. -/
def InterpEnv.measurePlan (env : InterpEnv) (specs : List RelSpec) (rel : RelSpec) (key : SpecKey)
    (c : CtorSpec) (plan : Plan) (size : Nat) (inputs : List Val := []) (n : Nat := 200)
    (limit : Nat := 24) : IO (PlanOutcome × List (Nat × Nat)) := do
  match rescheduleLowered rel key c plan with
  | .error e => return (.rejected e.message, [])
  | .ok low =>
    -- Both kinds of dependency, and checkers enabled. A sweep exists to vary *polarity*: the whole
    -- point of moving a premise later is that it stops producing and becomes a `Check`. So a plan
    -- routinely needs a **checker** for a relation this environment only has a generator for, and
    -- `stepDepKey?` reports producer dependencies only. Without `stepCheckKey?` and `deriveCheckers`
    -- every demoting plan comes back `unrunnable` — which is not a fact about the plan, it is the
    -- sweep failing to bring up what the plan asked for.
    let deps := key :: low.schedule.1.filterMap stepDepKey?
      ++ low.schedule.1.filterMap stepCheckKey?
    match env.deriveClosure specs deps limit (deriveCheckers := true) with
    | .error e => return (.unrunnable low.schedule e, [])
    | .ok closedRaw =>
      -- Publish the derived checkers before validating, as `learnSchedules` does: a generator's `Check`
      -- reads only name-keyed leaves, so a plan that demotes a premise to a check whose only checker is
      -- one this closure derived would otherwise fail every attempt and be measured as all discards.
      let closed := closedRaw.publishInterpretedCheckers
      match closed.withCtorSchedule key c.ctorName low.schedule with
      | none => return (.unrunnable low.schedule s!"[interp] {renderSpecKey key} was not derived", [])
      | some env' =>
        match env'.validate with
        | .error report => return (.unrunnable low.schedule report, [])
        | .ok () =>
          let stats ← env'.sample key size inputs n 1
          let prof ← env'.profileCtor key c.ctorName size inputs n
          return (.ran low.schedule stats prof, low.blame prof.stepCounts)

/-- Sweeps the candidate plans for one constructor: re-derive its schedule for each plan, bring up
    whatever modes that schedule needs, and measure.

    `specs` are the relations available to derive from — the same list `InterpEnv.deriveClosure`
    takes. `env` supplies the leaves (unconstrained generators, checkers, functions); the schedules
    are derived here rather than read out of it, so a plan asking for `BST[1,2]` gets it.

    Ranked best-first, but every candidate is reported, including the ones that never became a
    schedule: knowing an ordering is impossible is as useful as knowing another is slow. -/
def InterpEnv.sweepPlans (env : InterpEnv) (specs : List RelSpec) (rel : RelSpec) (key : SpecKey)
    (ctorName : Name) (size : Nat) (inputs : List Val := []) (n : Nat := 200)
    (limit : Nat := 24) : IO (List (Plan × PlanOutcome)) := do
  let some ctor := rel.ctors.find? (fun c => c.ctorName == ctorName)
    | throw (IO.userError s!"[interp] '{rel.inductiveName}' has no constructor '{ctorName}'")
  let mut results := []
  for (plan, _) in plansOf rel key ctor limit do
    let (outcome, _) ← env.measurePlan specs rel key ctor plan size inputs n limit
    results := results ++ [(plan, outcome)]
  return sortBy (fun (_, a) (_, b) => a.better b) results

/-- Renders a plan sweep, best first. -/
def renderPlanSweep (ctor : CtorSpec) (results : List (Plan × PlanOutcome)) : String :=
  let rows := results.zipIdx.map (fun ((plan, outcome), i) =>
    let head := s!"#{i + 1}  {ppPlan ctor plan}"
    match outcome with
    | .rejected reason => s!"{head}\n    ✗ not a schedule: {reason}"
    | .unrunnable sched report =>
      s!"{head}\n{ppScheduleSteps sched.1}\n    ✗ cannot run here: {report}"
    | .ran sched stats prof =>
      s!"{head}  {stats.renderLine}\n{renderProfile prof}\n{ppScheduleSteps sched.1}")
  s!"[interp] {ctor.ctorName}: {results.length} plan(s), best first:\n"
    ++ "\n\n".intercalate rows

/-! ## Discard-guided tuning

    Put the profiler and the mutation operators together and you get a hill-climb: measure, blame the
    premise that discarded most, mutate around it, keep the mutation that measures better, repeat.

    This is a local search over plans, not a replacement for the compile-time schedule search. It has
    the advantage of measuring the real discard behaviour instead of predicting it from a static
    score, and the limitation of every hill-climb: it stops at a local optimum, and it costs `n`
    samples per candidate. -/

/-- One step of the search, kept for the report. -/
structure TuneStep where
  /-- Round number, starting at 0 for the initial plan. -/
  round : Nat
  /-- The plan measured. -/
  plan : Plan
  /-- What it scored, or why it could not be measured. -/
  outcome : PlanOutcome
  /-- Premises blamed for discards, heaviest first, as `(premise index, discards)`. -/
  blamed : List (Nat × Nat)
  /-- Whether this became the new incumbent. -/
  accepted : Bool

/-- Hill-climbs on plans, guided by which premise the discards are attributed to.

    Each round: measure the incumbent, blame the premises that discarded most, try the mutations
    `mutationsFor` proposes around them, and adopt the best one that beats the incumbent. Stops when
    no mutation improves, or after `rounds` rounds.

    Returns the winning plan and the full trace, because the trace is where the insight is: which
    premise was the bottleneck, and what moving it did. -/
def InterpEnv.tunePlan (env : InterpEnv) (specs : List RelSpec) (rel : RelSpec) (key : SpecKey)
    (ctorName : Name) (size : Nat) (inputs : List Val := []) (n : Nat := 200) (rounds : Nat := 4)
    (start : Option Plan := none) (limit : Nat := 24) : IO (Plan × List TuneStep) := do
  let some c := rel.ctors.find? (fun k => k.ctorName == ctorName)
    | throw (IO.userError s!"[interp] '{rel.inductiveName}' has no constructor '{ctorName}'")
  let mut plan := start.getD ((List.range c.hypotheses.length).map PlanStep.use)
  let mut (best, blamed) ← env.measurePlan specs rel key c plan size inputs n limit
  let mut trace := [{ round := 0, plan := plan, outcome := best, blamed := blamed,
                      accepted := true : TuneStep }]
  for round in List.range rounds do
    -- Aim the mutations at the premises that actually discarded; a premise blamed for nothing has
    -- nothing to fix.
    let candidates := mutationsFor c plan
      (blamed.filterMap (fun (i, d) => if d == 0 then none else some i))
    let mut improved := false
    for cand in candidates do
      let (outcome, blamed') ← env.measurePlan specs rel key c cand size inputs n limit
      let accept := outcome.better best
      trace := trace ++ [{ round := round + 1, plan := cand, outcome := outcome,
                           blamed := blamed', accepted := accept }]
      if accept then
        best := outcome
        blamed := blamed'
        plan := cand
        improved := true
    if !improved then break
  return (plan, trace)

/-- Renders a tuning trace: every candidate, what it scored, and which premise it was aimed at. -/
def renderTune (c : CtorSpec) (trace : List TuneStep) : String :=
  let blameStr := fun (bs : List (Nat × Nat)) =>
    if bs.isEmpty then "" else
      "  ← discards: " ++ ", ".intercalate (bs.filterMap (fun (i, d) =>
        if d == 0 then none else
          some s!"{(c.hypotheses[i]?).elim s!"#{i}" ppHypothesisExpr} ×{d}"))
  let rows := trace.map (fun t =>
    let mark := if t.accepted then "✔" else " "
    let score :=
      match t.outcome with
      | .ran _ s p =>
        let dis := if p.attempts == 0 then 0 else p.discards * 100 / p.attempts
        s!"discards {dis}% ({p.discards}/{p.attempts}) · {s.renderLine}"
      | .unrunnable _ _ => "cannot run here"
      | .rejected r => s!"not a schedule: {r}"
    s!"{mark} r{t.round}  {score}\n      {ppPlan c t.plan}{blameStr t.blamed}")
  s!"[interp] tuning {c.ctorName}:\n" ++ "\n".intercalate rows

/-- Validation report plus a sample summary: the first thing to run on a new environment. -/
def InterpEnv.report (env : InterpEnv) (key : SpecKey) (size : Nat) (inputs : List Val := [])
    (n : Nat := 200) : IO String := do
  match env.validate with
  | .error report => return report
  | .ok () => do
    let stats ← env.sample key size inputs n
    return env.checkReport ++ "\n" ++ stats.render

end Specimen.Interp
