import Specimen.Interp.Learn
import Specimen.Interp.Dataflow

/-!
# Learning premise orders by following blame

The pipeline this serves: start from the premise orders the compile-time deriver settled on, measure where
the generator loses attempts, change only the orders that measurement blames, and report — as pins — only
the changes that measurably improve coverage.

**Moves are anchor moves only.** An anchor of premise `i` is a premise sharing a value variable with it,
and `Plan.anchorMoves` gives every relocation of `i` among its anchors, before and after. Every other
reordering lowers to one of these schedules, and none of them inserts an `inst`, so every candidate can be
pinned. (The earlier generator proposed mostly `inst` insertions: on Cedar 146 of 209 candidates could not
be pinned.)

**Blame follows a chain, nearest cause first.** A step rejects on values it read. Level 0 is the premise
that emitted the rejecting step; level `k + 1` are the premises that produced what level `k` read
(`Dataflow.chainOf`, over the provenance recorded at lowering). When a rejection was decided by the mode's
*inputs* — its reads were all input-determined, or the callee could apply no constructor to them
(`noApplyError`) — the local chain cannot fix it, and blame goes up to the callers' call sites, whose own
order decides what those inputs are (and may change which mode gets called).

**Acceptance is by measured coverage; wasted work is only a tie-break.** Every candidate at a level is
screened; the best is kept if it beats the incumbent by a margin at least the incumbent's own seed-to-seed
spread, and is then re-measured on seeds it was not chosen on (`confirmSeeds`). Failing that, a candidate
that loses no paths on either seed set and cuts rejections by at least `tieBreakCut` percent on both is
kept as a tie-break. Rejections, not wall-clock: they are deterministic under a seed, and a move of a
premise that draws nothing (a `Check`, an enumeration) changes nothing else.

Blame is read from the **root sample's** retry log, so it reflects the input distribution the generator
actually sees, and costs no per-mode profile.

**Why a blamed move usually cannot change coverage.** `Gen` is `StateT StdGen` over `Except`, so a caught
failure restores the generator state the branch started from: a rejected branch leaves no trace in the
random stream. The values a seed produces are therefore fixed by the draws of the *successful* run alone,
and any move that keeps those draws in the same order — relocating a `Check`, or an enumeration, which
draws nothing — produces the same values and only changes how much work is thrown away. On Cedar's
`HasType[0,4]` every blamed candidate (17, all installed) gave the incumbent's samples exactly, with
rejection counts differing by at most 2% and no consistent direction over 800 samples. Coverage moves
are the ones that change what the successful run draws: which premise *produces* a variable rather than
checks it, or which mode a call site selects. The same holds for the compiled generator, which runs in
the same `Gen`.
-/

open Lean Schedules

namespace Specimen.Interp

/-- Whether a blamed rejection was decided inside the constructor, or by the inputs it was given. -/
inductive BlameKind where
  | internal
  | onInputs
  deriving Repr, BEq, Inhabited

/-- A premise the retry log blames, with how many rejections and of which kind. -/
structure ChainTarget where
  key : SpecKey
  ctorName : Name
  premise : Nat
  count : Nat
  kind : BlameKind
  deriving Repr, Inhabited

def ChainTarget.render (t : ChainTarget) : String :=
  s!"{renderSpecKey t.key} · {t.ctorName} · premise {t.premise} ({t.count}×{if t.kind == .onInputs then ", on inputs" else ""})"

/-- The closure mode a step calls, if the closure interprets it. An instantiated mode is matched on its
    relation, outputs and sort when the step's key carries no instantiation. -/
def InterpEnv.calleeKey? (env : InterpEnv) (st : ScheduleStep) : Option SpecKey :=
  match st with
  | .SuchThat _ (.Rec f _) _ | .SuchThat _ (.MutRec f _) _
  | .Unconstrained _ (.Rec f _) _ | .Unconstrained _ (.MutRec f _) _ => env.keyOfFn? f
  | _ =>
    match stepDepKey? st with
    | some k =>
      if (env.relations[k]?).isSome then some k
      else (env.relations.toList.find? (fun (k', _) =>
        k'.inductiveName == k.inductiveName && k'.outputIndices == k.outputIndices
          && k'.deriveSort == k.deriveSort)).map (·.1)
    | none => none

/-- Every generator step in the closure that calls `callee`: `(mode, constructor, step index)`. -/
def InterpEnv.callSitesOf (env : InterpEnv) (callee : SpecKey) : List (SpecKey × Name × Nat) :=
  env.relations.toList.flatMap (fun (k, rs) =>
    if k.deriveSort != .Generator then []
    else rs.allSchedules.flatMap (fun (c, (steps, _)) =>
      steps.zipIdx.filterMap (fun (st, i) =>
        if env.calleeKey? st == some callee then some (k, c, i) else none)))

/-- The premises the root sample's retry log blames, heaviest first.

    * A prologue step (no recorded origin) is dispatch — the constructor not applying — and is dropped.
    * A call to a mode the closure interprets is blamed only for its `noApply` share (the callee could
      apply nothing to what was passed, which is this call's doing); the rest is already counted inside the
      callee, at the steps that actually rejected.
    * A call to a leaf producer is blamed in full.
    * A `Match` or `Check` is blamed in full, as `onInputs` when everything it read was fixed by the inputs.
    * A step emitted by an `inst` is not a premise, and cannot be moved.

    With `focus := some ind`, only modes of `ind` are blamed, and a call to an interpreted mode is blamed
    **in full**. That is the structural reading: `ind` is the relation whose derivations are the output,
    so an abandoned constructor of it is a shape the output lost — whatever the callee did inside —
    while retries inside auxiliary relations cost only time, since a failed branch rolls the random state
    back. Without a focus, blame follows rejections wherever they happen, which on Cedar ranked inner
    map walks (`MapContainsPairKey`) first and found nothing a move could improve. -/
def InterpEnv.rootCausesOf (env : InterpEnv) (log : RetryLog) (focus : Option Name := none)
    (minEntries : Nat := 5) : List ChainTarget :=
  let raw : List ChainTarget := log.byStep.toList.filterMap (fun ((k, c, i), n) => do
    if let some ind := focus then
      if k.inductiveName != ind then none
    let rs ← env.relations[k]?
    let prov ← rs.provenanceOf? c
    let (steps, _) ← rs.ctorSchedule? c
    let st ← steps[i]?
    let origin ← (prov.origins[i]?).bind id
    let premise ← match origin with
      | .use p => some p
      | .inst _ => none
    let noApply := log.byStepNoApply.getD (k, c, i) 0
    match st with
    | .SuchThat .. | .Unconstrained .. =>
      match env.calleeKey? st with
      | some _ =>
        if focus.isSome then
          some { key := k, ctorName := c, premise, count := n,
                 kind := if noApply > 0 then .onInputs else .internal }
        else if noApply > 0 then some { key := k, ctorName := c, premise, count := noApply, kind := .onInputs }
        else none
      | none => some { key := k, ctorName := c, premise, count := n, kind := .internal }
    | _ =>
      some { key := k, ctorName := c, premise, count := n,
             kind := if Dataflow.failsOnInputs rs.inputNames steps i then .onInputs else .internal })
  let merged := raw.foldl (fun (acc : List ChainTarget) t =>
    match acc.find? (fun u => u.key == t.key && u.ctorName == t.ctorName && u.premise == t.premise
        && u.kind == t.kind) with
    | some _ => acc.map (fun u =>
        if u.key == t.key && u.ctorName == t.ctorName && u.premise == t.premise && u.kind == t.kind then
          { u with count := u.count + t.count } else u)
    | none => acc ++ [t]) []
  match focus with
  | none => merged.mergeSort (fun a b => b.count ≤ a.count)
  | some _ =>
    -- A constructor that almost never succeeds loses its whole shape every time it is picked, however
    -- rarely that is; ranking by raw count put the frequent constructors first and never reached
    -- `binaryAppContains` (entered ~14 times in 50 samples, 2 successes — every failure at its set operand).
    -- So: failure rate of the constructor first, count second, and too few entries to judge are skipped.
    let failRate := fun (t : ChainTarget) =>
      let r := log.byCtor.getD (t.key, t.ctorName) {}
      if r.attempts == 0 then 0 else r.failures * 1000 / r.attempts
    let enough := fun (t : ChainTarget) => (log.byCtor.getD (t.key, t.ctorName) {}).attempts ≥ minEntries
    (merged.filter enough).mergeSort (fun a b =>
      failRate b < failRate a || (failRate b == failRate a && b.count ≤ a.count))

/-- The candidate plans at one level: every anchor move of every premise in the level, applied to the
    installed plan's bare order and repaired, deduplicated by lowered schedule and without the installed
    one. Repair can only insert `inst`s the order *forces*, so every candidate can be pinned. -/
def levelCandidates (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (installed : Plan) (level : List Nat) :
    List (Plan × Schedule) :=
  let bare : Plan := installed.filter (fun st => match st with | .use _ => true | .inst _ => false)
  let installedSteps := match repair rel key c installed with
    | .ok (_, s) => some s.1
    | .error _ => none
  let moves := level.flatMap (fun i => Plan.anchorMoves c bare i)
  moves.foldl (fun (acc : List (Plan × Schedule)) p =>
    match repair rel key c p with
    | .ok (p', sched) =>
      if installedSteps == some sched.1 || acc.any (fun (_, s) => s.1 == sched.1) then acc
      else acc ++ [(p', sched)]
    | .error _ => acc) []

/-- One measurement of a book: the closure it builds, sampled from the root with `noApply` attribution on,
    and the retry log that sampling produced. -/
structure BookMeasure where
  env : InterpEnv
  stats : RunStats
  log : RetryLog

/-- Every rejection the sampling recorded, at any step of any mode. A move of a premise that draws nothing
    (a `Check`, an enumeration) leaves the values generated — and so the paths — unchanged, and shows up
    only here. -/
def BookMeasure.rejections (m : BookMeasure) : Nat :=
  m.log.byStep.fold (fun acc _ n => acc + n) 0

/-- Whether the closure a measurement built installed `plan` for `(key, ctorName)`. Checked on every
    candidate, because the failure it guards against is silent: a booked plan that the closure does not use
    measures the incumbent again, and every candidate ties. -/
def BookMeasure.installs (m : BookMeasure) (key : SpecKey) (ctorName : Name) (plan : Plan) : Bool :=
  ((m.env.relations[key]?).bind (·.provenanceOf? ctorName)).map (·.plan) == some plan

/-- Builds and samples a book as it would ship: `prepare` gives the closure the compiled weights and
    leaves, and derived checkers are published before validating, as `learnSchedules` does.

    `moreInputs` are further root inputs, sampled like `inputs` and pooled into the same stats and log.
    Constructors that only apply at one requested value — `andTtTt` concludes at `bool tt`, so a root
    that only ever asks for `bool anyBool` never exercises it — are invisible to a single input, and so is
    anything a schedule change does to them. -/
def InterpEnv.measureBook (leaves : InterpEnv) (specs : List RelSpec) (rootKey : SpecKey)
    (book : PlanBook) (prepare : InterpEnv → InterpEnv) (size : Nat) (inputs : List Val) (n : Nat)
    (seeds : List Nat) (limit fuel : Nat) (moreInputs : List (List Val) := []) :
    IO (Except String BookMeasure) := do
  match leaves.deriveClosureWith specs [rootKey] book limit fuel (deriveCheckers := true) with
  | .error e => return .error e
  | .ok raw =>
    let env := { (prepare raw).publishInterpretedCheckers with attributeNoApply := true }
    match env.validate with
    | .error r => return .error r
    | .ok () =>
      let (st, log) ← withRetryLog do
        let mut acc : RunStats := {}
        for ins in inputs :: moreInputs do
          for s in seeds do
            acc := acc.merge (← env.sample rootKey size ins n 0 (some s))
        return acc
      return .ok { env, stats := st, log }

/-- One decision of `learnByBlame`, for the report. -/
structure BlameStep where
  round : Nat
  target : String
  level : String
  /-- The mode and constructor whose order the candidate changes — the target's own, or a caller's. -/
  site : String := ""
  plan : Option Plan := none
  /-- Distinct k-paths of the candidate on the screening seeds, and of the incumbent. -/
  paths : Option Nat := none
  incumbentPaths : Option Nat := none
  /-- Rejections recorded while screening, of the candidate and of the incumbent. -/
  rejections : Option Nat := none
  incumbentRejections : Option Nat := none
  accepted : Bool := false
  note : String := ""
  deriving Inhabited

/-- A trace entry. A function rather than record syntax at each site: a structure instance's fields are
    column-sensitive, and these are long enough to need wrapping. -/
def mkStep (round : Nat) (target level : String) (site : String := "") (plan : Option Plan := none)
    (paths : Option Nat := none) (incumbentPaths : Option Nat := none) (rejections : Option Nat := none)
    (incumbentRejections : Option Nat := none) (accepted : Bool := false) (note : String := "") :
    BlameStep :=
  { round, target, level, site, plan, paths, incumbentPaths, rejections, incumbentRejections, accepted,
    note }

/-- A plan as the premise order it pins, with generated-blind variables marked. -/
def renderPlan (p : Plan) : String :=
  "[" ++ ", ".intercalate (p.map (fun st => match st with
    | .use i => toString i
    | .inst v => s!"inst {v}")) ++ "]"

def BlameStep.render (t : BlameStep) : String :=
  let mark := if t.accepted then "✔" else " "
  let score := match t.paths, t.incumbentPaths with
    | some p, some q => s!" → {p} paths (incumbent {q})"
    | _, _ => ""
  let rej := match t.rejections, t.incumbentRejections with
    | some r, some q => s!", {r} rejections (incumbent {q})"
    | _, _ => ""
  let move := match t.plan with
    | some p => s!"\n      {t.site} ← {renderPlan p}"
    | none => ""
  s!"{mark} r{t.round} [{t.level}] {t.target}{score}{rej}{if t.note.isEmpty then "" else s!" · {t.note}"}{move}"

/-- Learns premise orders by following blame from a start book (typically `DeriverChoice.generatorBook`).
    Returns the learned book and a trace of every decision. See the module docstring for the method.

    `prepareFor book` gives the closure for `book` what the compiled generator for it would have — its
    weights, above all. The weights are a function of the schedule (the scorer's badness of each
    constructor's schedule), so a candidate that changes an order can change its own constructor's weight,
    and measuring it under the start's weights measures a generator `derive_mutual` would never emit. On
    Cedar, pinning `ValidEntityUID.enum ← [1,0]` moves that constructor's badness from 727 to 1000. A
    caller that can re-derive (`deriveChoice` under the book's pins) passes that here, in its own monad;
    each distinct book is prepared once. The default applies `prepare` to every book. -/
def InterpEnv.learnByBlame {m : Type → Type} [Monad m] [MonadLiftT IO m] (leaves : InterpEnv)
    (specs : List RelSpec) (rootKey : SpecKey) (size : Nat)
    (inputs : List Val) (start : PlanBook) (prepare : InterpEnv → InterpEnv := id)
    (prepareFor : PlanBook → m (InterpEnv → InterpEnv) := fun _ => pure prepare)
    (moreInputs : List (List Val) := []) (focus : Option Name := none) (n : Nat := 40)
    (confirmN : Option Nat := none)
    (screenSeeds : List Nat := [11, 2029, 90210]) (confirmSeeds : List Nat := [7, 4242, 31337])
    (rounds : Nat := 4) (targetsPerRound : Nat := 4) (maxMeasurements : Nat := 200) (upWidth : Nat := 2)
    (tieBreakCut : Nat := 20) (limit : Nat := 24) (fuel : Nat := 400) : m (PlanBook × List BlameStep) := do
  -- Screening uses the start's weights, which is cheap; the one candidate a level keeps is confirmed
  -- under its own (`prepareFor`), since a changed order can change its constructor's weight.
  let screen := fun (b : PlanBook) (seeds : List Nat) =>
    (leaves.measureBook specs rootKey b prepare size inputs n seeds limit fuel moreInputs : IO _)
  -- Confirmation is the decision, so it gets the larger sample: on Cedar at size 12, 180 samples per
  -- measurement put the incumbent 8 paths apart between seed sets and let a move through that lost 17–35
  -- paths on 720 fresh samples, where the incumbent itself was stable to 2.
  let nC := confirmN.getD n
  let measure := fun (b : PlanBook) (seeds : List Nat) => do
    let prep ← prepareFor b
    (leaves.measureBook specs rootKey b prep size inputs nC seeds limit fuel moreInputs : IO _)
  let mut book := start
  let mut trace : List BlameStep := []
  let .ok inc0 ← screen book screenSeeds
    | return (book, [mkStep 0 "start" "" (note := "the start book does not build")])
  let .ok incC0 ← measure book confirmSeeds
    | return (book, [mkStep 0 "start" "" (note := "the start book does not build")])
  -- The incumbent at confirmation size on the screening seeds too: its spread against `incC0` is the
  -- noise a confirmed gain has to clear.
  let .ok incS0 ← measure book screenSeeds
    | return (book, [mkStep 0 "start" "" (note := "the start book does not build")])
  let mut inc := inc0
  let mut incConfirm := incC0.stats.coverage
  let mut incConfirmRej := incC0.rejections
  -- `r` cuts `r₀` by the tie-break percentage.
  let cuts := fun (r r₀ : Nat) => r * 100 ≤ r₀ * (100 - tieBreakCut) && r < r₀
  -- The incumbent's own spread across seed sets: a gain smaller than this is indistinguishable from noise.
  let noise := (Int.natAbs ((incS0.stats.coverage : Int) - (incC0.stats.coverage : Int)))
  let margin := max 2 (noise + 1)
  let mut measurements := 3
  let mut irreducible : List (SpecKey × Name × Nat) := []
  trace := trace ++ [mkStep 0 "start" "" (paths := some inc.stats.coverage)
    (incumbentPaths := some incConfirm) (rejections := some inc.rejections)
    (incumbentRejections := some incC0.rejections)
    (note := s!"screen {inc.stats.coverage} at n={n} · confirm-size {incS0.stats.coverage}/{incConfirm} at n={nC} · margin {margin}")]
  for round in List.range rounds do
    let targets := (inc.env.rootCausesOf inc.log focus).filter (fun t =>
      !irreducible.contains (t.key, t.ctorName, t.premise)) |>.take targetsPerRound
    if targets.isEmpty then
      trace := trace ++ [mkStep (round + 1) "—" "" (note := "nothing left to blame")]
      break
    let mut improved := false
    for t in targets do
      if improved || measurements ≥ maxMeasurements then break
      let some rel := specs.find? (·.inductiveName == t.key.inductiveName) | continue
      let some c := rel.ctors.find? (·.ctorName == t.ctorName) | continue
      let some rs := inc.env.relations[t.key]? | continue
      let some prov := rs.provenanceOf? t.ctorName | continue
      let some (steps, _) := rs.ctorSchedule? t.ctorName | continue
      let chain := Dataflow.chainOf rs.inputNames steps prov.origins c t.premise
      -- Local levels first, then the callers — which may choose different inputs, or a different mode.
      let local_ : List (String × SpecKey × Name × List Nat) :=
        chain.levels.zipIdx.map (fun (l, d) =>
          (if d == 0 then "own" else s!"producer {d}", t.key, t.ctorName, l))
      let up : List (String × SpecKey × Name × List Nat) :=
        if t.kind == .onInputs || chain.readsInputs then
          (inc.env.callSitesOf t.key).take upWidth |>.filterMap (fun (k', c', i) => do
            let rs' ← inc.env.relations[k']?
            let prov' ← rs'.provenanceOf? c'
            match (prov'.origins[i]?).bind id with
            | some (.use p) => some ("caller", k', c', [p])
            | _ => none)
        else []
      for (label, k, cn, lvl) in local_ ++ up do
        if improved || measurements ≥ maxMeasurements then break
        let some relL := specs.find? (·.inductiveName == k.inductiveName) | continue
        let some cL := relL.ctors.find? (·.ctorName == cn) | continue
        let some rsL := inc.env.relations[k]? | continue
        let some provL := rsL.provenanceOf? cn | continue
        let cands := levelCandidates relL k cL provL.plan lvl
        -- Screen every candidate at this level, keep the best.
        let mut best : Option (Plan × BookMeasure) := none
        for (plan, _) in cands do
          if measurements ≥ maxMeasurements then break
          measurements := measurements + 1
          let site := s!"{renderSpecKey k} · {cn}"
          match ← screen (book.set k cn plan) screenSeeds with
          | .error e =>
            trace := trace ++ [mkStep (round + 1) t.render label site (plan := some plan)
              (note := s!"does not build: {e.take 160}")]
          | .ok m =>
            if !m.installs k cn plan then
              trace := trace ++ [mkStep (round + 1) t.render label site (plan := some plan)
                (note := "booked but not installed — measured the incumbent again; skipped")]
              continue
            trace := trace ++ [mkStep (round + 1) t.render label site (plan := some plan)
              (paths := some m.stats.coverage) (incumbentPaths := some inc.stats.coverage)
              (rejections := some m.rejections) (incumbentRejections := some inc.rejections)]
            let better := match best with
              | none => true
              | some (_, b) => m.stats.coverage > b.stats.coverage
                  || (m.stats.coverage == b.stats.coverage && m.rejections < b.rejections)
            if better then best := some (plan, m)
        let some (plan, m) := best | continue
        let gain := (m.stats.coverage : Int) - (inc.stats.coverage : Int)
        let tieBreak := gain ≥ 0 && cuts m.rejections inc.rejections
        -- Screening only selects; the confirmation below, at the larger sample, decides.
        if gain ≤ 0 && !tieBreak then continue
        -- Confirm on seeds the choice was not made on, against the incumbent on the same seeds.
        measurements := measurements + 1
        let .ok mc ← measure (book.set k cn plan) confirmSeeds | continue
        let confirmGain := (mc.stats.coverage : Int) - (incConfirm : Int)
        let keeps := keepsRepeatedPaths ({ root := m.stats } : ClosureStats) ({ root := inc.stats } : ClosureStats)
        let byCoverage := confirmGain ≥ margin
        let byTieBreak := tieBreak && confirmGain ≥ 0 && cuts mc.rejections incConfirmRej
        let accept := (byCoverage || byTieBreak) && keeps && m.stats.interpErrors ≤ inc.stats.interpErrors
        trace := trace ++ [mkStep (round + 1) t.render label s!"{renderSpecKey k} · {cn}" (plan := some plan)
          (paths := some mc.stats.coverage) (incumbentPaths := some incConfirm)
          (rejections := some mc.rejections) (incumbentRejections := some incConfirmRej) (accepted := accept)
          (note := s!"confirm{if byCoverage then " (coverage)" else if byTieBreak then " (tie-break: fewer rejections)" else ""}: \
            {mc.stats.coverage} vs {incConfirm} (screen +{gain}, margin {margin})")]
        if accept then
          book := book.set k cn plan
          inc := m
          incConfirm := mc.stats.coverage
          incConfirmRej := mc.rejections
          improved := true
      if !improved then irreducible := irreducible ++ [(t.key, t.ctorName, t.premise)]
    if !improved then
      trace := trace ++ [mkStep (round + 1) "—" "" (note := "no target improved")]
      break
  return (book, trace)

end Specimen.Interp
