import Specimen.Scoring

/-!
# `Scoring.InversionAwareScore`

`BudgetAwareScore` with one more term, `inversion`, ranked with `selectivity` (above `density`): a
generator's schedule that produces a value elsewhere — a free draw, or another relation — and then
makes the relation being derived hit it exactly, or checks it with a relation that could have
produced it.

The common case is capabilities: `iteTt`, under `BudgetAwareScore`, draws `c₁` from `CapMerge` and
then asks the recursive call for an `x₁` whose capabilities are exactly `c₁`, rather than producing
`x₁` and `c₁` together and merging forward. Under a free draw that has no meaningful generator (an
`Expr`, a `Key`) such a schedule never succeeds, and it needs a mode of the relation with that output
as an input, which the forward schedule does not.

Like `selectivity`, the term corrects `density`, which rewards the free producer; unlike it, the
right producer is not a finite pin but a call of the relation itself. It is not part of `badness`,
so a constructor with no other schedule keeps its weight.

The bundle searches without pruning (`PruneStrategy.noPruning`): the search tree scores orderings of
a subset of the premises, and with multi-output steps adding a premise can change what an earlier
one produces — `restTt`'s recursive call produces `tyNext` and `cr` until `GetAttrOn` is placed before
it — so a bound on a subset is not a bound on its extensions.
-/

namespace Scoring

open Lean Meta Schedules

structure InversionAwareScore where
  base : BudgetAwareScore := {}
  inversion : Nat := 0
  deriving Repr, BEq, Inhabited

deriving instance TypeName for InversionAwareScore

instance : Ord InversionAwareScore where
  compare a b :=
    (compare (a.base.selectivity + a.inversion) (b.base.selectivity + b.inversion)).then
      (compare a.base b.base)

instance : LT InversionAwareScore := ltOfOrd

instance : Scorable InversionAwareScore where
  empty := {}
  combine a b := { base := Scorable.combine a.base b.base, inversion := a.inversion + b.inversion }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { base := Scorable.uncoveredPenalty }
  worst := { base := Scorable.worst, inversion := 100 }
  badness s := Scorable.badness s.base

/-- The inversions of a generator schedule (see the module docstring). -/
def inversionOf (key : SpecKey) (steps : List ScheduleStep) : Nat := Id.run do
  if key.deriveSort != .Generator then return 0
  let selfCall (src : Source) : Option (List ConstructorExpr) := match src with
    | .NonRec (relName, args) => if relName == key.inductiveName then some args else none
    | .Rec n args | .MutRec n args => if n == key.inductiveName then some args else none
  let mut produced : Std.HashSet Name := {}
  let mut fromSelf : Std.HashSet Name := {}
  let mut inversion := 0
  for step in steps do
    let src? : Option Source := match step with
      | .SuchThat _ src _ => some src | .Check src _ => some src | _ => none
    if let some src := src? then
      -- handed to a call of this relation at an argument this mode outputs
      if let some args := selfCall src then
        for p in key.outputIndices do
          match args[p]? with
          | some (.Unknown v) =>
            if produced.contains v && !fromSelf.contains v then inversion := inversion + 1
          | _ => pure ()
    -- checked by another relation, which could have produced it
    if let .Check (.NonRec (relName, args)) _ := step then
      if relName != key.inductiveName then
        if (args.flatMap varsInConstructorExpr).any (fun v => produced.contains v && !fromSelf.contains v) then
          inversion := inversion + 1
    match step with
    | .Unconstrained n _ _ => produced := produced.insert n
    | .SuchThat outputs src _ =>
      for (n, _) in outputs do
        produced := produced.insert n
        if (selfCall src).isSome then fromSelf := fromSelf.insert n
    | _ => pure ()
  return inversion

private def argsOf : Source → List ConstructorExpr
  | .NonRec (_, args) | .Rec _ args | .MutRec _ args => args

private def generatedVarDeps (inputVars : Std.HashSet Name) (src : Source) : Nat :=
  (argsOf src |>.flatMap varsInConstructorExpr).filter (!inputVars.contains ·) |>.length

private def localityOf (key : SpecKey) (src : Source) : CallLocality :=
  match src with
  | .Rec .. | .MutRec .. => .Internal
  | .NonRec (indName, _) => if indName == key.inductiveName then .SameIndExt else .External

/-- A dependency mode's `BudgetAwareScore` terms, if they are to be trusted: `none` for a mode in
progress or not yet derived, and, in bound mode, for a cycle-dependent one. The read is recorded for
the provenance of the derivation running now. -/
def depBase (memo : Std.HashMap SpecKey MemoEntry) (k : SpecKey) : MetaM (Option BudgetAwareScore) := do
  let provisional ← recordMemoRead memo k
  let bound ← (memoBoundMode.get : IO Bool)
  match memo[k]? with
  | some (.done s) =>
    if provisional && bound then return none
    return some (Score.unwrap InversionAwareScore s.score).base
  | _ => return none

/-- `BudgetAwareScore`'s step scorer, reading the dependencies through `depBase`, with an unknown
dependency taken at its best (`Total`, no fabrication): a lower bound for whatever it is derived to. -/
def inversionAwareStepScorer : StepScorer InversionAwareScore := fun key memo inputVars step => do
  let isChecker := key.deriveSort == .Checker || key.deriveSort == .Enumerator
  match step with
  | .Unconstrained _ src _ =>
    return { base := { density := .Total, locality := localityOf key src,
                       fabrication := if isChecker then 1 else 0 } }
  | .Match .. => return { base := { density := .Backtracking } }
  | .Check src _ =>
    let varDeps := generatedVarDeps inputVars src
    let inputDeps := if varDeps > 0 then
      (argsOf src |>.flatMap varsInConstructorExpr).filter inputVars.contains |>.length
    else 0
    return { base := { density := .Checking, locality := localityOf key src, varDeps := varDeps,
                       inputCheckDeps := inputDeps } }
  | .SuchThat outputs src _ =>
    let outputNames := Std.HashSet.ofList (outputs.map (·.1))
    let varDeps := generatedVarDeps (inputVars.union outputNames) src
    let outputIdxs : List Nat := match src with
      | .NonRec (_, args) => outputs.filterMap fun (n, _) =>
          args.findIdx? fun a => match a with | .Unknown v => v == n | _ => false
      | _ => []
    let depDensity : Density ← match src with
      | .Rec .. | .MutRec .. => pure .Partial
      | .NonRec (indName, _) =>
        let depKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs,
                                  deriveSort := key.deriveSort }
        if depKey == key then pure .Partial
        else pure ((← depBase memo depKey).map (·.density) |>.getD .Total)
    let producingFab : Nat ← match src with
      | .Rec .. | .MutRec .. => pure 0
      | .NonRec (indName, _) =>
        let enumKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs,
                                   deriveSort := .Enumerator }
        pure ((← depBase memo enumKey).map (·.fabrication) |>.getD 0)
    return { base := { density := depDensity, fabrication := if isChecker then producingFab else 0,
                       locality := localityOf key src, varDeps := varDeps } }

/-- The state of `InversionAwareScore`'s scorer after a prefix of a schedule: its steps' scores
folded, and what `selectivity` (`BudgetAwareScore`'s: each variable some relation of the schedule
ground-pins to a finite set, produced, but not by a relation pinning it) and `inversionOf` track. -/
structure InversionState where
  steps : InversionAwareScore := {}
  produced : Std.HashSet Name := {}
  producedFinitely : Std.HashSet Name := {}
  finitePinnable : Std.HashSet Name := {}
  fromSelf : Std.HashSet Name := {}
  inversion : Nat := 0
  deriving Inhabited

deriving instance TypeName for InversionState

/-- The state extended by one step. -/
def InversionState.push (key : SpecKey) (memo : Std.HashMap SpecKey MemoEntry) (inputVars : Std.HashSet Name)
    (st : InversionState) (step : ScheduleStep) : MetaM InversionState := do
  let mut st := { st with steps := Scorable.combine st.steps (← inversionAwareStepScorer key memo inputVars step) }
  let src? : Option Source := match step with
    | .SuchThat _ src _ => some src | .Check src _ => some src | _ => none
  -- inversions (see `inversionOf`), before the step's outputs are produced
  if key.deriveSort == .Generator then
    let selfCall (src : Source) : Option (List ConstructorExpr) := match src with
      | .NonRec (relName, args) => if relName == key.inductiveName then some args else none
      | .Rec n args | .MutRec n args => if n == key.inductiveName then some args else none
    if let some src := src? then
      if let some args := selfCall src then
        for p in key.outputIndices do
          match args[p]? with
          | some (.Unknown v) =>
            if st.produced.contains v && !st.fromSelf.contains v then st := { st with inversion := st.inversion + 1 }
          | _ => pure ()
    if let .Check (.NonRec (relName, args)) _ := step then
      if relName != key.inductiveName then
        if (args.flatMap varsInConstructorExpr).any (fun v => st.produced.contains v && !st.fromSelf.contains v) then
          st := { st with inversion := st.inversion + 1 }
    if let .SuchThat outputs src _ := step then
      if (selfCall src).isSome then
        st := { st with fromSelf := outputs.foldl (fun s (n, _) => s.insert n) st.fromSelf }
  -- selectivity
  match step with
  | .Unconstrained name _ _ => st := { st with produced := st.produced.insert name }
  | .SuchThat outputs src _ =>
    st := { st with produced := outputs.foldl (fun s (n, _) => s.insert n) st.produced }
    if let .NonRec (relName, args) := src then
      let pinned ← finitePinnedArgPositions relName
      for (n, _) in outputs do
        if pinned.any (fun i => match args[i]? with | some (.Unknown v) => v == n | _ => false) then
          st := { st with producedFinitely := st.producedFinitely.insert n }
  | _ => pure ()
  if let some (.NonRec (relName, args)) := src? then
    for i in ← finitePinnedArgPositions relName do
      if let some (.Unknown v) := args[i]? then st := { st with finitePinnable := st.finitePinnable.insert v }
  return st

/-- The score of the schedule the state is of. -/
def InversionState.finish (st : InversionState) : InversionAwareScore :=
  let selectivity := st.finitePinnable.toList.filter
    (fun v => st.produced.contains v && !st.producedFinitely.contains v) |>.length
  { base := { st.steps.base with selectivity := selectivity }, inversion := st.inversion }

def inversionAwareWholeScheduleScorer : ResolvedWholeScheduleScorer := fun key memo inputVars steps => do
  let st ← steps.foldlM (InversionState.push key memo inputVars) {}
  return Score.wrap st.finish

def inversionAwareIncremental : IncrementalScorer where
  init := Dynamic.mk ({} : InversionState)
  push key memo ins d step := do
    return Dynamic.mk (← InversionState.push key memo ins (d.get? InversionState |>.getD {}) step)
  finish d := Score.wrap (d.get? InversionState |>.getD {}).finish

initialize do
  let base := mkScorerBundle `Scoring.InversionAwareScore
    inversionAwareStepScorer (fun steps => steps.foldl Scorable.combine Scorable.empty)
    (fun ctors => match ctors with
      | [] => Scorable.uncoveredPenalty
      | _ => Scorable.bestOf (ctors.map Prod.snd))
    (fun leaves => leaves.foldl Scorable.combine Scorable.empty)
  registerScoringBundle { base with wholeScheduleScorer := some inversionAwareWholeScheduleScorer,
                                    incrementalScorer := some inversionAwareIncremental,
                                    pruneStrategy := .noPruning }

end Scoring
