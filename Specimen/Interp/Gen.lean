import Specimen.Interp.Env
import Specimen.Interp.DataflowCore

/-!
# Interpreting a schedule as a generator, at runtime

`interpRel` runs a `Schedules.Schedule` *as data*: no elaboration, no `MetaM`, no metaprogramming.
Feed it an `InterpEnv` (schedules + leaves) and it behaves like the generator `derive_mutual` would
have emitted for those schedules — so you can permute steps, reorder constructors, or swap weight
functions and see the effect immediately, without paying for another derivation.

## Fidelity to the emitted code

The emitted generator (see `mkConstrainedProducerTypeClassInstance` and
`MExp.scheduleToMExp`) has the shape

```lean
let rec aux_arb (fuel initSize size : Nat) (inputs…) :=
  match fuel with
  | 0            => throw outOfFuelError
  | fuel' + 1    =>
    match size with
    | 0          => backtrack [ (w, base₁), … ]
    | size' + 1  => backtrack [ (w, base₁), …, (w, rec₁), … ]
fun size => aux_arb <specimen.fuel> size size
```

and this module reproduces it decision for decision:

* **Bucketing.** Base constructors whose schedule contains a mutual call still consume fuel, so
  they are counted and scheduled as recursive (`RelSchedule.bucketedSchedules`).
* **Weights.** `weightFn ctor outputIndices deriveSort badness isRec (if isRec then size' else 0)
  numBase numRec numRecCalls`, with `numRecCalls = countSizeConsumingCalls`.
* **Size budget.** Every size-consuming call in a constructor's schedule receives
  `size' / numRecCalls` (plain `size'` when there is at most one).
* **Dependency fuel.** A `SuchThat`/`Check` on a *different* relation gets the full `initSize`; one
  on the *same* inductive shares the split budget. Recursive and mutual calls thread `fuel'`.
* **Failure.** A failing check or a non-matching `Match` throws `Gen.genericFailure`, which
  `backtrack` catches to try the next constructor; exhausted fuel throws `Gen.outOfFuelError`.

One place the interpreter *chooses* a reading rather than copying: in the `size = 0` branch the
emitted base-constructor bodies would reference `size'`, which is not bound there. The interpreter
passes `size' = 0`.

## Scope

This module interprets **generators**. Checkers and enumerators live in
`Specimen.Interp.CheckEnum`, which the three sorts' differing failure semantics make a separate
concern; theorem schedules are not interpreted at all. `interpRel` refuses a schedule of the wrong
sort with an explicit `[interp]` error rather than mis-running it — a checker schedule's steps assume
`Except GenError Bool` semantics, so interpreting one here would fail deep inside for an
unrelated-looking reason.

Unconstrained generators, and checkers for relations you would rather not interpret, are supplied as
leaves in the `InterpEnv` (see `Specimen.Interp.Bridge`).

## Misconfiguration vs. a schedule that just fails

`backtrack` catches *every* error to try the next branch, so a missing leaf would otherwise look
like an unproductive schedule. Two mitigations: interpreter errors are prefixed with `[interp] `,
and `InterpEnv.check` (in `Specimen.Interp.Validate`) reports every unresolvable step up front.
`runCtorOnce` runs a single constructor's schedule with no backtracking, so its errors surface
verbatim.
-/

open Lean Plausible Schedules GeneratorCombinators

namespace Specimen.Interp

/-- Prefix marking an error as interpreter *misconfiguration* (a missing leaf, an unsupported step)
    rather than an ordinary generation failure. -/
def interpErrorPrefix : String := "[interp] "

/-- A `GenError` reporting interpreter misconfiguration. -/
def interpError (msg : String) : GenError := .genError (interpErrorPrefix ++ msg)

/-- Whether a `GenError` reports interpreter misconfiguration. -/
def isInterpError : GenError → Bool
  | .genError m => interpErrorPrefix.isPrefixOf m

/-- Fails with an interpreter-misconfiguration error. -/
def throwInterp {α : Type} (msg : String) : Gen α := throw (interpError msg)

/-! ## Attributing a discard to a step

    A schedule that discards most of its attempts is the thing worth fixing, and the useful question
    is *where* it discards: a check late in the schedule throws away all the work before it, and a
    check that fails often belongs earlier — or belongs to a premise that should have produced its
    variable instead of testing it.

    So a rejection records the index of the step that caused it. The label is carried in the
    `GenError` message because `Gen` is `Except`-based and rolls its state back on `throw`, so there
    is nowhere else to put it. Attribution is per-schedule: when a sub-producer fails, `blaming`
    re-tags the failure with the *calling* step's index, so each frame reports where its own attempt
    died rather than inheriting a callee's step number. Fuel exhaustion and misconfiguration pass
    through untouched — neither is a discard. -/

/-- Prefix on a rejection that records the step index that caused it. Deliberately distinct from
    `interpErrorPrefix`, so a discard is never mistaken for a misconfiguration. -/
def rejectPrefix : String := "[interp:reject:"

/-- A rejection attributed to step `idx`, described by `desc`. -/
def rejectAt (idx : Nat) (desc : String) : GenError :=
  .genError s!"{rejectPrefix}{idx}] {desc}"

/-- Thrown by a mode none of whose constructors could apply to the inputs it was given: every branch was
    refused by a step that read only input-determined values, or dispatch left no branch at all. Definitive,
    like any failure — distinguished only so blame can go to the caller. -/
def noApplyError (key : SpecKey) : GenError :=
  .genError s!"[interp:noapply] no constructor of {renderSpecKey key} applies to its inputs"

def isNoApply : GenError → Bool
  | .genError m => "[interp:noapply]".isPrefixOf m

/-- A rejection at a call step whose callee could apply no constructor to what it was passed. Still a
    rejection at step `idx` (`rejectStepIdx?` reads the index), tagged so the caller's choice of inputs can
    be blamed. -/
def rejectNoApplyAt (idx : Nat) : GenError := .genError s!"{rejectPrefix}{idx}:noapply] "

def isRejectNoApply : GenError → Bool
  | .genError m => rejectPrefix.isPrefixOf m && (m.splitOn ":noapply]").length > 1

/-- The step index a rejection was attributed to, if it carries one. -/
def rejectStepIdx? : GenError → Option Nat
  | .genError m =>
    if rejectPrefix.isPrefixOf m then
      let rest := m.drop rejectPrefix.length
      (rest.takeWhile Char.isDigit).toNat?
    else none

/-- Runs `g`, re-tagging a discard with the step it happened at. Fuel exhaustion and interpreter
    misconfiguration are left alone.

    `desc` is a **thunk** so the label is built only when a discard actually needs it. As a `String`
    argument it was pretty-printed on *every* execution of every producing step, successes included.

    Honest accounting: making it lazy measured no improvement on the cases I checked, because those
    reject at a `.Match`, which calls `rejectAt` directly and never reaches `blaming`. Dropping the
    description from `rejectAt` — where `profileCtor` re-renders it from the schedule anyway — was
    worth 4% end to end. The thunk is kept because it is free and correct in principle. -/
def blaming {α : Type} (idx : Nat) (desc : Unit → String) (g : Gen α) : Gen α :=
  tryCatch g (fun e =>
    if isInterpError e || Gen.GenError.isInconclusive e then throw e
    else if isNoApply e then throw (rejectNoApplyAt idx)
    else throw (rejectAt idx (desc ())))

/-- Depth of the recorded rule-path window. -/
def rulePathDepth : Nat := 3

/-- Whether rule paths are being recorded. Off outside `withRulePaths`. -/
initialize rulePathEnabledRef : IO.Ref Bool ← IO.mkRef false

/-- The rule paths seen so far, most recent first. -/
initialize rulePathsRef : IO.Ref (List (List Name)) ← IO.mkRef []

@[never_extract, noinline]
private unsafe def notePathImpl {α : Type} (p : List Name) (a : α) : α :=
  unsafeBaseIO do
    if ← rulePathEnabledRef.get then
      rulePathsRef.modify (fun ps => p :: ps)
    return a

/-- Records one completed rule path and returns `a` unchanged. -/
@[implemented_by notePathImpl, never_extract, noinline]
def notePath {α : Type} (_p : List Name) (a : α) : α := a

/-- The path count at the start of each open branch, innermost first.

    Rule paths are recorded when a constructor branch *succeeds* (`notePath`), but a success can still
    be thrown away: a sub-derivation that succeeds and whose parent then fails. Rolling back the random
    state does not undo an `IO.Ref`, so without help those paths would be counted as if they were part
    of an output — and they come disproportionately from the constructors that fail most, which are the
    ones blame is trying to measure. So each branch of the backtracking combinators (and each root
    `attempt`) pushes the current count as it starts, and pops it as it ends: keeping what it recorded
    on success, truncating back to it on failure. What remains is exactly the kept derivations.

    Every one of these is a pure-looking function whose *result is the thing run next*, the same shape
    as `notePath`: the push returns the branch, the pops return the continuation. Taking the count in a
    separate `let` instead leaves the compiler free to move it, which it does: hoisted to a constant
    evaluated once, or floated into the failure handler, both silently wrong. The same reason puts
    `@[never_extract, noinline]` on every shim here. Their pure definitions are the identity, so two
    identical applications may be commoned up, and a call whose result is discarded may be dropped,
    either of which loses what it was there to record. -/
initialize rulePathMarksRef : IO.Ref (List Nat) ← IO.mkRef []

@[never_extract, noinline]
private unsafe def pathPushImpl {β α : Type} (_dep : β) (g : α) : α :=
  unsafeBaseIO do
    if ← rulePathEnabledRef.get then
      let n := (← rulePathsRef.get).length
      rulePathMarksRef.modify (n :: ·)
    return g

/-- Opens a branch: records the current path count, and returns `g`. -/
@[implemented_by pathPushImpl, never_extract, noinline]
def pathPush {β α : Type} (_dep : β) (g : α) : α := g

@[never_extract, noinline]
private unsafe def pathPopImpl {α : Type} (rollback : Bool) (a : α) : α :=
  unsafeBaseIO do
    if ← rulePathEnabledRef.get then
      match ← rulePathMarksRef.get with
      | mark :: rest =>
        rulePathMarksRef.set rest
        if rollback then rulePathsRef.modify (fun ps => ps.drop (ps.length - mark))
      | [] => pure ()
    return a

/-- Closes a branch, dropping what it recorded if `rollback`, and returns `a`. -/
@[implemented_by pathPopImpl, never_extract, noinline]
def pathPop {α : Type} (_rollback : Bool) (a : α) : α := a

/-- `tryCatch g h`, with the rule paths `g` recorded dropped if it fails. `key` is any value that
    differs per run, so that opening the branch is not shared between runs. -/
def tryCatchPaths {α β : Type} (key : β) (g : Gen α) (h : GenError → Gen α) : Gen α :=
  tryCatch (pathPush key (do let v ← g; pure (pathPop false v))) (fun e => pathPop true (h e))

/-- `GeneratorCombinators.backtrack`, except that interpreter **misconfiguration** is re-thrown rather
    than absorbed.

    `backtrack` treats every error as "this branch failed, try another". For an emitted generator that is
    right — its errors are all genuine failures — but the interpreter can also fail *internally*: an
    arity mismatch in `bindInputs`, an unregistered function, a leaf that cannot read its arguments. Under
    `backtrack` those looked like ordinary discards and another constructor was tried, so a rule that
    could never run was invisible. That is how the instance-argument bug hid: every call to Cedar's
    `MapNotContainsKey` from `hasAttrRecordNotFound` died on an arity mismatch, and nothing reported it.

    Otherwise identical — same draws, same order, same removal, same final error — so a schedule with no
    internal error samples exactly what it did before. It is a separate combinator rather than a change
    to `backtrack` itself so that emitted generators, which share `backtrack`, pay nothing for it. -/
def backtrackInterp {α : Type} (gs : List (Nat × Gen α)) : Gen α :=
  go gs.length (sumFst gs) gs false
where
  go : Nat → Nat → List (Nat × Gen α) → Bool → Gen α
    | .zero, _, _, anyInconclusive =>
      if anyInconclusive then throw Gen.outOfFuelError
      else throw (.genError "Specimen.GeneratorCombinators.backtrack: all branches failed")
    | .succ fuel', total, gs, anyInconclusive => do
      let n ← Gen.choose Nat 0 (total - 1) (by omega)
      let (k, g, gs') := pickDrop gs n
      tryCatchPaths n g (fun e =>
        if isInterpError e then throw e
        else go fuel' (total - k) gs' (anyInconclusive || Gen.GenError.isInconclusive e))

/-- `backtrackInterp`, additionally told for each branch whether a given failure was a refusal *on the
    inputs*; when every branch failed that way, it throws `noApplyError key` instead of "all branches
    failed". Same draws, same order, same outcome otherwise — both errors are definitive. -/
def backtrackInterpTracked {α : Type} (key : SpecKey) (gs : List (Nat × Gen α × (GenError → Bool))) :
    Gen α :=
  go gs.length (sumFst (gs.map (fun (w, g, _) => (w, g)))) gs false true
where
  go : Nat → Nat → List (Nat × Gen α × (GenError → Bool)) → Bool → Bool → Gen α
    | .zero, _, _, anyInconclusive, allOnInputs =>
      if anyInconclusive then throw Gen.outOfFuelError
      else if allOnInputs then throw (noApplyError key)
      else throw (.genError "Specimen.GeneratorCombinators.backtrack: all branches failed")
    | .succ fuel', total, gs, anyInconclusive, allOnInputs => do
      let n ← Gen.choose Nat 0 (total - 1) (by omega)
      let (k, g, gs') := pickDropTracked gs n
      tryCatchPaths n g.1 (fun e =>
        if isInterpError e then throw e
        else go fuel' (total - k) gs' (anyInconclusive || Gen.GenError.isInconclusive e)
          (allOnInputs && g.2 e))
  /-- `pickDrop` over triples, clause for clause, so the same branch is drawn for the same `n`. -/
  pickDropTracked : List (Nat × Gen α × (GenError → Bool)) → Nat →
      Nat × (Gen α × (GenError → Bool)) × List (Nat × Gen α × (GenError → Bool))
    | [], _ => (0, (throw (.genError "Plausible.Specimen.GeneratorCombinators: failure."), fun _ => false), [])
    | (k, x, f) :: xs, n =>
      if n < k then (k, (x, f), xs)
      else
        let (k', x', xs') := pickDropTracked xs (n - k)
        (k', x', (k, x, f) :: xs')

/-! ## Counting the failures `backtrack` absorbs

    A discard is only visible from outside if it reaches the caller, and almost none of them do:
    `backtrack` catches every branch failure to try the next constructor, so a run that retried a
    thousand times reports the same "one success" as a run that retried once. Measured at the root,
    Cedar's `HasType[0,3,4]` scores 1000‰ acceptance under *every* premise ordering — while the
    orderings differ 4.5× in wall-clock. All of the signal is in the absorbed failures.

    `profileCtor` exposes them for a *single* constructor by running `runCtorOnce`, which has no
    backtrack. That misses the recursive case: a constructor whose sub-producer call retries deeply
    still looks like one attempt. So the count has to be taken where the absorption happens, inside
    `ctorBranch`.

    `Gen` is `StateT StdGen` over `Except` — no IO, no writer, and `throw` rolls the state back — so
    there is nowhere in the monad to accumulate a counter. Rather than change `Gen`'s type (which
    would touch every derived generator and all the emitted code for a number only the tuner wants),
    the tally lives in a module-level `IO.Ref` written through `@[implemented_by]` shims. The pure
    definitions are the identity, so nothing about generation depends on the counting; the compiled
    versions record and return their argument, which is why they are applied to the value being
    returned or the error being thrown rather than called for effect — an unused `Unit` would be
    dropped.

    Off by default, and `withRetryLog` is the only thing that turns it on. When disabled the cost is
    a `tryCatch` and a `Bool` deref per constructor attempt. -/

/-- Branch attempts and absorbed failures for one (mode, constructor) pair. -/
structure RetryTally where
  /-- Constructor branches entered. -/
  attempts : Nat := 0
  /-- Of those, how many failed and were caught by `backtrack`. -/
  failures : Nat := 0
  /-- Of those failures, how many were interpreter **misconfiguration** (`isInterpError`) rather than a
      discard. Kept apart because it is a bug to fix, not a rate to tune: `backtrackInterp` re-throws
      these, so each one also ends the attempt it happened in. -/
  internal : Nat := 0
  deriving Repr, Inhabited, BEq

/-- Absorbed failures, per (mode, constructor) and per rejecting step.

    `byStep` is the localiser: `byCtor` says which constructor is retrying, `byStep` says which of
    its premises threw the attempt away. Failures with no step attribution (fuel exhaustion,
    misconfiguration) are counted in `byCtor` but not in `byStep`. -/
structure RetryLog where
  byCtor : Std.HashMap (SpecKey × Name) RetryTally := {}
  byStep : Std.HashMap (SpecKey × Name × Nat) Nat := {}
  /-- The subset of `byStep` whose rejection was a callee applying no constructor to what this step passed
      (`rejectNoApplyAt`), which is the caller's choice of inputs rather than anything inside the callee. -/
  byStepNoApply : Std.HashMap (SpecKey × Name × Nat) Nat := {}
  /-- The first internal error recorded: where it started (the innermost frame counts first) and its
      message. -/
  firstInternal : Option (SpecKey × Name × String) := none
  deriving Inhabited

/-- Whether the counters are recording. Off outside `withRetryLog`. -/
initialize retryEnabledRef : IO.Ref Bool ← IO.mkRef false

/-- The tally being accumulated. -/
initialize retryLogRef : IO.Ref RetryLog ← IO.mkRef {}

private def RetryLog.bump (l : RetryLog) (k : SpecKey) (c : Name) (failed : Bool)
    (step : Option Nat) (internalMsg : Option String := none) (noApply : Bool := false) : RetryLog :=
  let t := l.byCtor.getD (k, c) {}
  let byCtor := l.byCtor.insert (k, c)
    { t with attempts := t.attempts + 1, failures := t.failures + (if failed then 1 else 0),
             internal := t.internal + (if internalMsg.isSome then 1 else 0) }
  let byStep := match step with
    | some i => l.byStep.insert (k, c, i) ((l.byStep.getD (k, c, i) 0) + 1)
    | none => l.byStep
  let firstInternal := l.firstInternal.orElse (fun _ => internalMsg.map (fun m => (k, c, m)))
  let byStepNoApply := match step, noApply with
    | some i, true => l.byStepNoApply.insert (k, c, i) ((l.byStepNoApply.getD (k, c, i) 0) + 1)
    | _, _ => l.byStepNoApply
  { l with byCtor := byCtor, byStep := byStep, firstInternal := firstInternal,
           byStepNoApply := byStepNoApply }

@[never_extract, noinline]
private unsafe def noteSuccessImpl {α : Type} (k : SpecKey) (c : Name) (a : α) : α :=
  unsafeBaseIO do
    if ← retryEnabledRef.get then
      retryLogRef.modify (fun l => l.bump k c false none)
    return a

/-- Records a successful constructor attempt and returns `a` unchanged. -/
@[implemented_by noteSuccessImpl, never_extract, noinline]
def noteSuccess {α : Type} (_k : SpecKey) (_c : Name) (a : α) : α := a

@[never_extract, noinline]
private unsafe def noteFailureImpl (k : SpecKey) (c : Name) (e : GenError) : GenError :=
  unsafeBaseIO do
    if ← retryEnabledRef.get then
      let internalMsg := match e with
        | .genError m => if isInterpError e then some m else none
      retryLogRef.modify (fun l => l.bump k c true (rejectStepIdx? e) internalMsg (isRejectNoApply e))
    return e

/-- Records a failed constructor attempt and returns `e` unchanged, so the error still propagates
    to `backtrack` exactly as before. -/
@[implemented_by noteFailureImpl, never_extract, noinline]
def noteFailure (_k : SpecKey) (_c : Name) (e : GenError) : GenError := e

/-! ## Rule-path coverage

`RunStats.kPathsSeen` records paths through the generated **value**'s constructors. This records paths
through the **rules** — the implicit proof tree — which is a different question: two outputs can share a
shape while being derived by different rules, and one output can be derivable several ways.

The path arrives as an ordinary parameter threaded down the interpreter, so there is no push/pop
discipline to get wrong; the ref is append-only and order-insensitive. What is recorded is every
*completed constructor schedule*, so under `backtrack` some recorded paths belong to attempts that an
enclosing rule later abandoned. That is fine for comparing two policies measured the same way, but it is
"rule paths explored", not "rule paths in the accepted derivation". -/

/-- Runs `act` with rule-path recording on, returning the distinct paths alongside its result.

    Not reentrant, for the same reason `withRetryLog` is not: one module-level ref. -/
def withRulePaths {α : Type} (act : IO α) : IO (α × List (List Name)) := do
  rulePathsRef.set []
  rulePathMarksRef.set []
  rulePathEnabledRef.set true
  try
    let a ← act
    let ps ← rulePathsRef.get
    return (a, ps.foldl (fun acc p => if acc.contains p then acc else p :: acc) [])
  finally
    rulePathEnabledRef.set false

/-! ## Recording where constructors are entered

Diagnosing a constructor in isolation (`Interp.Diagnose`) needs the inputs and sizes it is *actually*
entered with. Most constructors of a large relation run only as sub-calls, with inputs the root never
supplies — Cedar's `varContext` is asked for record types, and no root input passes its guard at all — so
testing them on the root's inputs says nothing about them. -/

/-- One recorded entry: the inputs, `initSize`, and the size the constructor's schedule ran with. -/
abbrev CtorEntry := List Val × Nat × Nat

/-- Whether entries are being recorded. Off outside `withEntries`. -/
initialize entryEnabledRef : IO.Ref Bool ← IO.mkRef false

/-- Entries so far, per `(mode, constructor)`: distinct, and at most `entryCap` each. -/
initialize entriesRef : IO.Ref (Std.HashMap (SpecKey × Name) (Array CtorEntry)) ← IO.mkRef {}

/-- How many distinct entries are kept per constructor. -/
def entryCap : Nat := 40

@[never_extract, noinline]
private unsafe def recordEntryImpl (key : SpecKey) (ctor : Name) (initSize size : Nat) (inputs : List Val) :
    List Val :=
  unsafeBaseIO do
    if ← entryEnabledRef.get then
      entriesRef.modify (fun m =>
        let es := m.getD (key, ctor) #[]
        let e : CtorEntry := (inputs, initSize, size)
        if es.size ≥ entryCap || es.contains e then m else m.insert (key, ctor) (es.push e))
    return inputs

/-- Records that constructor `ctor` of `key` was entered with `inputs` at `(initSize, size)`, and
    returns `inputs` — the shape of `notePath`, so the call stays where it is. -/
@[implemented_by recordEntryImpl, never_extract, noinline]
def recordEntry (_key : SpecKey) (_ctor : Name) (_initSize _size : Nat) (inputs : List Val) : List Val :=
  inputs

/-- Runs `act` recording constructor entries, and returns them. Not reentrant (one module-level ref). -/
def withEntries {α : Type} (act : IO α) : IO (α × Std.HashMap (SpecKey × Name) (Array CtorEntry)) := do
  entriesRef.set {}
  entryEnabledRef.set true
  try
    let a ← act
    return (a, ← entriesRef.get)
  finally
    entryEnabledRef.set false

/-- `withRulePaths`, keeping every recorded path rather than the distinct ones — one per node of every
    kept derivation. -/
def withRulePathsAll {α : Type} (act : IO α) : IO (α × List (List Name)) := do
  rulePathsRef.set []
  rulePathMarksRef.set []
  rulePathEnabledRef.set true
  try
    let a ← act
    return (a, (← rulePathsRef.get).reverse)
  finally
    rulePathEnabledRef.set false

/-- Wraps one constructor branch so that whichever way it ends is counted. Semantically the identity
    on `g`: the same value is returned and the same error is rethrown. -/
def counting {α : Type} (k : SpecKey) (c : Name) (g : Gen α) : Gen α :=
  tryCatch (do let v ← g; pure (noteSuccess k c v))
    (fun e => throw (noteFailure k c e))

/-- Runs `act` with the counters recording, and returns the tally alongside its result.

    Not reentrant: the log is a single module-level ref, so nested or concurrent uses share it. -/
def withRetryLog {α : Type} (act : IO α) : IO (α × RetryLog) := do
  retryLogRef.set {}
  retryEnabledRef.set true
  try
    let a ← act
    let l ← retryLogRef.get
    return (a, l)
  finally
    retryEnabledRef.set false

namespace RetryLog

/-- Entries, worst first by absorbed failures. -/
def entries (l : RetryLog) : List ((SpecKey × Name) × RetryTally) :=
  l.byCtor.toList.mergeSort (fun a b => b.2.failures ≤ a.2.failures)

def totalAttempts (l : RetryLog) : Nat :=
  l.byCtor.fold (fun acc _ t => acc + t.attempts) 0

def totalFailures (l : RetryLog) : Nat :=
  l.byCtor.fold (fun acc _ t => acc + t.failures) 0

/-- Constructor attempts that ended in interpreter misconfiguration. Also included in `totalFailures`,
    so `failPerMille` keeps its meaning; report this beside it, and treat any nonzero value as a bug. -/
def totalInternal (l : RetryLog) : Nat :=
  l.byCtor.fold (fun acc _ t => acc + t.internal) 0

/-- Absorbed failures per thousand constructor attempts. The deterministic counterpart of
    `ClosureStats.wastePerMille`, which has to infer the same quantity from wall-clock. -/
def failPerMille (l : RetryLog) : Nat :=
  let a := l.totalAttempts
  if a == 0 then 0 else 1000 * l.totalFailures / a

/-- The tally for one mode, summed over its constructors. -/
def forKey (l : RetryLog) (k : SpecKey) : RetryTally :=
  l.byCtor.fold (fun acc (k', _) t =>
    if k' == k then { attempts := acc.attempts + t.attempts,
                      failures := acc.failures + t.failures }
    else acc) {}

/-- The steps that threw attempts away for one (mode, constructor), worst first. -/
def stepsFor (l : RetryLog) (k : SpecKey) (c : Name) : List (Nat × Nat) :=
  (l.byStep.toList.filterMap (fun ((k', c', i), n) =>
    if k' == k && c' == c then some (i, n) else none)).mergeSort (fun a b => b.2 ≤ a.2)

def render (l : RetryLog) (top : Nat := 12) : String :=
  let hdr := s!"{l.totalFailures}/{l.totalAttempts} constructor attempts absorbed \
    ({l.failPerMille}‰)" ++
    (match l.firstInternal with
     | some (k, c, m) => s!"\n  {l.totalInternal} died on an internal error, first in {c} @ \
         {renderSpecKey k}: {m}"
     | none => "")
  let lines := (l.entries.take top).map (fun ((k, c), t) =>
    let steps := l.stepsFor k c
    let stepStr := if steps.isEmpty then "" else
      "  steps " ++ ", ".intercalate (steps.take 3 |>.map (fun (i, n) => s!"#{i}×{n}"))
    let perMille := if t.attempts == 0 then 0 else 1000 * t.failures / t.attempts
    s!"  {c} @ {renderSpecKey k}: {t.failures}/{t.attempts} ({perMille}‰){stepStr}")
  hdr ++ (if lines.isEmpty then "" else "\n" ++ "\n".intercalate lines)

end RetryLog

/-- Lifts a pure `Except String` computation, treating its errors as misconfiguration. -/
def liftInterp {α : Type} : Except String α → Gen α
  | .ok a => pure a
  | .error e => throwInterp e

/-- Binds a list of names to a list of values, failing if the arities disagree. -/
def bindVars (names : List Name) (vals : List Val) (bindings : ValEnv) : Except String ValEnv :=
  if names.length != vals.length then
    .error s!"arity mismatch binding sub-producer results: {names.length} variable(s) \
      {names} but {vals.length} value(s) {vals.map toString}"
  else
    .ok ((names.zip vals).foldl (fun acc (n, v) => acc.insert n v) bindings)

/-- Binds a relation's value-level inputs to its argument names at the input positions. -/
def RelSchedule.bindInputs (rel : RelSchedule) (inputs : List Val) : Except String ValEnv :=
  bindVars rel.inputNames inputs ∅

/-- Collapses a sub-producer's results into the single value an `Unconstrained` step binds:
    multiple outputs become a right-nested tuple, exactly as the emitted code's tuple pattern. -/
def collapseOutputs : List Val → Val
  | [v] => v
  | vs => Val.tuple vs

/-- Splits a hypothesis' arguments into the *output* positions (those mentioning one of `vars`) and
    the evaluated *input* values (every other value-level position).

    Positions are raw indices into the hypothesis' argument list, and a position counts as an output
    when it *mentions* one of `vars` — the rule `Schedules.computeOutputIndicesForRewrite` uses to
    compute a `SpecKey`'s `outputIndices` at compile time. Usually the argument simply *is* the
    variable, because the scheduler rewrites a produced argument that is a constructor application
    into a fresh variable plus a `Match` (`handleConstrainedOutputs`). The exception is a delegated
    equality premise, where the variable stays buried in a function application and the producer
    returns its value; reading the variable out of the position rather than requiring the position to
    be the variable covers both. Outputs come back ascending by position.

    Inputs skip the callee's type and instance positions `typeIdx` (`InterpEnv.typeArgIndicesOf`) as
    well as anything syntactically type-level, so the callee gets exactly one value per position it
    binds. Skipping by kind alone passed Cedar's `instDecidableEqString` dictionary to
    `MapNotContainsKey` as an extra input — see `valueArgsAt`. -/
def splitHypothesis (funcs : FuncTable) (bindings : ValEnv) (vars : List Name)
    (args : List ConstructorExpr) (typeIdx : List Nat := []) :
    Except String (List (Nat × Name) × List Val) := do
  let indexed := args.zipIdx
  let outputs : List (Nat × Name) := indexed.filterMap (fun (a, i) =>
    match a with
    | .Unknown u => if vars.contains u then some (i, u) else none
    | _ => (varsInConstructorExpr a |>.find? (vars.contains ·)).map (fun u => (i, u)))
  -- One position per variable: a variable appearing twice is an output at its first occurrence.
  let outputs := outputs.foldl (fun acc (i, u) =>
    if acc.any (fun (_, u') => u' == u) then acc else acc ++ [(i, u)]) []
  let missing := vars.filter (fun v => !outputs.any (fun (_, u) => u == v))
  if !missing.isEmpty then
    .error s!"variable(s) {missing} are produced by this step but do not appear as arguments of \
      the hypothesis, so the interpreter cannot tell which output position they occupy"
  let inputs ← indexed.filterMap (fun (a, i) =>
      if outputs.any (fun (j, _) => j == i) || typeIdx.contains i || isTypeLevel a then none
      else some a)
    |>.mapM (evalConstructorExpr funcs bindings)
  return (outputs, inputs)

/-- The value-level arguments of a hypothesis, evaluated — what a checker receives.

    `typeIdx` is the checked relation's type and instance positions (`InterpEnv.typeArgIndicesOf`). An
    *interpreted* checker binds one input per value position, so a dictionary that survived `valueArgs`
    is one input too many for it, where a leaf reading from the end never noticed. -/
def evalHypothesisArgs (funcs : FuncTable) (bindings : ValEnv) (args : List ConstructorExpr)
    (typeIdx : List Nat := []) : Except String (List Val) :=
  (valueArgsAt typeIdx args).mapM (evalConstructorExpr funcs bindings)

/-- Interprets a `Check` step's source as a three-valued check. The outer `Except String` reports
    interpreter misconfiguration; the inner `Except GenError Bool` is the checker's own verdict,
    exactly as `DecOpt.decOpt` would return it.

    `Eq` and `Ne` are decided structurally, mirroring the built-in `[Decidable P] → DecOpt P`
    instance the pipeline relies on. Every other relation is looked up in `InterpEnv.checkers`. -/
def checkSource (env : InterpEnv) (targetInductive : Name) (src : Source)
    (fuel' initSize sizeExpr : Nat) (bindings : ValEnv) :
    Except String (Except GenError Bool) := do
  match src with
  | .NonRec (relName, args) => do
    let vals ← evalHypothesisArgs env.funcs bindings args (env.typeArgIndicesOf relName)
    if relName == ``Eq then
      match lastArgs 2 vals with
      | [a, b] => return .ok (a == b)
      | _ => .error s!"`Eq` check expected 2 value arguments, got {vals.length}"
    else if relName == ``Ne then
      match lastArgs 2 vals with
      | [a, b] => return .ok (!(a == b))
      | _ => .error s!"`Ne` check expected 2 value arguments, got {vals.length}"
    else
      match env.checkers[relName]? with
      | some c =>
        -- Same-inductive dependencies share the split size budget; others get the full `initSize`.
        let fuel := if relName == targetInductive then sizeExpr else initSize
        return c fuel vals
      | none =>
        .error s!"no checker registered for '{relName}' (needed to check \
          `{ppHypothesisExpr (relName, args)}`; register one with `InterpEnv.addChecker`)"
  | .Rec f args | .MutRec f args => do
    let vals ← (valueArgs args).mapM (evalConstructorExpr env.funcs bindings)
    match env.checkers[f]? with
    -- The emitted code compiles this to `recCall f fuel' initSize sizeExpr`, so the *size* it gets is
    -- the split budget. A `ValChecker` leaf takes one number, and that number plays the role of size
    -- (it is what `DecOpt.decOpt` receives), so `sizeExpr` is the faithful choice — `fuel'` would hand
    -- a recursive checker the outer termination fuel and make it effectively unbounded.
    | some c => return c sizeExpr vals
    | none =>
      .error s!"step checks via the recursive checker '{f}', which v1 does not interpret; \
        register a checker for '{f}' with `InterpEnv.addChecker`"

/-! ## Dividing a constructor's size budget among its recursive calls

`.equal` reproduces the emitted code exactly: one quotient handed to every call. `.starsAndBars` draws a
composition uniformly, so an unbalanced shape is reachable without inflating the total budget.

**Why stars and bars rather than drawing each part from what is left:** the latter is not uniform over
compositions and systematically favours the early parts — the same bias a threaded remainder has. Drawing
`k-1` cut points in `0..n`, sorting, and taking the gaps is uniform. -/

private def gapsOf (n : Nat) : Nat → List Nat → List Nat
  | prev, [] => [n - prev]
  | prev, c :: cs => (c - prev) :: gapsOf n c cs

private def drawCuts (n : Nat) : Nat → Gen (List Nat)
  | 0 => pure []
  | k + 1 => do
      let c ← Subtype.val <$> Gen.choose Nat 0 n (by omega)
      let rest ← drawCuts n k
      return c :: rest

/-- A composition of `n` into `k` non-negative parts. `.equal` gives `k` copies of `n / k`, which is
what the emitted code computes; `.starsAndBars` guarantees each part `floor‰` of `n / k` and draws the
remainder's composition uniformly. -/
def drawSplitEven (policy : SplitPolicy) (n k : Nat) (floor : Nat := 0) : Gen (List Nat) :=
  match policy with
  | .equal => pure (List.replicate k (if k ≤ 1 then n else n / k))
  | .starsAndBars =>
      if k ≤ 1 then pure (List.replicate k n)
      else do
        let base := n / k * min floor 1000 / 1000
        let rest := n - k * base
        let cuts ← drawCuts rest (k - 1)
        return (gapsOf rest 0 (cuts.mergeSort (· ≤ ·))).map (· + base)

/-- `drawSplitEven`, after first guaranteeing call `i` the minimum `mins[i]` (see
    `InterpEnv.premiseFloor`). Minimums are met in call order as far as `n` reaches; what is left is split
    by `policy`. With no positive minimum this is `drawSplitEven` exactly, draw for draw. The parts
    always sum to what `drawSplitEven` would hand out for the remainder plus the minimums met, so the
    budget never grows. -/
def drawSplit (policy : SplitPolicy) (n k : Nat) (floor : Nat := 0) (mins : List Nat := []) :
    Gen (List Nat) :=
  if mins.all (· == 0) then drawSplitEven policy n k floor
  else do
    let (passed, left) := (mins.take k).foldl (fun (acc : List Nat × Nat) m =>
      let g := min m acc.2
      (acc.1 ++ [g], acc.2 - g)) ([], n)
    let passed := passed ++ List.replicate (k - passed.length) 0
    let rest ← drawSplitEven policy left k floor
    return (passed.zip rest).map (fun (a, b) => a + b)

/-- For each size-consuming step of a schedule, in order, the premise that emitted it (`none` for a
    step no premise emitted). These are the steps `runSteps` hands an allocation to. -/
def sizeConsumingPremises (target : Name) (steps : List ScheduleStep)
    (origins : List (Option PlanStep)) : List (Option Nat) :=
  steps.zipIdx.filterMap (fun (st, i) =>
    if countSizeConsumingCalls target [st] == 0 then none
    else some (match (origins[i]?).bind id with | some (.use p) => some p | _ => none))

mutual

/-- Runs a spec at `(fuel, initSize, size)` on its value-level `inputs` (ascending input position),
    producing one value per value-level output position (ascending).

    Prefers an interpreted schedule; falls back to a registered `ValProducer`. -/
partial def interpRel (env : InterpEnv) (key : SpecKey) (fuel initSize size : Nat)
    (inputs : List Val) (rulePath : List Name := []) : Gen (List Val) :=
  match env.relations[key]? with
  | some rel =>
    -- Refuse a schedule of the wrong sort rather than mis-running it. A checker schedule ends in
    -- `CheckerSchedule` and its steps assume `Except GenError Bool` semantics — interpreting it here
    -- would fail deep inside for an unrelated-looking reason. `interpEnumRel` and `interpChecker`
    -- guard the same way.
    if rel.key.deriveSort == .Generator then interpRelSchedule env rel fuel initSize size inputs rulePath
    else
      throwInterp s!"{renderSpecKey key} is registered as a {repr rel.key.deriveSort}, not a \
        Generator; use `InterpEnv.decide` for a checker or `InterpEnv.enumerateSpec` for an enumerator"
  | none =>
    match env.producers[key]? with
    | some p => p initSize size inputs
    | none =>
      throwInterp s!"no schedule or producer registered for {renderSpecKey key} \
        (add a `RelSchedule` with `InterpEnv.addRelation`, or a leaf with \
        `InterpEnv.addProducer`)"

/-- The body of the emitted `aux_arb`: match on fuel, then on size, then backtrack over the
    constructors admissible at that size. -/
partial def interpRelSchedule (env : InterpEnv) (rel : RelSchedule) (fuel initSize size : Nat)
    (inputs : List Val) (rulePath : List Name := []) : Gen (List Val) :=
  match fuel with
  | 0 => throw Gen.outOfFuelError
  | fuel' + 1 =>
    let (baseScheds0, recScheds0) := rel.bucketedSchedules
    -- Hoisted dispatch: drop the branches whose leading input `Match` cannot match, instead of entering
    -- them and letting each reject at its first step. `numBase`/`numRec` are counted *after* the filter,
    -- so the weight function sees the branch counts it is actually choosing among.
    -- `inputNames` is hoisted out of the per-constructor test. Computing it inside rebuilds
    -- `List.range rel.argNames.length` plus two filters and a `filterMap` **76 times per entry**, purely
    -- to map a scrutinee name to an input index, which costs more than the filter saves: 14% slower
    -- generation even while absorbed failures drop 83%. The `matchPattern` calls genuinely depend on the
    -- runtime inputs and stay; the scaffolding does not.
    --
    -- The filter can empty the list. That case is correct rather than merely tolerated: `backtrack []` throws "all branches failed", a *definitive*
    -- failure and not `outOfFuelError`, and by `guardPassesWith`'s soundness argument an empty list means
    -- no constructor's input pattern can match these inputs — so there is genuinely no derivation. The
    -- distinction matters downstream, where only inconclusive errors poison a checker's verdict
    -- (`lazyListBacktrackOpt`); a definitive failure correctly reads as `.ok false`.
    let inNames := rel.inputNames
    -- Refuse a call with the wrong number of inputs here, once, and *outside* `backtrack`. Left to
    -- `bindInputs` it failed in every constructor, `backtrack` rethrew that as a plain "all branches
    -- failed", and the caller's `blaming` filed it as an ordinary discard at the calling step. That is
    -- how Cedar's `MapNotContainsKey[3,4]`, handed an instance dictionary as an extra input, read as
    -- `HasType.hasAttrRecordNotFound` rejecting at its producer step rather than as misconfiguration.
    -- Thrown from here it stays an `[interp]` error, which `blaming` passes through untouched, so
    -- `runCtorOnce` on the calling rule names the arity instead of `[interp:reject:…]`.
    --
    -- It also keeps the dispatch guard sound. `guardPassesWith` reads `inputs` by index into `inNames`,
    -- and a stray leading value shifts every read by one, so it matched each rule's pattern against the
    -- wrong input and pruned rules that could have run.
    if inputs.length != inNames.length then
      throwInterp s!"{renderSpecKey rel.key} binds {inNames.length} value input(s) {inNames} but \
        was called with {inputs.length}: {inputs.map toString}"
    else
      let keep := fun (p : Name × Schedule) =>
        !env.dispatchInputs || RelSchedule.guardPassesWith inNames p.2.1 inputs
      let baseScheds := baseScheds0.filter keep
      let recScheds := recScheds0.filter keep
      let numBase := baseScheds.length
      let numRec := recScheds.length
      let branch := fun (size' : Nat) (isRec : Bool) (p : Name × Schedule) =>
        ctorBranch env rel fuel' initSize size' isRec numBase numRec inputs p.1 p.2 rulePath
      if env.attributeNoApply then
        -- Which failures of a branch were refusals on the inputs: a `Match`/`Check` that read only
        -- input-determined values, or a call, reading only such values, whose callee applied nothing.
        let onInputs := fun (steps : List ScheduleStep) (e : GenError) =>
          match rejectStepIdx? e with
          | some i => Dataflow.failsOnInputs inNames steps i
                        || (isRejectNoApply e && Dataflow.callReadsOnlyInputs inNames steps i)
          | none => false
        let tracked := fun (size' : Nat) (isRec : Bool) (p : Name × Schedule) =>
          let (w, g) := branch size' isRec p
          (w, g, onInputs p.2.1)
        let branches := match size with
          | 0 => baseScheds.map (tracked 0 false)
          | size' + 1 => baseScheds.map (tracked size' false) ++ recScheds.map (tracked size' true)
        if branches.isEmpty then throw (noApplyError rel.key)
        else backtrackInterpTracked rel.key branches
      else
      match size with
      | 0 => backtrackInterp (baseScheds.map (branch 0 false))
      | size' + 1 =>
        backtrackInterp (baseScheds.map (branch size' false) ++ recScheds.map (branch size' true))

/-- One weighted branch of the backtracking combinator: the weight the emitted code computes for
    this constructor, paired with the generator that runs its schedule. -/
partial def ctorBranch (env : InterpEnv) (rel : RelSchedule) (fuel' initSize size' : Nat)
    (isRec : Bool) (numBase numRec : Nat) (inputs : List Val) (ctorName : Name)
    (sched : Schedule) (rulePath : List Name := []) : Nat × Gen (List Val) :=
  let numRecCalls := rel.numRecCallsOf ctorName sched.1
  let weight := env.weightFn ctorName rel.key.outputIndices rel.key.deriveSort
    (rel.badnessOf ctorName) isRec (if isRec then size' else 0) numBase numRec numRecCalls
  -- `counting` is the identity unless `withRetryLog` is active; this is the point where `backtrack`
  -- would otherwise absorb the failure without trace.
  (weight, counting rel.key ctorName (runCtor env rel ctorName fuel' initSize size' inputs sched rulePath))

/-- Runs one constructor's schedule: bind the inputs, split the size budget, execute the steps. -/
partial def runCtor (env : InterpEnv) (rel : RelSchedule) (ctorName : Name)
    (fuel' initSize size' : Nat)
    (inputs : List Val) (sched : Schedule) (rulePath : List Name := []) : Gen (List Val) := do
  let (steps, sort) := sched
  let numRecCalls := rel.numRecCallsOf ctorName steps
  let sizeExpr := if numRecCalls ≤ 1 then size' else size' / numRecCalls
  -- Per-call allocation. Under `.equal` every entry is `sizeExpr`, so behaviour is bit-identical to
  -- before; under `.starsAndBars` the entries vary and `sizeExpr` survives only as the fallback for
  -- steps that are not recursive calls.
  -- Provenance only for a constructor that has floors: this runs on every constructor attempt, and a
  -- two-scrutinee `match` would evaluate the lookup for all of them.
  let mins : List Nat := match env.premiseFloor[ctorName]? with
    | none => []
    | some floors =>
      match rel.provenanceOf? ctorName with
      | none => []
      | some prov =>
        (sizeConsumingPremises rel.key.inductiveName steps prov.origins).map (fun p? =>
          match p? with
          | some p => ((floors.find? (·.1 == p)).map (·.2)).getD 0
          | none => 0)
  let alloc ← drawSplit env.splitPolicy size' numRecCalls (env.splitFloor.getD ctorName 0) mins
  let bindings ← liftInterp (rel.bindInputs (recordEntry rel.key ctorName initSize size' inputs))
  -- The path to *this* rule. Recorded when its schedule completes, and extended for anything it calls.
  --
  -- Held **newest-first and capped at `rulePathDepth`**, which matters because this runs on every
  -- constructor attempt whether or not anything is recording. `rulePath ++ [ctorName]` was an O(depth)
  -- append per attempt — O(depth²) of allocation per generated value — and the recorded window then cost
  -- two more full reverses. Only the last `rulePathDepth` entries are ever recorded, so truncating on the
  -- way down is the same window: cons is O(1) and the only reverse left is of at most three elements.
  let here := (ctorName :: rulePath).take rulePathDepth
  let vals ← runSteps env rel fuel' initSize sizeExpr alloc bindings steps sort 0 here
  return notePath here.reverse vals

/-- Executes the remaining schedule steps, then the epilogue.

    `stepIdx` is the index of the head of `steps` in the schedule as a whole, so a discard can name
    the step that caused it (see `blaming`). It is bookkeeping only: nothing about generation depends
    on it. -/
partial def runSteps (env : InterpEnv) (rel : RelSchedule) (fuel' initSize sizeExpr : Nat)
    (alloc : List Nat) (bindings : ValEnv) (steps : List ScheduleStep) (sort : ScheduleSort)
    (stepIdx : Nat) (rulePath : List Name := []) : Gen (List Val) := do
  -- `recSize` is this step's share if it is a recursive call, `alloc'` the rest. Empty list falls back
  -- to `sizeExpr`, so a schedule with more recursive steps than `numRecCallsOf` counted still runs.
  let recSize := alloc.headD sizeExpr
  let alloc' := alloc.tail
  match steps with
  | [] => runEpilogue env bindings sort
  | step :: rest =>
    -- A non-recursive step must NOT consume an allocation, or the recursive calls run out and silently
    -- fall back to `sizeExpr` — which reproduces `.equal` exactly and makes the policy a no-op.
    let continueWith := fun (bindings' : ValEnv) =>
      runSteps env rel fuel' initSize sizeExpr alloc bindings' rest sort (stepIdx + 1) rulePath
    let continuePop := fun (bindings' : ValEnv) =>
      runSteps env rel fuel' initSize sizeExpr alloc' bindings' rest sort (stepIdx + 1) rulePath
    match step with
    | .Unconstrained v src ps => do
      if ps == .Enumerator then
        throwInterp s!"step generates '{v}' with an enumerator; v1 interprets generators only"
      match src with
      | .NonRec hyp =>
        match env.lookupArbitrary hyp with
        | some g => do continueWith (bindings.insert v (← g))
        | none =>
          throwInterp s!"no unconstrained generator registered for type \
            `{ppHypothesisExpr hyp}` (needed to generate '{v}'; register one with \
            `InterpEnv.addArbitrary {hyp.1}` or `InterpEnv.addArbitraryAt \
            \"{ppHypothesisExpr hyp}\"`)"
      | .Rec f args | .MutRec f args => do
        let outs ← blaming stepIdx (fun _ => ppStep step) (interpCall env f args fuel' initSize recSize bindings rulePath)
        continuePop (bindings.insert v (collapseOutputs outs))
    | .SuchThat varsTys src ps => do
      let vars := varsTys.map Prod.fst
      if ps == .Enumerator then
        throwInterp s!"step produces {vars} with an enumerator; v1 interprets generators only"
      match src with
      | .NonRec hypExpr => do
        let outs ← blaming stepIdx (fun _ => ppStep step)
          (interpConstrained env rel hypExpr vars initSize sizeExpr bindings)
        continueWith (← liftInterp (bindVars (outs.map Prod.fst) (outs.map Prod.snd) bindings))
      | .Rec f args | .MutRec f args => do
        let outs ← blaming stepIdx (fun _ => ppStep step) (interpCall env f args fuel' initSize recSize bindings rulePath)
        continuePop (← liftInterp (bindVars vars outs bindings))
    | .Check src polarity => do
      let verdict ← liftInterp
        (checkSource env rel.key.inductiveName src fuel' initSize sizeExpr bindings)
      match verdict with
      | .ok b => if b == polarity then continueWith bindings else throw (rejectAt stepIdx "")
      -- A checker that failed *internally* (a leaf that cannot read its arguments, a derived checker
      -- that hit an arity mismatch) has not refuted anything: pass the error on instead of filing it
      -- as a rejection at this step. Any other error — out of fuel, a genuine failure — rejects, as before.
      | .error e => if isInterpError e then throw e else throw (rejectAt stepIdx "")
    | .Match _ scrutinee pattern => do
      match bindings[scrutinee]? with
      | none =>
        throwInterp s!"match scrutinee '{scrutinee}' is unbound at this point in the schedule"
      | some v =>
        match matchPattern pattern v bindings with
        | some bindings' => continueWith bindings'
        | none => throw (rejectAt stepIdx "")

/-- A recursive or mutual-recursive call: the callee is named by its `recFnName`, its explicit
    arguments are the caller's inputs, and it threads the decremented fuel and the split size. -/
partial def interpCall (env : InterpEnv) (f : Name) (args : List ConstructorExpr)
    (fuel' initSize sizeExpr : Nat) (bindings : ValEnv) (rulePath : List Name := []) :
    Gen (List Val) := do
  match env.keyOfFn? f with
  | none =>
    throwInterp s!"no relation registered under the recursive function name '{f}' \
      (register the `RelSchedule` whose `recFnName` is '{f}')"
  | some key => do
    let vals ← liftInterp ((valueArgs args).mapM (evalConstructorExpr env.funcs bindings))
    interpRel env key fuel' initSize sizeExpr vals rulePath

/-- A constrained producer for a hypothesis about some other relation (or a different mode of the
    same one), i.e. the emitted `ArbitrarySizedSuchThat.arbitrarySizedST`. Returns the produced
    outputs paired with the variables they bind.

    `x = e` / `e = x` are solved structurally, mirroring the built-in
    `ArbitrarySizedSuchThat α (fun x => x = e)` instance. -/
partial def interpConstrained (env : InterpEnv) (rel : RelSchedule) (hypExpr : HypothesisExpr)
    (vars : List Name) (initSize sizeExpr : Nat) (bindings : ValEnv) :
    Gen (List (Name × Val)) := do
  let (relName, args) := hypExpr
  let (outputs, inputs) ←
    liftInterp (splitHypothesis env.funcs bindings vars args (env.typeArgIndicesOf relName))
  if relName == ``Eq then
    -- Exactly one side is the unknown; the other side is already evaluated into `inputs`.
    match outputs, lastArgs 1 inputs with
    | [(_, u)], [v] => return [(u, v)]
    | _, _ =>
      throwInterp s!"cannot solve `{ppHypothesisExpr hypExpr}` for {vars}: the built-in equality \
        producer needs exactly one unknown side and one known side"
  else
    -- The derived instance is `fun size => aux_arb <specimen.fuel> size size`, so a fresh full
    -- fuel budget with `initSize = size = ` the dependency's size allocation.
    let s := if relName == rel.key.inductiveName then sizeExpr else initSize
    -- `typeArgs` must match what `stepDepKey?` recorded when the mode was derived. A monomorphised
    -- mode is registered as e.g. `MapContains[3]@(0:Attr, 1:QualifiedType)`; looking it up with a bare
    -- key misses it entirely, and the failure reads "no schedule or producer registered" for a mode
    -- that is right there — with `InterpEnv.check` reporting no issue, because it *is* typeArgs-aware.
    let key : SpecKey :=
      { inductiveName := relName, outputIndices := outputs.map Prod.fst, deriveSort := .Generator,
        typeArgs := renderedTypeArgs hypExpr }
    let vals ← interpRel env key env.fuel s s inputs
    if vals.length != outputs.length then
      throwInterp s!"{renderSpecKey key} returned {vals.length} value(s) but \
        `{ppHypothesisExpr hypExpr}` expects {outputs.length}"
    return (outputs.map Prod.snd).zip vals

/-- The schedule's conclusion: for a producer schedule, the outputs read off the constructor's
    conclusion. -/
partial def runEpilogue (env : InterpEnv) (bindings : ValEnv) (sort : ScheduleSort) :
    Gen (List Val) := do
  match sort with
  | .ProducerSchedule _ outputs => liftInterp (outputs.mapM (evalConstructorExpr env.funcs bindings))
  | .CheckerSchedule =>
    throwInterp "this is a checker schedule; v1 interprets producer schedules only"
  | .TheoremSchedule .. =>
    throwInterp "this is a theorem schedule; v1 interprets producer schedules only"

end

/-- Runs a spec as a generator at the requested `size`, mirroring the emitted entry point
    `fun size => aux_arb <specimen.fuel> size size`.

    `inputs` supplies one value per value-level input position (ascending); the result holds one
    value per value-level output position (ascending). -/
def InterpEnv.generate (env : InterpEnv) (key : SpecKey) (size : Nat)
    (inputs : List Val := []) : Gen (List Val) :=
  interpRel env key env.fuel size size inputs

/-- `InterpEnv.generate` for a spec named by its recursive function name. -/
def InterpEnv.generateVia (env : InterpEnv) (fnName : Name) (size : Nat)
    (inputs : List Val := []) : Gen (List Val) :=
  match env.keyOfFn? fnName with
  | some key => env.generate key size inputs
  | none => throwInterp s!"no relation registered under the recursive function name '{fnName}'"

/-- Runs exactly *one* constructor's schedule, with no backtracking over the alternatives.

    The debugging entry point: because nothing catches the error, a missing leaf or a malformed
    step surfaces verbatim instead of being absorbed as "this branch failed". -/
def InterpEnv.runCtorOnce (env : InterpEnv) (key : SpecKey) (ctorName : Name) (size : Nat)
    (inputs : List Val := []) : Gen (List Val) :=
  match env.relations[key]? with
  | none => throwInterp s!"no schedule registered for {renderSpecKey key}"
  | some rel =>
    match rel.ctorSchedule? ctorName with
    | none => throwInterp s!"{renderSpecKey key} has no schedule for constructor '{ctorName}'"
    | some sched => runCtor env rel ctorName env.fuel size size inputs sched

end Specimen.Interp
