import Lean
open Lean

initialize registerTraceClass `plausible.deriving.results

/-- Reports each pinned premise order as the deriver consumes it.

    Pinning is silent on both outcomes that matter: a pin that matches changes the schedule with no
    other visible sign, and a pin whose `SpecKey` does not match any mode the derivation mints is
    simply never found. The two are indistinguishable from the output otherwise — so a pin that
    silently does nothing reads exactly like a pin that worked. -/
initialize registerTraceClass `specimen.pinnedOrders

/-- Reports every constructor `deriveBestInductiveSchedule` leaves out of a mode, with the reason.

    A constructor is dropped in two ways — no schedule found, or an exception while deriving one — and
    both are silent: the generator simply lacks that rule. That is often legitimate (a rule with no
    viable schedule in this mode), but it is also where a bug hides, since a generator missing some of its
    rules still runs and still measures as if it were complete. Opt-in rather
    than a warning, because the search derives many modes speculatively, only to score candidate
    orderings, and their drops are noise. Turn it on with `set_option trace.specimen.droppedCtors true`. -/
initialize registerTraceClass `specimen.droppedCtors

/-- Option to enable debug messages from Specimen -/
register_option specimen.debug : Bool := {
  defValue := false
  descr := "enable debug messages from Specimen"
}

/-- When true, the scheduler produces maximally many outputs per hypothesis step -/
register_option specimen.multiOutput : Bool := {
  defValue := true
  descr := "allow multi-output production steps in derived generators"
}

/-- When true, derived **generators** are emitted against Basalt's generator algebra instead of
    `Plausible.Gen`: the body is polymorphic in a generator monad `G` with `Gen`, `Fail`,
    `FailWith Specimen.Exhaustion`, `Specimen.Backtrack` and `Specimen.MonoBacktrack`, its type is `G α`, and the instance emitted
    is `BacktrackGenFor` rather than `ArbitrarySizedSuchThat`. One derived body then elaborates at
    every such `G`, not only the one it runs at.

    Requires `import Specimen.Basalt` in the deriving file: the emitted code names Basalt's classes, and
    that module also supplies the bridge back to `ArbitrarySizedSuchThat`, so the `plausible` tactic and
    existing call sites run Basalt-derived generators unchanged.

    Generators only: enumerators and checkers keep their concrete fuel-indexed types.
    See `Docs/Specimen-Basalt-port.md`. -/
register_option specimen.plainBinds : Bool := {
  defValue := false
  descr := "emit a derived worker's binds and returns as `Bind.bind m fun x => k` and `Pure.pure e` \
    rather than `do` notation: the same code without the `do` elaborator's cost, and without the \
    trivial `match` on a variable a typed `do` binding elaborates to"
}

register_option specimen.emitBasalt : Bool := {
  defValue := false
  descr := "emit derived generators against Basalt's `Gen` algebra instead of `Plausible.Gen`"
}

/-- When true (with `specimen.emitBasalt`), `derive_mutual` proves each derived generator sound for its
    relation, as `#specimen_sound` does: `W.sound` next to each worker `W`. Requires
    `import Specimen.Correctness.SoundOf` in the deriving file. A generator whose proof does not close
    is still emitted, with a warning; a hand-written instance's law is a fact for the proofs when
    tagged `@[specimen_sound]`. -/
register_option specimen.emitSound : Bool := {
  defValue := false
  descr := "prove derived generators sound for their relations (needs Specimen.Correctness.SoundOf)"
}

/-- When true, `derive_mutual` reports each derived producer rule's rejection points: the checks,
    matches and required output shapes that can fail on a value the rule drew
    (`Specimen.Rejections`). -/
register_option specimen.reportRejections : Bool := {
  defValue := false
  descr := "report derived producers' rejection points"
}

/-- When true, `derive_mutual` compiles each spec's code in a task of its own, in parallel; the code
    and the order it is emitted in are as without it. -/
register_option specimen.parallelCodegen : Bool := {
  defValue := false
  descr := "compile derived specs' code in parallel tasks"
}

/-- When true, with `specimen.emitSound`, each block's proofs are split per worker into theorems for
    the induction's base and step, which Lean elaborates in parallel (as it does any `theorem`), and
    assembled by `Nat.rec`; the next components go on while they run. A proof that does not close is
    then an error of the file, rather than a warning that the block was not proved. -/
register_option specimen.parallelProofs : Bool := {
  defValue := false
  descr := "prove each derived block's workers as parallel theorems (with specimen.emitSound)"
}

/-- What `specimen.emitSound` runs on each derived component: its generators, as (worker, relation,
    output indices), and the soundness theorems of the generators derived so far. Set by
    `Specimen.Correctness.SoundOf`, which the deriver cannot import. -/
initialize specimenSoundHook :
    IO.Ref (Option (Array (Name × Name × List Nat) → Array Name → Elab.Command.CommandElabM Unit)) ←
  IO.mkRef none

/-- What `specimen.emitSound` runs on each derived component's checkers, as (worker, relation), with
the soundness theorems derived so far; first, the generators and enumerators of the same mutual block,
as for `specimenSoundHook`, to be proved sound with them. Set by `Specimen.Correctness.CheckSoundOf`. -/
initialize specimenCheckSoundHook :
    IO.Ref (Option (Array (Name × Name × List Nat) → Array (Name × Name) → Array Name →
      Elab.Command.CommandElabM Unit)) ←
  IO.mkRef none

/-- What `specimen.emitSound` runs on each derived component's enumerators, with the theorems derived
so far: their searches' laws. Set by `Specimen.Correctness.EnumSoundOf`. -/
initialize specimenEnumSoundHook :
    IO.Ref (Option (Array Name → Array Name → Elab.Command.CommandElabM Unit)) ←
  IO.mkRef none

/-- When true, a derived **generator** emitted against Basalt (`specimen.emitBasalt`) shares a rule's
    size budget among its size-consuming calls by drawing a split (`Specimen.SizeSplit.drawEven`: each
    call its floor, the remainder uniformly over its compositions) instead of handing each the quotient
    `size' / k`. Enumerators and checkers always divide. See `specimen.splitFloor`. -/
register_option specimen.sizeSplit : Bool := {
  defValue := false
  descr := "in Basalt generators, draw a split of the size budget among recursive calls"
}

/-- Under `specimen.sizeSplit`, the share of `size' / k` (per mille) each call is guaranteed before the
    remainder is split: 0 is the uniform split, 1000 spreads only what the quotient leaves. -/
register_option specimen.splitFloor : Nat := {
  defValue := 0
  descr := "under specimen.sizeSplit, per-mille of the equal share guaranteed to each call"
}

/-- Under `specimen.sizeSplit`, floor functions for relations' recursive calls, as
    `"Rel:floorFn,…"`: a rule's call to `Rel` is guaranteed `floorFn` at the call's inputs, the least
    size it can succeed at, and the rest of the size is split uniformly. -/
register_option specimen.splitFloors : String := {
  defValue := ""
  descr := "under specimen.sizeSplit, per-relation floor functions of a call's inputs: Rel:fn,…"
}

/-- When true (with `specimen.emitBasalt`), `derive_mutual` proves each derived generator complete:
    `W.complete` (every derivation is produced at every large enough size) and a
    `BacktrackGenForComplete` instance, relative to the `BacktrackGenForComplete` and
    `ArbitrarySizedComplete` instances of what it calls. Its instances then run their workers at fuel
    `size + 1` rather than `specimen.fuel`. Requires `import Specimen.Correctness.CompleteOf`. -/
register_option specimen.emitComplete : Bool := {
  defValue := false
  descr := "prove derived generators complete (needs Specimen.Correctness.CompleteOf)"
}

register_option specimen.deferComplete : Bool := {
  defValue := false
  descr := "with specimen.emitComplete, record each component's generators instead of proving them \
    complete, for `#specimen_complete_*` commands in files that import this one: completeness split \
    across files, which Lean checks in parallel (within a file, its kernel checks run one at a time)"
}

register_option specimen.completeDropUnreachable : Bool := {
  defValue := false
  descr := "the completeness parts' walks drop the branches that cannot return the case's value \
    (`basalt.walk.dropUnreachable`)"
}

register_option specimen.reachExtended : Bool := {
  defValue := false
  descr := "`reach_close` also: fixes what a check is about from a premise or its negation in context, \
    rewrites a `match` with a premise either way round, and accepts a search over a type's unconstrained \
    values (`CheckerSearchAll`). `specimen_complete_case` turns it on only for a case the plain search \
    does not close, which pays nothing for the cases it does"
}

register_option specimen.reachSimpAll : Bool := {
  defValue := true
  descr := "`reach_close` tries `simp_all` last on a check's premise (costly; rarely what closes it)"
}

register_option specimen.searchSeparately : Bool := {
  defValue := false
  descr := "with specimen.completeAllSorts, the completeness blocks do not prove the enumerators' \
    searches (`searchHits`): `#specimen_prove_all_but` does, before them"
}

register_option specimen.completeAllSorts : Bool := {
  defValue := false
  descr := "with specimen.emitComplete, prove the derived enumerators and checkers complete too, not \
    only the generators: each enumerator's `complete` and its searches' `searchHits`/`searchTotal`, each \
    checker's `complete`, and their instances' `EnumForComplete`, `EnumForSearch` and `DecOptComplete`"
}

register_option specimen.splitMinWorkers : Nat := {
  defValue := 4
  descr := "`#specimen_prove_setup`: the components with at least this many workers are split across     `#specimen_prove_part` files; the rest are proved by the setup"
}

register_option specimen.skipFailedParts : Bool := {
  defValue := false
  descr := "a slice of a component's completeness parts declares only the parts it proves, each \
    proved in a task of its own; the rest are left to `#specimen_prove_finish`, in a file that \
    imports more (no part is admitted)"
}

register_option specimen.admitFailedParts : Bool := {
  defValue := false
  descr := "a completeness part whose proof fails (or runs out of heartbeats) is admitted with `sorry` \
    and a warning rather than an error, so that the file still compiles (`lean -o` writes no `.olean` \
    for a file with errors); the theorems that use it then depend on `sorryAx`, as they would anyway"
}

register_option specimen.deferSound : Bool := {
  defValue := false
  descr := "with specimen.emitSound, record the soundness proofs' steps instead of running them, for \
    `#specimen_sound_replay` in a file that imports this one (soundness proved alongside the files \
    that prove completeness, rather than before them)"
}

/-- What `specimen.emitComplete` runs on each derived component's generators, as (worker, relation,
    output indices). Set by `Specimen.Correctness.CompleteOf`. -/
initialize specimenCompleteHook :
    IO.Ref (Option (Array (Name × Name × List Nat) → Elab.Command.CommandElabM Unit)) ←
  IO.mkRef none

/-- Fuel for derived generators (termination device). High values are fine; only decrease for testing. -/
register_option specimen.fuel : Nat := {
  defValue := 10000
  descr := "fuel (termination budget) for derived generators/enumerators/checkers"
}

/-- When true, derive_mutual automatically derives dependencies for other inductives
    referenced in the specs' constructors before emitting the mutual block. -/
register_option specimen.autoDeriveDeps : Bool := {
  defValue := true
  descr := "automatically derive dependency instances in derive_mutual"
}

/-- When true, derive_mutual emits a rich HTML widget in the infoview with interactive
    schedule details. When false, only plain text output is emitted (faster). -/
register_option specimen.richOutput : Bool := {
  defValue := true
  descr := "emit rich HTML widget output in derive_mutual (disable for faster builds)"
}

/-- Controls plain-text schedule output verbosity in derive_mutual.
    0 = off, 1 = one-line per spec (name + quality), 2 = full schedules for poor-quality specs,
    3 = full schedules for all specs. Useful for LLM tooling and non-IDE workflows. -/
register_option specimen.textOutput : Nat := {
  defValue := 0
  descr := "plain-text output verbosity (0=off, 1=summary, 2=problems, 3=full)"
}

register_option specimen.prefixSearch : Bool := {
  defValue := false
  descr := "search premise orders with the prefix explorer (every order reachable, committed prefixes, \
    sleep-set reduction) instead of the insertion tree"
}

register_option specimen.cycleFixpoint : Nat := {
  defValue := 0
  descr := "after deriving, re-derive the modes of each cycle (and its root), whose schedules were \
    chosen against a placeholder for a mode then in progress, with every other mode at its derived \
    score, up to this many rounds or until no schedule's score changes (0: off)"
}

register_option specimen.noncomputableDefs : Bool := {
  defValue := false
  descr := "emit the derived definitions and instances `noncomputable` (no compiled code; for \
    checking proofs only)"
}

register_option specimen.prefixFullFootprint : Bool := {
  defValue := false
  descr := "in the prefix explorer, take two premises as independent when they share no unbound \
    variable anywhere in their arguments, not only when both are plain relations"
}

/-- Maximum number of hypothesis orderings to evaluate per constructor before
    stopping the search. Guards against combinatorial explosion on relations
    with many hypotheses. -/
register_option specimen.searchLimit : Nat := {
  defValue := 200000
  descr := "max hypothesis orderings to evaluate per constructor during schedule search"
}

/-- When true, a derived **generator** tests each constructor's leading input pattern-matches before
    handing the constructor list to `backtrack`, and drops the constructors that cannot match these inputs.

    A dropped constructor is one whose branch would fail at its first step on every run with these
    inputs, so removing it leaves the output distribution unchanged — weights are *not* recounted after
    the filter. The guard is built from each branch's own leading `match`es (with bound variables replaced
    by wildcards), so it can only be weaker than the branch's test and never drops a branch that could
    succeed. The gain is in relations whose constructors split on an input, such as Cedar's `HasType`;
    where every constructor can match any input, as in STLC and BST, the filter keeps them all. -/
register_option specimen.dispatchInputs : Bool := {
  defValue := true
  descr := "in derived generators, skip constructors whose leading input pattern cannot match"
}

/-- When true, all of Specimen's informational derivation output is suppressed:
    the `Try this:` suggestion popups from the single-derive commands
    (`derive_checker` / `derive_generator` / `derive_generator_multi` /
    `derive_enumerator` / `derive_enum`) as well as the HTML widget and
    plain-text schedule reports from `derive_mutual`. The typeclass instances
    are still installed exactly as before; only the console/infoview output is
    skipped. Useful in batch builds where hundreds of derives would otherwise
    flood the console with tens of thousands of lines. -/
register_option specimen.silent : Bool := {
  defValue := false
  descr := "suppress all informational derivation output (Try this: suggestions, derive_mutual widgets/text)"
}

/-- When true, each constructor's weight function is reduced under the runtime `size` binder
    at elaboration time, so the generated code carries a small residual expression in `size`
    rather than a full weight-function call. Reduction needs the weight and modifier arguments
    to be kernel-reducible; any failure falls back to the un-reduced call. -/
register_option specimen.precomputeWeights : Bool := {
  defValue := true
  descr := "partially evaluate constructor weight functions under the size binder at elaboration time"
}

/-- Whether the `specimen`/`specimen_test` shrinker attempts to minimize counterexamples. -/
register_option specimen.shrink : Bool := {
  defValue := true
  descr := "enable counterexample shrinking in specimen_test / specimen"
}

/-- How many shrink candidates to consider per step. Caps each variable's `Shrinkable.shrink`
    list, and so the jointly-constrained cartesian products built from them, bounding both
    candidate generation and the `DecOpt` re-checks. Lower is faster but less thorough. -/
register_option specimen.shrinkBreadth : Nat := {
  defValue := 8
  descr := "max shrink candidates considered per variable/step (bounds cartesian products)"
}

/-- Maximum number of greedy shrink steps (descent depth) per attempt. -/
register_option specimen.shrinkDepth : Nat := {
  defValue := 100
  descr := "max greedy shrink steps (descent depth) per counterexample"
}

/-- Seed for the random draws `specimen_test` and the `specimen` tactic make.

    Zero means draw a seed from the ambient RNG, so interactive use varies from run to run. Any
    other value fixes the stream, which is what a test file wants: the same draws every run, so a
    pathological draw is either always present or never, rather than appearing at random. The seed
    a run used is reported alongside a counterexample, so a varying run can be reproduced by
    setting this option to it. -/
register_option specimen.testSeed : Nat := {
  defValue := 0
  descr := "seed for `specimen_test` draws (0 draws a seed from the ambient RNG)"
}

/-- Budget in milliseconds for one `specimen_test` or `specimen` invocation, zero meaning no
    budget.

    Wall clock rather than a step count, because the test loop runs as a plain `IO` action through
    Lean's IR interpreter, where neither the heartbeat limit nor `maxRecDepth` reaches it. A step
    count would have to be threaded through the generator combinators, which every derived
    generator calls at runtime, and the check would cost more than the budget is worth.

    The default is two orders of magnitude above a normal invocation, so it marks a generator that
    has run away rather than one that is merely slow on a loaded machine. Exceeding it is reported
    as an error naming the proposition, the budget and the seed. -/
register_option specimen.testTimeoutMs : Nat := {
  defValue := 120000
  descr := "budget in ms for one `specimen_test` invocation (0 for no budget)"
}

/-- When true, `derive_mutual` logs where its time went: a per-phase breakdown (schedule
    search, SCC condensation, constraints, codegen, widget/text, Lean's elaboration of the
    emitted block) plus a codegen-versus-pretty-printing split. Diagnostic only. -/
register_option specimen.reportPhaseTimers : Bool := {
  defValue := false
  descr := "log per-phase timings for derive_mutual"
}

/-- Global flag for enabling/disabling debug messages -/
def globalDebugFlag : Bool := false

/-- Conditional debug trace for pure contexts. Use as `let _ := schedTrace "msg"`. -/
macro "schedTrace " msg:interpolatedStr(term) : term =>
  `(if globalDebugFlag then dbg_trace $msg; () else ())

/-- Determines whether the `specimen.debug` Option flag is set -/
def inDebugMode [Monad m] [MonadOptions m] : m Bool := do
  let opts ← getOptions
  return Lean.Option.get opts specimen.debug

/-- Determines whether the `specimen.silent` Option flag is set -/
def inSilentMode [Monad m] [MonadOptions m] : m Bool := do
  let opts ← getOptions
  return Lean.Option.get opts specimen.silent

/-- Performs a monadic `action` if a flag value is set -/
def withDebugFlag [Monad m] [MonadOptions m] [MonadWithOptions m] [MonadLog m] [AddMessageContext m] (flag : Bool) (action : m Unit) : m Unit := do
  withOptions (fun opts => opts.set `specimen.debug flag) do
    if (← inDebugMode) then do
      action
      logInfo ""

/-- Appends `line` to the file `SPECIMEN_TIMER_LOG` names, if set, and flushes. Lean holds a command's
    standard streams until the command ends, so this is how a long derivation can be watched while it
    runs. -/
def timerLog (line : String) : IO Unit := do
  if let some path ← IO.getEnv "SPECIMEN_TIMER_LOG" then
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn line
    h.flush

/-- Time and count of each labelled step of the proof in progress (`timeIn`, the `timed` tactic),
    reported to the file `SPECIMEN_TIMER_LOG` names. -/
initialize tacticTimes : IO.Ref (Array (String × Nat × Nat)) ← IO.mkRef #[]

/-- Whether `timeIn` records (`SPECIMEN_TACTIC_TIMES` set). Off by default: the totals are shared by
every thread, and proofs elaborated in parallel would mostly wait on each other for them. -/
initialize tacticTimesOn : Bool ← return (← IO.getEnv "SPECIMEN_TACTIC_TIMES").isSome

/-- Run `x`, adding its time to `label`'s. -/
def timeIn [Monad m] [MonadLiftT IO m] [MonadFinally m] (label : String) (x : m α) : m α := do
  unless tacticTimesOn do return ← x
  let t0 ← (IO.monoNanosNow : IO Nat)
  try x
  finally
    let dt := (← (IO.monoNanosNow : IO Nat)) - t0
    (tacticTimes.modify fun a =>
      match a.findIdx? (·.1 == label) with
      | some i => a.modify i fun (k, v, c) => (k, v + dt, c + 1)
      | none => a.push (label, dt, 1) : IO Unit)

/-- `timed "label" tac`: `tac`, its time added to `label`'s. -/
syntax "timed " str ppSpace tactic : tactic

open Elab Tactic in
elab_rules : tactic | `(tactic| timed $l:str $t:tactic) => timeIn l.getString (evalTactic t)

/-- Report and reset the totals. -/
def reportTacticTimes (what : String) : IO Unit := do
  let a ← tacticTimes.get
  tacticTimes.set #[]
  unless a.isEmpty do
    timerLog s!"    {what} by step: {", ".intercalate (a.toList.map fun (k, v, c) => s!"{k} {v / 1000000} ms ×{c}")}"

/-- `#specimen_tactic_times`: the totals of `timeIn` so far (`SPECIMEN_TACTIC_TIMES`), to the timer
log, reset. -/
elab "#specimen_tactic_times" : command => do reportTacticTimes "all"
