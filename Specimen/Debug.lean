import Lean
open Lean

initialize registerTraceClass `plausible.deriving.results

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
