import Lean
open Lean

initialize registerTraceClass `plausible.deriving.results

/-- Option to enable debug messages from Specimen -/
register_option specimen.debug : Bool := {
  defValue := false
  descr := "enable debug messages from Specimen"
}

/-- When true, the scheduler produces maximally many outputs per hypothesis step -/
register_option specimen.multiOutput : Bool := {
  defValue := false
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
  defValue := false
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
