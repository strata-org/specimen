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

/-- Global flag for enabling/diabling debug messages -/
def globalDebugFlag : Bool := false

/-- Determines whether the `specimen.debug` Option flag is set -/
def inDebugMode [Monad m] [MonadOptions m] : m Bool := do
  let opts ← getOptions
  return Lean.Option.get opts specimen.debug

/-- Performs a monadic `action` if a flag value is set -/
def withDebugFlag [Monad m] [MonadOptions m] [MonadWithOptions m] [MonadLog m] [AddMessageContext m] (flag : Bool) (action : m Unit) : m Unit := do
  withOptions (fun opts => opts.set `specimen.debug flag) do
    if (← inDebugMode) then do
      action
      logInfo ""
