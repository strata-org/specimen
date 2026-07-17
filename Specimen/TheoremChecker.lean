import Plausible.Gen
import Plausible.Shrinkable

open Plausible

/-! # Theorem testing infrastructure

Types and combinators for running and shrinking theorem tests.
The compiled theorem schedule produces a generator of the full variable tuple.
We wrap this in a `forAllShrinkChecked` combinator that:
- Generates the tuple (using the schedule — constrained generation)
- Checks the conclusion
- On failure: shrinks each variable, re-checking hypotheses after each shrink
-/

namespace Specimen

/-- Returns `true` iff the result is `.ok true`. Used by compiled `validShrinks` functions. -/
def isOkTrue : Except GenError Bool → Bool
  | .ok true => true
  | _ => false

/-- Fair round-robin interleave of multiple lists.
    `interleave [[a,b,c], [1,2], [x,y,z,w]] = [a, 1, x, b, 2, y, c, z, w]` -/
partial def interleave (lists : List (List α)) : List α :=
  let rec go (remaining : List (List α)) (acc : List α) : List α :=
    let step := remaining.filterMap fun
      | [] => none
      | h :: t => some (h, t)
    match step with
    | [] => acc.reverse
    | _ =>
      let heads := step.map Prod.fst
      let tails := step.map Prod.snd
      go tails (heads.reverse ++ acc)
  go lists []

/-- Result of testing one sample of a theorem property.
    Parameterized by the counterexample type (typically a tuple of the generated variables). -/
inductive SpecimenResult (α : Type) where
  | passed
  | failed (counterexample : α)
  | discarded (reason : GenError)
  deriving Repr, Inhabited

/-- A theorem checker bundles:
    - `generate`: produces the full variable tuple (constrained by hypotheses)
    - `checkConclusion`: given a tuple, checks if the conclusion holds
    - `validShrinks`: given a counterexample and fuel, produces smaller candidates
      that still satisfy all hypotheses AND still violate the conclusion.
      Interleaves shrinking with hypothesis checking to short-circuit early. -/
structure TheoremProperty (α : Type) where
  generate : Nat → Gen α
  checkConclusion : α → Nat → Bool
  validShrinks : α → Nat → List α

/-- Run a single test sample: generate a tuple, check the conclusion. -/
def TheoremProperty.runOnce (prop : TheoremProperty α) (size : Nat) (fuel : Nat)
    : Gen (SpecimenResult α) := do
  tryCatch
    (do
      let x ← prop.generate size
      if prop.checkConclusion x fuel then
        return .passed
      else
        return .failed x)
    (fun e => return .discarded e)

/-- Shrink a counterexample: `validShrinks` already produces only candidates
    that satisfy hypotheses and violate the conclusion (short-circuiting internally).
    We greedily take the first valid shrink and recurse until fixpoint. -/
partial def TheoremProperty.shrinkCounterexample (prop : TheoremProperty α) (cex : α) (fuel : Nat)
    : α :=
  match prop.validShrinks cex fuel with
  | smaller :: _ => prop.shrinkCounterexample smaller fuel
  | [] => cex

/-- Run the full test loop: sample `numTests` times, shrink on failure. -/
def TheoremProperty.run (prop : TheoremProperty α) (numTests : Nat := 100)
    (maxSize : Nat := 100) (doShrink : Bool := true) : IO (SpecimenResult α) := do
  let mut discards : Nat := 0
  for i in List.range numTests do
    let size := (i + 1) * maxSize / numTests
    let result ← Gen.run (prop.runOnce size size) size
    match result with
    | .passed => continue
    | .discarded _ => discards := discards + 1
    | .failed cex =>
      if doShrink then
        let shrunk := prop.shrinkCounterexample cex size
        return .failed shrunk
      else
        return .failed cex
  if discards > numTests / 2 then
    return .discarded (.genError s!"too many discards ({discards}/{numTests})")
  return .passed

/-- Run a compiled theorem checker (Nat → Nat → Nat → Gen (Except GenError Bool)) directly.
    Interprets: `.ok true` = passed, `.ok false` = counterexample, exception = discard.
    Returns `SpecimenResult Unit` (no counterexample data yet — just pass/fail/discard). -/
def runTheoremTests (checker : Nat → Nat → Nat → Gen (Except GenError Bool))
    (numTests : Nat := 100) (maxSize : Nat := 100) : IO (SpecimenResult Unit) := do
  let mut discards : Nat := 0
  for i in List.range numTests do
    let size := (i + 1) * maxSize / numTests
    let result ← try
      let r ← Gen.run (checker size size size) size
      pure (some r)
    catch _ => pure none
    match result with
    | some (.ok true) => continue
    | some (.ok false) => return .failed ()
    | some (.error e) => discards := discards + 1; let _ := e
    | none => discards := discards + 1
  if discards > numTests / 2 then
    return .discarded (.genError s!"too many discards ({discards}/{numTests})")
  return .passed

end Specimen
