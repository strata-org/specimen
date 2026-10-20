import Specimen.EnumeratorCombinators

/-!
# One classification of inconclusive errors

The checker path (`lazyListBacktrackOpt`, behind `enumeratingOpt`) reads every error the generator calls
inconclusive as *inconclusive*: the search did not finish, so the answer is `error`, not `ok false`. The
classifier is shared, so a message such as `"Gen.runUntil: Out of attempts"` cannot be a definite
refutation on one path and inconclusive on another.
-/

open EnumeratorCombinators Plausible

private def noneTrue : Nat → Except GenError Bool := fun _ => .ok false

private def verdict (e : GenError) : String :=
  match lazyListBacktrackOpt (.lcons (.error e) (Thunk.pure .lnil)) noneTrue false with
  | .ok b => s!"ok {b}"
  | .error _ => "inconclusive"

-- Every message the generator treats as inconclusive is inconclusive here too.
/-- info: ["inconclusive", "inconclusive", "inconclusive"] -/
#guard_msgs in
#eval [ "Specimen: out of fuel (termination limit reached)", "out of fuel", "Gen.runUntil: Out of attempts" ].map
  fun m => verdict (.genError m)

-- A definitive failure stays definitive: nothing was found and nothing was cut short.
/-- info: "ok false" -/
#guard_msgs in
#eval verdict (.genError "some branch does not apply")

-- And the classifiers agree on every message above.
/-- info: true -/
#guard_msgs in
#eval [ "Specimen: out of fuel (termination limit reached)", "out of fuel", "Gen.runUntil: Out of attempts",
        "some branch does not apply" ].all fun m =>
  isInconclusiveError (.genError m) == Gen.GenError.isInconclusive (.genError m)
