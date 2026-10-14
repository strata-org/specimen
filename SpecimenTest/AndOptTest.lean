import Specimen.DecOpt

/-!
# `andOpt` is Kleene's strong conjunction

`false` annihilates conjunction even when the other operand is inconclusive: the conjunction is false on
account of the definite operand alone. Reporting "cannot decide" there would make an enclosing checker
inconclusive about something it can refute. The full truth table, both operand orders.
-/

open Plausible DecOpt

private def showV : Except GenError Bool → String
  | .ok b => toString b
  | .error _ => "?"

private def vals : List (Except GenError Bool) := [.ok true, .ok false, .error (.genError "out of fuel")]

/-- info: [["true", "false", "?"], ["false", "false", "false"], ["?", "false", "?"]] -/
#guard_msgs in
#eval vals.map fun a => vals.map fun b => showV (andOpt a b)

-- `andOptList` inherits it: one definite `false` anywhere decides the conjunction.
/-- info: ["false", "false", "?"] -/
#guard_msgs in
#eval [ [.error (.genError "out of fuel"), .ok false], [.ok false, .error (.genError "out of fuel")],
        [.error (.genError "out of fuel"), .ok true] ].map fun l => showV (andOptList l)
