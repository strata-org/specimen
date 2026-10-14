import Specimen

/-!
# `trace.specimen.droppedCtors` says which constructors a mode lost, and why

`AllBelow.step` has a `∀` premise no schedule can discharge, so the checker mode is derived without it.
That used to be silent — the checker simply lacked the rule. With the trace on, the drop is reported.
-/

inductive AllBelow : Nat → Prop where
  | zero : AllBelow 0
  | step : ∀ n, (∀ m, m < n → AllBelow m) → AllBelow n

set_option trace.specimen.droppedCtors true in
/-- trace: [specimen.droppedCtors] dropped AllBelow.step from AllBelow[] as Schedules.DeriveSort.Checker -/
#guard_msgs (trace, drop info, drop warning, substring := true) in
derive_mutual checker (fun n => AllBelow n)
