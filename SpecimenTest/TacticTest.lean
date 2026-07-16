import Specimen

open Specimen.Tactic

-- A simple inductive relation to test (using .succ.succ for structural pattern matching in checkers)
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ : Even n → Even n.succ.succ

-- Test 1: true property — should pass
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true) in
specimen_test (∀ n : Nat, Even n → Even (n + 2))

-- Test 2: false property — should find counterexample
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true) in
specimen_test (∀ n : Nat, Even n → Even (n + 1))

-- Test 3: multi-variable relation
inductive Add3 : Nat → Nat → Nat → Prop where
  | zero_l : Add3 Nat.zero n n
  | succ_l : Add3 a b c → Add3 (a.succ) b (c.succ)

-- True property with 3 variables
/-- tests passed -/
#guard_msgs (info, substring := true) in
specimen_test (∀ a b c : Nat, Add3 a b c → Add3 a b c)

-- False property: Add3 a b c → Add3 a c b (nondeterministic counterexample values)
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true) in
specimen_test (∀ a b c : Nat, Add3 a b c → Add3 a c b)

-- Test 5: Multiple hypotheses — true property that previously failed due to checker soundness bug
/-- tests passed -/
#guard_msgs (info, substring := true) in
specimen_test (∀ n : Nat, Even n → Even (n + 2) → Even (n + 4) → Even (n + 6))
