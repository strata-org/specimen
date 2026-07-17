import Specimen

open Specimen.Tactic

-- A simple inductive relation to test (using .succ.succ for structural pattern matching in checkers)
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ : Even n → Even n.succ.succ

-- Test 1: true property — should pass
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true) in
specimen_test (min := 1, max := 10) (∀ n : Nat, Even n → Even (n + 2))

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

-- -- False property: Add3 a b c → Add3 a c b (nondeterministic counterexample values)
-- /-- error: Found counter-example! -/
-- #guard_msgs (error, substring := true) in
specimen_test (∀ a b c : Nat, Add3 a b c → Add3 a c b)

-- Test 5: Multiple hypotheses — true property that previously failed due to checker soundness bug
/-- tests passed -/
#guard_msgs (info, substring := true) in
specimen_test (∀ n : Nat, Even n → Even (n + 2) → Even (n + 4) → Even (n + 6))

-- Test 6: Shrinking produces minimal counterexample
-- Even n → Even (n + 1) is false; smallest counterexample is n = 0
/--
error: Found counter-example!
  n : Nat := 0
-/
#guard_msgs (error, drop info, substring := true) in
specimen_test (∀ n : Nat, Even n → Even (Nat.succ n))

-- Test 7: Multi-variable shrinking — Add3 a b c → Add3 a c b
-- Shrinking respects the Add3 hypothesis constraint (b ≠ c guaranteed in counterexample)
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true) in
specimen_test (∀ a b c : Nat, Add3 a b c → Add3 a c b)

-- Test 8: `specimen` tactic on a true property — tests then admits (uses sorry)
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true, drop warning) in
example : ∀ n : Nat, Even n → Even (n + 2) := by
  specimen

-- Test 9: `specimen` tactic reverts local hypotheses into the goal
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true, drop warning) in
example (n : Nat) (h : Even n) : Even (n + 2) := by
  specimen

-- Test 10: `specimen` tactic finds a counterexample
/--
error: Found counter-example!
  n : Nat := 0
-/
#guard_msgs (error, drop info, substring := true, drop warning) in
example : ∀ n : Nat, Even n → Even (Nat.succ n) := by
  specimen

-- Test 11: `specimen` tactic with size config
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
example : ∀ a b c : Nat, Add3 a b c → Add3 a c b := by
  specimen (min := 10, max := 20)
