import Specimen

open Specimen.Tactic

-- Simple test: BST property
inductive BST : Nat → Nat → List Nat → Prop where
  | nil : BST lo hi []
  | cons (x : Nat) (left right : List Nat) :
    lo ≤ x → x ≤ hi →
    BST lo x left → BST x hi right →
    BST lo hi (left ++ [x] ++ right)

-- A simple inductive relation to test
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ : Even n → Even (n + 2)

-- Test 1: true property — should pass
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true) in
specimen_test (∀ n : Nat, Even n → Even (n + 2))

-- Test 2: false property — should find counterexample with variable names and types
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true) in
specimen_test (∀ n : Nat, Even n → Even (n + 1))

-- Test 3: multi-variable — a relation with three Nat arguments
inductive Add3 : Nat → Nat → Nat → Prop where
  | zero_l : Add3 0 n n
  | succ_l : Add3 a b c → Add3 (a + 1) b (c + 1)

-- True property with 3 variables
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true) in
specimen_test (∀ a b c : Nat, Add3 a b c → Add3 a b c)

-- False property: Add3 a b c → Add3 a c b (nondeterministic counterexample values)
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true) in
specimen_test (∀ a b c : Nat, Add3 a b c → Add3 a c b)
