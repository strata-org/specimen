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
/--
info: specimen_test: 6 derived specs, 6 components
---
info: 100 tests passed (0 discarded)
-/
#guard_msgs in
specimen_test (∀ n : Nat, Even n → Even (n + 2))

-- Test 2: false property — should find counterexample with variable names and types
-- Uncomment to see output:

/--
error: Found counter-example!
  n : Nat := 0
(0 tests passed, 0 discarded)
-/
#guard_msgs(error, drop info) in
specimen_test (∀ n : Nat, Even n → Even (n + 1))
