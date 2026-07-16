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

-- Test 1: specimen_test on a true property — should pass
specimen_test (∀ n : Nat, Even n → Even (n + 2))

-- Test 2: A false property — should find counterexamples
-- "Even n implies Even (n + 1)" is false (e.g., Even 2 but not Even 3)
-- Uncomment to verify: specimen_test (∀ n : Nat, Even n → Even (n + 1))
-- Expected: "Found N counter-example(s) in 100 tests"

