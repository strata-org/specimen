import Specimen
import Plausible
import SpecimenTest.CommonDefinitions.STLCDefinitions
import Specimen.Scoring

open Specimen.Tactic
open Plausible

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

-- False property: Add3 a b c → Add3 a c b (nondeterministic counterexample values)
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true) in
specimen_test (min := 1000) (∀ a b c : Nat, Add3 a b c → Add3 a c b)

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

-- Test 8: `specimen` tactic on a true property — diagnostic, leaves goal open
-- (does NOT prove/admit; `sorry` here just discharges the goal for the test)
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true, drop warning) in
example : ∀ n : Nat, Even n → Even (n + 2) := by
  specimen
  sorry

-- Test 9: `specimen` tactic includes local hypotheses in the tested proposition
/-- info: 100 tests passed (0 discarded) -/
#guard_msgs (info, drop info, substring := true, drop warning) in
example (n : Nat) (h : Even n) : Even (n + 2) := by
  specimen
  sorry

-- Test 10: `specimen` tactic finds a counterexample
/--
error: Found counter-example!
  n : Nat := 0
-/
#guard_msgs (error, drop info, substring := true, drop warning) in
example : ∀ n : Nat, Even n → Even (Nat.succ n) := by
  specimen
  sorry

-- Test 11: `specimen` tactic with size config
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
example : ∀ a b c : Nat, Add3 a b c → Add3 a c b := by
  specimen (min := 10, max := 20)
  sorry

-- === A: Leq antisymmetry (false) — jointly constrained pair, high min ===
inductive Leq : Nat → Nat → Prop where
  | zero : Leq 0 n
  | succ : Leq m n → Leq m.succ n.succ

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
specimen_test (min := 100) (∀ a b : Nat, Leq a b → Leq b a)

-- === B: List append commutativity (false) — joint list constraint ===
inductive Appended : List Nat → List Nat → List Nat → Prop where
  | nil : Appended [] ys ys
  | cons : Appended xs ys zs → Appended (x :: xs) ys (x :: zs)

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
specimen_test (min := 4) (∀ xs ys zs : List Nat, Appended xs ys zs → Appended ys xs zs)

-- === C: Tree membership bug (false) — tree-valued counterexample ===
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
  deriving Repr, Arbitrary, Shrinkable

inductive Elem : Nat → Tree → Prop where
  | here  : Elem x (.node l x r)
  | left  : Elem x l → Elem x (.node l y r)
  | right : Elem x r → Elem x (.node l y r)

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
specimen_test (∀ (x : Nat) (t : Tree), Elem x t → Elem x.succ t)

-- === D: STLC type preservation with a buggy step relation ===
-- `typing` and `lookup` come from SpecimenTest.CommonDefinitions.STLCDefinitions.
-- The `step` relation below has a DELIBERATE BUG in its beta rule: `App (Abs τ e1) e2`
-- should reduce by substituting `e2` for the bound variable in `e1`, but it just drops
-- the argument and returns `e1`. That breaks type preservation whenever `e1` mentions
-- the bound variable (e.g. `App (Abs Nat (Var 0)) (Const 0)` steps to the free `Var 0`).
--
-- Preservation: a well-typed term that steps stays well-typed — FALSE given the buggy step.
--
-- NOTE: currently WIP — generating a well-typed term together with its type (both `e` and
-- `τ` as outputs of `typing`) hits a codegen mismatch in the theorem scheduler. Left here
-- (commented) to experiment with. Add `import SpecimenTest.CommonDefinitions.STLCDefinitions`
-- at the top to use `typing`/`type`/`term`.
--
inductive step : term → term → Prop where
  | AppAbs : ∀ τ e1 e2, step (.App (.Abs τ e1) e2) e1            -- BUG: no substitution
  | App1   : ∀ e1 e1' e2, step e1 e1' → step (.App e1 e2) (.App e1' e2)
  | Add1   : ∀ e1 e1' e2, step e1 e1' → step (.Add e1 e2) (.Add e1' e2)
  | Add2   : ∀ e1 e2 e2', step e2 e2' → step (.Add e1 e2) (.Add e1 e2')

deriving instance DecidableEq for term, type
deriving instance Enum for type

set_option specimen.richOutput true in
set_option specimen.shrink true in
set_option specimen.scoreType "Scoring.UniformDensityScore" in
specimen_test (min:=0, max:=15, tests := 1) (∀ (e : term) (τ : type) (e' : term),
  typing [] e τ → step e e' → typing [] e' τ)
