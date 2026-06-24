import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker

/-!
# Regression test for issue #38: missing typeclass constraints for polymorphic dependencies

When a generator depends on a checker sharing a type parameter, the generator must
propagate the checker's constraints. Previously hardcoded; now computed bottom-up.
-/

open Plausible

-- ============================================================
-- Test 1: Basic — checker with Eq on type param propagates DecidableEq
-- ============================================================

inductive MyContains {α : Type} : α → List α → Prop where
  | here : ∀ x rest, MyContains x (x :: rest)
  | there : ∀ x y rest, MyContains x rest → MyContains x (y :: rest)

inductive NotIn {α : Type} : α → List α → Prop where
  | mk : ∀ x xs, ¬ MyContains x xs → NotIn x xs

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#guard_msgs(drop info) in
derive_mutual
  checker (fun α x xs => @MyContains α x xs),
  generator (fun α xs => ∃ x, @NotIn α x xs)

-- Generator only needs [Arbitrary α, DecidableEq α], NOT [Enum α]
example : ∀ [Plausible.Arbitrary α] [DecidableEq α],
    ArbitrarySizedSuchThat α (fun x => @NotIn α x xs) := inferInstance

-- ============================================================
-- Test 2: Compound type — generating List α propagates Arbitrary from List's instance
-- ============================================================

inductive AllEq {α : Type} : α → List α → Prop where
  | nil : ∀ x, AllEq x []
  | cons : ∀ x xs, AllEq x xs → AllEq x (x :: xs)

inductive HasAllEq {α : Type} : List α → Prop where
  | mk : ∀ x xs, AllEq x xs → HasAllEq (x :: xs)

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#guard_msgs(drop info) in
derive_mutual
  checker (fun α x xs => @AllEq α x xs),
  generator (fun α => ∃ xs, @HasAllEq α xs)

-- Generator needs [Arbitrary α, DecidableEq α] (Arbitrary for generating x, DecidableEq for Eq checks)
example : ∀ [Plausible.Arbitrary α] [DecidableEq α],
    ArbitrarySizedSuchThat (List α) (fun xs => @HasAllEq α xs) := inferInstance

-- ============================================================
-- Test 3: Generating List α unconstrainedly requires [Arbitrary α] transitively
-- ============================================================

inductive ListHead {α : Type} : α → List α → Prop where
  | mk : ∀ x xs, ListHead x (x :: xs)

inductive HasHead {α : Type} : List α → Prop where
  | mk : ∀ (xs : List α) (x : α), ListHead x xs → HasHead xs

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#guard_msgs(drop info) in
derive_mutual
  checker (fun α x xs => @ListHead α x xs),
  generator (fun α => ∃ ys, @HasHead α ys)

-- The generator must discover [Arbitrary α] from generating List α unconstrainedly
example : ∀ [Plausible.Arbitrary α] [DecidableEq α],
    ArbitrarySizedSuchThat (List α) (fun ys => @HasHead α ys) := inferInstance

-- ============================================================
-- Test 4: Custom class — manual DecOpt instance with [MyHashable α] propagates up
-- ============================================================

class MyHashable (α : Type) where
  myHash : α → UInt64

inductive HashesTo {α : Type} [MyHashable α] : α → UInt64 → Prop where
  | mk : ∀ (x : α), HashesTo x (MyHashable.myHash x)

-- Manual checker instance that requires [MyHashable α]
instance [MyHashable α] [DecidableEq UInt64] : DecOpt (@HashesTo α _ x h) where
  decOpt := fun _ => if MyHashable.myHash x == h then .ok true else .ok false

inductive ValidHash {α : Type} [MyHashable α] : α → Prop where
  | mk : ∀ (x : α) (h : UInt64), HashesTo x h → ValidHash x

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#guard_msgs(drop info) in
derive_mutual
  generator (fun a b x => ∃ h, @HashesTo a b x h)
