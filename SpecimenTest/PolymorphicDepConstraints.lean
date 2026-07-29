import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import Specimen.DeriveEnum
import Specimen.Enumerators
import Specimen.EnumeratorCombinators

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

-- ============================================================
-- Test 5: Warning for missing concrete instances
-- ============================================================

inductive MyColor | Red | Green | Blue

inductive HasColor : MyColor → Nat → Prop where
  | mk : ∀ c n, HasColor c n

/--
warning: derive_mutual: [generator] fun b => ∃ a, HasColor a b needs [Arbitrary (MyColor)] but no such instance exists
-/
#guard_msgs(warning, drop error, drop info) in
set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
derive_mutual
  checker (fun c n => HasColor c n),
  generator (fun n => ∃ c, HasColor c n)

-- ============================================================
-- Test 6: Enum propagates transitively through a checker that enumerates α
--
-- Chain: generator (NoWitness) --checks--> ¬HasWitness
--        HasWitness checker --enumerates a witness x : α--> needs [Enum α]
-- so [Enum α] must propagate all the way up to the NoWitness generator.
-- (The negation is essential: `¬ HasWitness` can only be *checked*, not inverted,
-- which is what forces the generator to depend on HasWitness's checker.)
-- ============================================================

inductive Witnessed {α : Type} : α → Nat → Prop where
  | mk : ∀ (x : α), Witnessed x 0

-- Deciding `HasWitness n` means searching for a witness `x : α` — the checker must
-- enumerate α, so it requires [Enum α].
inductive HasWitness {α : Type} : Nat → Prop where
  | mk : ∀ (x : α) n, Witnessed x n → HasWitness n

-- Generating `∃ n, NoWitness n` must *check* `¬ HasWitness n`, pulling in
-- HasWitness's checker and hence its [Enum α] constraint.
inductive NoWitness {α : Type} : Nat → Prop where
  | mk : ∀ n, ¬ HasWitness (α := α) n → NoWitness n

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#guard_msgs(drop info) in
derive_mutual
  checker   (fun α x n => @Witnessed α x n),
  checker   (fun α n => @HasWitness α n),
  generator (fun α => ∃ n, @NoWitness α n)

-- The checker for HasWitness enumerates α, so it needs [Enum α].
example [Enum α] [DecidableEq α] : DecOpt (@HasWitness α 0) := inferInstance

-- The generator for NoWitness must have propagated [Enum α] up through the
-- `¬ HasWitness` check — plus [Arbitrary α] (generate the witnesses when
-- exploring) and [DecidableEq α] (checker default).
example [Plausible.Arbitrary α] [Enum α] [DecidableEq α] :
    ArbitrarySizedSuchThat Nat (fun n => @NoWitness α n) := inferInstance

-- And it resolves at a concrete type carrying Enum + DecidableEq.
example : ArbitrarySizedSuchThat Nat (fun n => @NoWitness Bool n) := inferInstance

-- ============================================================
-- Test 7: The Test 6 chain, but the shared type A lives inside a STRUCTURE
-- parameter P (as `P.A`). The [Enum P.A] a checker needs to enumerate a
-- leaf-typed witness must still propagate — across specs — up to the generator,
-- re-rooted onto each spec's own copy of the parameter.
-- ============================================================

structure Cfg where
  A : Type
  Spare : Type   -- unused: must never acquire a spurious constraint

inductive RS (P : Cfg) : P.A → Nat → Prop where
  | mk : ∀ (x : P.A), RS P x 0

-- Deciding `HasWitnessS P n` enumerates a witness `x : P.A` ⇒ checker needs [Enum P.A].
inductive HasWitnessS (P : Cfg) : Nat → Prop where
  | mk : ∀ (x : P.A) n, RS P x n → HasWitnessS P n

-- Generating `∃ n, NoWitnessS P n` must *check* `¬ HasWitnessS P n`, so [Enum P.A]
-- propagates from the checker up to this generator.
inductive NoWitnessS (P : Cfg) : Nat → Prop where
  | mk : ∀ n, ¬ HasWitnessS P n → NoWitnessS P n

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#guard_msgs(drop info) in
derive_mutual
  checker   (fun (P : Cfg) x n => @RS P x n),
  checker   (fun (P : Cfg) n => @HasWitnessS P n),
  generator (fun (P : Cfg) => ∃ n, @NoWitnessS P n)

-- The struct-param leaf `P.A` gets exactly the discovered constraints:
-- the checker enumerates it ⇒ [Enum P.A].
example [Enum P.A] [DecidableEq P.A] : DecOpt (@HasWitnessS P 0) := inferInstance

-- ...and the generator inherits [Enum P.A] transitively through `¬ HasWitnessS`.
example [Plausible.Arbitrary P.A] [Enum P.A] [DecidableEq P.A] :
    ArbitrarySizedSuchThat Nat (fun n => @NoWitnessS P n) := inferInstance

-- Concrete instantiation: A = Bool (has the instances), Spare = Empty (no
-- instances) — resolving proves no spurious constraint attached to the unused
-- `Spare` field.
example : ArbitrarySizedSuchThat Nat (fun n => @NoWitnessS ⟨Bool, Empty⟩ n) := inferInstance
