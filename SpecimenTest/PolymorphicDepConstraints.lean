import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker

/-!
# Regression test for issue #38: missing typeclass constraints for polymorphic dependencies

When a generator depends on a checker sharing a type parameter, the generator must
propagate the checker's constraints. Previously hardcoded; now computed bottom-up.
-/

open Plausible

inductive MyContains {α : Type} : α → List α → Prop where
  | here : ∀ x rest, MyContains x (x :: rest)
  | there : ∀ x y rest, MyContains x rest → MyContains x (y :: rest)

inductive NotIn {α : Type} : α → List α → Prop where
  | mk : ∀ x xs, ¬ MyContains x xs → NotIn x xs

-- The fully polymorphic case: the generated instance must carry constraints from the checker dep
set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
#guard_msgs(drop info) in
derive_mutual
  checker (fun α x xs => @MyContains α x xs),
  generator (fun α xs => ∃ x, @NotIn α x xs)

-- Verify: generator only needs [Arbitrary α, DecidableEq α] (from the Eq check in MyContains)
-- NOT [Enum α] — the checker doesn't enumerate, it only checks equality
example : ∀ [Plausible.Arbitrary α] [DecidableEq α],
    ArbitrarySizedSuchThat α (fun x => @NotIn α x xs) := inferInstance
