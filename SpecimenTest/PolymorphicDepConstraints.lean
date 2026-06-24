import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker

/-!
# Regression test for issue #38: missing typeclass constraints for polymorphic dependencies
-/

open Plausible

inductive MyContains {α : Type} : α → List α → Prop where
  | here : ∀ x rest, MyContains x (x :: rest)
  | there : ∀ x y rest, MyContains x rest → MyContains x (y :: rest)

inductive NotIn {α : Type} : α → List α → Prop where
  | mk : ∀ x xs, ¬ MyContains x xs → NotIn x xs

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
set_option specimen.textOutput 3 in
derive_mutual
  checker (fun α x xs => @MyContains α x xs),
  generator (fun α xs => ∃ x, @NotIn α x xs)

-- Verify: the generator instance has [Enum α] propagated from the checker dep
example : ∀ [Enum α] [DecidableEq α] [Plausible.Arbitrary α],
    ArbitrarySizedSuchThat α (fun x => @NotIn α x xs) := inferInstance
