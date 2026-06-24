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
derive_mutual
  checker (fun α x xs => @MyContains α x xs),
  generator (fun α xs => ∃ x, @NotIn α x xs)
