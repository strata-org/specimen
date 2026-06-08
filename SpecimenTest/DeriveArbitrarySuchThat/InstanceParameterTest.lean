import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary
import Plausible.Arbitrary

open Plausible

set_option guard_msgs.diff true

/-! ## Instance parameters in inductive relations

When an inductive relation has instance-implicit parameters (e.g.,
[DecidableEq α]), the deriver should skip them during schedule
derivation — they are resolved by typeclass synthesis, not generated. -/

inductive MyRel {α : Type} [DecidableEq α] : α → Nat → Prop where
  | mk : MyRel x 0

set_option maxHeartbeats 400000

#guard_msgs(drop info) in
derive_generator (fun (α : Type) (inst : DecidableEq α) (x : α) =>
  ∃ n, @MyRel α inst x n)

#guard_msgs(drop info) in
#synth ArbitrarySizedSuchThat Nat (fun n => @MyRel Nat instDecidableEqNat 42 n)

/-! ## Eta-expanded instance lambdas in constructor arguments

When a constructor's conclusion or hypothesis contains an application whose
arguments include an eta-expanded typeclass instance (e.g.,
`fun a b => instDecidableEqFoo a b`), the deriver should recognize it as
a typeclass instance and skip it. -/

-- A relation where DecidableEq appears as an eta-expanded lambda in constructor args
-- because the conclusion references a type (Prod α α) that carries the instance.
inductive PairRel {α : Type} [DecidableEq α] : α → (α × α) → Prop where
  | mk : PairRel x (x, x)

#guard_msgs(drop info) in
derive_generator (fun (α : Type) (inst : DecidableEq α) (x : α) =>
  ∃ (p : α × α), @PairRel α inst x p)

#guard_msgs(drop info) in
#synth @ArbitrarySizedSuchThat (Nat × Nat) (fun p => @PairRel Nat instDecidableEqNat 42 p)
