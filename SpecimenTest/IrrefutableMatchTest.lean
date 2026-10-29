import Specimen
import Specimen.Basalt

/-!
# A pattern that matches every value gets no failure arm

A schedule's `Match` step tests an input against a constructor pattern and fails otherwise. For a
one-constructor structure the pattern matches every value, so the failure arm after it is redundant,
and Lean rejects a redundant `| _ => …` alternative. Each derivation below matches on `Tagged`, which
has one constructor; before the fix every one of them failed to elaborate. `Pick` matches on a
two-constructor type, where the failure arm is still needed, so it pins that the fix stays out of the
refutable case.
-/

open Plausible

namespace IrrefutableMatchTest

structure Tagged where
  tag : Nat
  n : Nat

/-- Every `Tagged` value: the checker's pattern is irrefutable. -/
inductive Inner : Tagged → Prop where
  | mk : ∀ s n, Inner ⟨s, n⟩

/-- A premise after the irrefutable match, so the match is not the whole body. -/
inductive Pos : Tagged → Prop where
  | mk : ∀ s n, 0 < n → Pos ⟨s, n⟩

/-- An input of `Tagged` type to a generator, matched against its only constructor. -/
inductive TagSum : Tagged → Nat → Prop where
  | mk : ∀ s n, TagSum ⟨s, n⟩ (s + n)

/-- A two-constructor input: the match is refutable and keeps its failure arm. -/
inductive Pick : Option Nat → Nat → Prop where
  | some : ∀ n, Pick (.some n) n

#guard_msgs(drop info) in
derive_checker (fun t => Inner t)

#guard_msgs(drop info) in
derive_checker (fun t => Pos t)

#guard_msgs(drop info) in
derive_generator (fun t => ∃ m, TagSum t m)

#guard_msgs(drop info) in
derive_enumerator (fun t => ∃ m, TagSum t m)

#guard_msgs(drop info) in
derive_checker (fun o n => Pick o n)

/-- info: [true, true, false] -/
#guard_msgs in
#eval [DecOpt.decOpt (Inner ⟨1, 2⟩) 5, DecOpt.decOpt (Pos ⟨1, 2⟩) 5, DecOpt.decOpt (Pos ⟨1, 0⟩) 5].map
  fun r => match r with | .ok b => b | .error _ => false

/-- info: [true, false] -/
#guard_msgs in
#eval [DecOpt.decOpt (Pick (.some 3) 3) 5, DecOpt.decOpt (Pick .none 3) 5].map
  fun r => match r with | .ok b => b | .error _ => true

end IrrefutableMatchTest
