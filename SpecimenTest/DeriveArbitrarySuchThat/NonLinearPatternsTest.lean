import Plausible.Gen
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.CommonDefinitions.BinaryTree

/-! Tests for `derive_generator` on inductive relations with non-linear (repeated variable) patterns. -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

-- Example taken from "Generating Good Generators for Inductive Relations", section 3
inductive GoodTree : Nat → Nat → BinaryTree → Prop where
  | GoodLeaf : ∀ n, GoodTree n n .Leaf

#guard_msgs(drop info) in
derive_generator (fun in1 in2 => ∃ (t : BinaryTree), GoodTree in1 in2 t)


/-- `SameHead xs ys` means the lists `xs` and `ys` have the same head
     - This is an example relation with a non-linear pattern
      (`x` appears twice in the conclusion of `HeadMatch`) -/
inductive SameHead : List Nat → List Nat → Prop where
| HeadMatch : ∀ x xs ys, SameHead (x::xs) (x::ys)

#guard_msgs(drop info) in
derive_generator (fun ys => ∃ (xs : List Nat), SameHead xs ys)
