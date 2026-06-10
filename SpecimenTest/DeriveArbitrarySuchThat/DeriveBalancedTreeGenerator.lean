import Plausible.Gen
import Plausible.Arbitrary
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.CommonDefinitions.BinaryTree

/-! Snapshot test: derived constrained generator for balanced binary trees. -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

-- `balancedTree n t` describes whether the tree `t` of height `n` is *balancedTree*, i.e. every path through the tree has length either `n` or `n-1`. -/
inductive balancedTree : Nat → BinaryTree → Prop where
  | B0 : balancedTree .zero BinaryTree.Leaf
  | B1 : balancedTree (.succ .zero) BinaryTree.Leaf
  | BS : ∀ n x l r,
    balancedTree n l → balancedTree n r →
    balancedTree (.succ n) (BinaryTree.Node x l r)

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

#guard_msgs(drop info) in
derive_mutual
 (fun n => ∃ (t : BinaryTree), balancedTree n t)
