import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.ModesBST
inductive BinaryTree where
  | Leaf : BinaryTree
  | Node : Nat → BinaryTree → BinaryTree → BinaryTree
  deriving Repr

inductive Between : Nat -> Nat -> Nat -> Prop where
| BetweenN : ∀ n m, n <= m -> Between n (.succ n) (.succ (.succ m))
| BetweenS : ∀ n m o, Between n m o -> Between n (.succ m) (.succ o)

inductive BST : Nat → Nat → BinaryTree → Prop where
  | BstLeaf: BST lo hi .Leaf
  | BstNode: ∀ lo hi x l r, Between lo x hi → BST lo x l → BST x hi r → BST lo hi (.Node x l r)


set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual enumerator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t),
  enumerator (fun lo hi => ∃ (x : Nat), Between lo x hi),
  generator (fun lo hi => ∃ (x : Nat), Between lo x hi),
  checker (fun lo hi t => BST lo hi t),
  checker (fun lo x hi => Between lo x hi)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.ModesBST
