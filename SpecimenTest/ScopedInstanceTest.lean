import Plausible.Gen
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.CommonDefinitions.BinaryTree
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker

/-! Test: scoped and local instance visibility for `derive_mutual`.
    Demonstrates that the same relation can be derived with different strategies
    in separate namespaces without global conflicts (issue #43). -/

open Plausible

deriving instance Arbitrary for BinaryTree

namespace Strategy.A

set_option specimen.autoDeriveDeps true in
scoped derive_mutual
  (fun (lo hi : Nat) => ∃ (t : BinaryTree), BST lo hi t)

end Strategy.A

namespace Strategy.B

set_option specimen.autoDeriveDeps true in
scoped derive_mutual
  (fun (lo hi : Nat) => ∃ (t : BinaryTree), BST lo hi t)

end Strategy.B

-- Without opening either namespace, instance synthesis should fail
#check_failure (inferInstance : ArbitrarySizedSuchThat BinaryTree (fun t => BST 0 10 t))

-- Opening Strategy.A makes its instance available
open Strategy.A in
#check (inferInstance : ArbitrarySizedSuchThat BinaryTree (fun t => BST 0 10 t))

-- Opening Strategy.B makes its instance available
open Strategy.B in
#check (inferInstance : ArbitrarySizedSuchThat BinaryTree (fun t => BST 0 10 t))

-- Opening both is valid — Lean picks one by priority/order (no ambiguity error)
open Strategy.A Strategy.B in
#check (inferInstance : ArbitrarySizedSuchThat BinaryTree (fun t => BST 0 10 t))
