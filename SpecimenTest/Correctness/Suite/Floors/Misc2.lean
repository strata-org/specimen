import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace SuiteF.Misc2
inductive HasDep {α : Type} (_ : List α) : Nat → Prop where
| foo (a b : α) : a = b → HasDep _ 0
inductive HasClassDep {α : Type} [h : DecidableEq α] : Nat → Prop where
| foo (a b : α) : a = b → HasClassDep 0
inductive Box (α : Type) where
  | mk : α → Box α
  deriving Repr
inductive Wraps (α : Type) : α → Box α → Prop where
  | wrap : Wraps α x (.mk x)
inductive MyRel {α : Type} [DecidableEq α] : α → Nat → Prop where
  | mk : MyRel x 0
inductive PairRel {α : Type} [DecidableEq α] : α → (α × α) → Prop where
  | mk : PairRel x (x, x)
inductive Total {α} : α → Prop where
| any a : Total a

set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun α l => ∃ n, @HasDep α l n),
  generator (fun α inst => ∃ n, @HasClassDep α inst n),
  checker (fun α inst n => @HasClassDep α inst n),
  enumerator (fun α inst => ∃ n, @HasClassDep α inst n),
  generator (fun (α : Type) (_inst : DecidableEq α) (x : α) => ∃ (b : Box α), @Wraps α x b),
  generator (fun (α : Type) (inst : DecidableEq α) (x : α) => ∃ n, @MyRel α inst x n),
  generator (fun (α : Type) (inst : DecidableEq α) (x : α) => ∃ (p : α × α), @PairRel α inst x p),
  generator (∃ (a : Nat), Total a)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end SuiteF.Misc2
