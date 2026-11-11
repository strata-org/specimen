import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace SuiteF.Misc1
inductive Cube : Nat → Prop where
| cube n : Cube (n * n * n)
def f : Nat → Nat := fun _ => 0
inductive HasCall : Nat → Prop where
| foo (n : Nat) : f n = 0 → HasCall n
inductive square_of' : Nat → Nat → Prop where
  | sq : forall x, square_of' x (x * x)
inductive square_of'' : Nat → Nat × Nat → Prop where
  | sq : forall x, square_of'' x (x, x)
inductive Tm : Type where
  | var (i : Nat)
  deriving Repr
inductive HasTy : List Nat → Tm → Nat → Prop where
  | var : Γ[i]? = some τ → HasTy Γ (.var i) τ
inductive ListConstr : List Nat → Prop where
| empty : ListConstr []
| cons₁ : ListConstr l → 2 ≤ x → ListConstr (x :: x :: l)
| cons₂ : ListConstr l → x < 2 → ListConstr (x :: l)

set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (∃ (m : Nat), Cube m),
  generator (∃ n, HasCall n), enumerator (∃ n, HasCall n),
  generator (fun n => ∃ (m : Nat), square_of'' m n),
  generator (fun n => ∃ (m : Nat), square_of' m n),
  generator (fun Γ τ => ∃ e : Tm, HasTy Γ e τ),
  generator (fun (_ : Unit) => ∃ (l : List Nat), ListConstr l),
  checker (fun l => ListConstr l)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end SuiteF.Misc1
