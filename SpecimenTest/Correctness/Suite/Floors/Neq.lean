import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace SuiteF.Neq
inductive usesNeq : Nat → Prop where
| c : a ≠ b → usesNeq a
inductive usesNeq' : Nat × Nat → Prop where
| c : a ≠ b → usesNeq' (a, b)
inductive Diag : (α : Type u) → α → α × α → Prop where
| c : Diag α a (b, b)

set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (∃ a, usesNeq a), generator (∃ a, usesNeq' a),
  generator (fun γ p => ∃ g, Diag γ g p), checker (fun γ g p => Diag γ g p)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end SuiteF.Neq
