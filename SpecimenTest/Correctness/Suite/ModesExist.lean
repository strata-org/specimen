import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.ModesExist
inductive LessThanEq : Nat → Nat → Prop where
  | Refl : ∀ n, LessThanEq n n
  | Succ : ∀ n m, LessThanEq n m → LessThanEq n (.succ m)
inductive NatChain (a b : Nat) : Prop where
| ChainExists : ∀ (x y : Nat), (LessThanEq a x) → (LessThanEq x y) → (LessThanEq y b) → NatChain a b
inductive SizedLe : Nat → Nat → Prop where
  | Refl : ∀ n, SizedLe n n
  | Succ : ∀ size' n, SizedLe size' n → SizedLe size' (Nat.succ n)
inductive AuxDecLe : Nat → Nat → Prop where
  | Refl : ∀ n, AuxDecLe n n
  | Succ : ∀ aux_dec n, AuxDecLe aux_dec n → AuxDecLe aux_dec (Nat.succ n)

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual enumerator (fun x => ∃ (a : Nat), LessThanEq a x),
  enumerator (fun x => ∃ (y : Nat), LessThanEq x y),
  checker (fun n m => LessThanEq n m),
  checker (fun a b => NatChain a b),
  checker (fun size' n => SizedLe size' n),
  generator (fun size' => ∃ n, SizedLe size' n),
  checker (fun aux_dec n => AuxDecLe aux_dec n)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.ModesExist
