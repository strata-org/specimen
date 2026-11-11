import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.ModesList
inductive InList : Nat → List Nat → Prop where
| Here : ∀ x l, InList x (x::l)
| There : ∀ x y l, InList x l → InList x (y::l)
inductive MinOk : List Nat → List Nat → Prop where
| MO_empty : MinOk [] []
| MO_present : ∀ x l l', MinOk l l' → InList x l → MinOk l (x::l')
inductive MinEx : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx .zero [] []
| ME_present : ∀ x l n l', MinEx n l l' → InList x l → MinEx (Nat.succ n) l (x::l')
inductive MinEx2 : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx2 .zero [] []
| ME_present : ∀ x l l', MinEx2 x l l' → MinEx2 (Nat.succ x) l ([x] ++ l')
inductive square_of : Nat → Nat → Prop where
  | sq : forall n, square_of n (n * n)

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual enumerator (fun x => ∃ (l : List Nat), InList x l),
  enumerator (fun a => ∃ (l : List Nat), MinOk l a),
  enumerator (fun n a => ∃ (l : List Nat), MinEx n l a),
  checker (fun x l => InList x l),
  checker (fun l a => MinOk l a),
  checker (fun n l a => MinEx n l a),
  checker (fun n m => square_of n m)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.ModesList
