import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.ListRel
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

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun x => ∃ (l : List Nat), InList x l),
  generator (fun l => ∃ (l' : List Nat), MinOk l l'),
  generator (fun n l => ∃ (l' : List Nat), MinEx n l l'),
  generator (fun l => ∃ (n : Nat) (l' : List Nat), MinEx2 n l l'),
  enumerator (fun l => ∃ (x : Nat), InList x l),
  checker (fun x l => InList x l)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.ListRel
