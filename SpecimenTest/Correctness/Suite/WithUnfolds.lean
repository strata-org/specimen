import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.WithUnfolds
structure TypeBox where
  ty : Type
instance : Inhabited TypeBox := ⟨⟨Unit⟩⟩
abbrev NatFoo : TypeBox where
  ty := Nat
inductive TypeBoxPred : Nat → Prop where
| someRefl {x : NatFoo.ty} : x = x → 0 = x → 5 = 5 → TypeBoxPred 5
inductive TypeBoxPredS : String → Prop where
| someRefl {x : NatFoo.ty} y : x = x → y = "foo" → TypeBoxPredS "foo"

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (∃ (n : Nat), TypeBoxPred n), generator (∃ (n : String), TypeBoxPredS n)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.WithUnfolds
