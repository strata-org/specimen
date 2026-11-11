import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.PolyMap
abbrev Map α β := List (α × β)
abbrev Maps α β := List (Map α β)
inductive MapFind₂ {α β : Type} : Map α β → α × β → Prop where
| hd : MapFind₂ ((x, y) :: m) (x, y)
| tl : MapFind₂ m (x, y) → MapFind₂ (p :: m) (x, y)
inductive MapsFind₂ : Maps α β → α × β → Prop where
| hd : MapFind₂ m (x, y) → MapsFind₂ (m :: ms) (x, y)
| tl : MapsFind₂ ms (x, y) → MapsFind₂ (m :: ms) (x, y)
inductive NotContains {α : Type} : List α → α → Prop where
| empty : NotContains [] x
| cons : x ≠ y → NotContains xs x → NotContains (y :: xs) x

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun α β m => ∃ pa, @MapFind₂ α β m pa),
  generator (fun α β m => ∃ pa, @MapsFind₂ α β m pa),
  checker (fun α β m pa => @MapsFind₂ α β m pa),
  generator (fun xs => ∃ x, @NotContains Nat xs x)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.PolyMap
