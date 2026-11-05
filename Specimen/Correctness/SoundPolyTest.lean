import Specimen
import Specimen.Basalt
import Specimen.Correctness.SoundOf

/-! Soundness for a relation with type parameters. -/

namespace Specimen.Correctness.SoundPolyTest
open Basalt Specimen.Correctness

inductive MC {α β : Type} : α → β → List (α × β) → Prop where
  | here : ∀ k v rest, MC k v ((k, v) :: rest)
  | there : ∀ k v p rest, MC k v rest → MC k v (p :: rest)

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.emitSound true

derive_mutual generator (fun (k : Nat) (m : List (Nat × Bool)) => ∃ v, MC k v m)

#print axioms specimen_gen_Specimen_Correctness_SoundPolyTest_MC_3__Specimen_Correctness_SoundPolyTest_Specimen_Correctness_SoundPolyTest.sound

end Specimen.Correctness.SoundPolyTest
