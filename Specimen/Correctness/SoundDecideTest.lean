import Specimen
import Specimen.Basalt
import Specimen.Correctness.SoundOf
import Specimen.Correctness.CheckSoundOf

/-! Soundness where the generator checks an input against a pattern variable by `decide`. -/

namespace Specimen.Correctness.SoundDecideTest
open Basalt Specimen.Correctness

inductive Look : Nat → Nat → List (Nat × Nat) → Prop where
  | here : ∀ e a rest, Look e a ((e, a) :: rest)
  | there : ∀ e a p rest, Look e a rest → Look e a (p :: rest)

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.emitSound true

derive_mutual generator (fun e l => ∃ a, Look e a l)

#print axioms specimen_gen_Specimen_Correctness_SoundDecideTest_Look_1__Specimen_Correctness_SoundDecideTest_Specimen_Correctness_SoundDecideTest.sound

end Specimen.Correctness.SoundDecideTest
