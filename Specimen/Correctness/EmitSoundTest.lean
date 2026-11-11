import Specimen
import Specimen.Basalt
import Specimen.Correctness.SoundOf

/-! `specimen.emitSound`: `derive_mutual` proves its generators sound. A callee, a mutual pair, and a
hand-written instance whose law is tagged. -/

namespace Specimen.Correctness.EmitSoundTest

open Basalt Specimen.Correctness

inductive Ev : Nat → Prop where
  | z : Ev 0
  | ss : ∀ n, Ev n → Ev (n + 2)

mutual
inductive EvM : Nat → Prop where
  | z : EvM 0
  | s : ∀ n, OdM n → EvM (n + 1)
inductive OdM : Nat → Prop where
  | s : ∀ n, EvM n → OdM (n + 1)
end

/-- Uses `Ev` and the mutual pair, and `Big`, which has a hand-written instance. -/
inductive Big : Nat → Prop where
  | mk : ∀ n, 10 ≤ n → Big n

instance : BacktrackGenFor Nat (fun n => Big n) where
  gen s _ := do
    let k ← chooseNat 0 s
    pure (10 + k)

@[specimen_sound]
theorem big_gen (s l : Nat) : succObs.spec (BacktrackGenFor.gen (P := fun n => Big n) (G := SGen) s l) Big := by
  show succObs.spec (do let k ← chooseNat 0 s; pure (10 + k) : SGen Nat) _
  walk
  exact .mk _ (by omega)

inductive Pair : Nat → Nat → Nat → Prop where
  | mk : ∀ a b c, Ev a → EvM b → Big c → Pair a b c

set_option specimen.emitBasalt true in
set_option specimen.emitSound true in
set_option specimen.richOutput false in
derive_mutual
  generator (∃ a b c, Pair a b c)

#check @specimen_gen_Specimen_Correctness_EmitSoundTest_Pair_0_1_2__Specimen_Correctness_EmitSoundTest_Specimen_Correctness_EmitSoundTest.sound
#print axioms specimen_gen_Specimen_Correctness_EmitSoundTest_Pair_0_1_2__Specimen_Correctness_EmitSoundTest_Specimen_Correctness_EmitSoundTest.sound

end Specimen.Correctness.EmitSoundTest
