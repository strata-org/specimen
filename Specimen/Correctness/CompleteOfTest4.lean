import Specimen
import Specimen.Basalt
import Specimen.Correctness.CompleteOf

/-! A mutual block. -/

namespace Specimen.Correctness.CompleteOfTest4
open Basalt Specimen.Correctness

mutual
inductive EvM : Nat → Prop where
  | z : EvM 0
  | s : ∀ n, OdM n → EvM (n + 1)
inductive OdM : Nat → Prop where
  | s : ∀ n, EvM n → OdM (n + 1)
end

set_option specimen.emitBasalt true
set_option specimen.emitComplete true
set_option specimen.reportPhaseTimers true
set_option specimen.richOutput false

derive_mutual generator (∃ n, EvM n)

example (n : Nat) (h : EvM n) :
    ∃ k, ∀ s l, k ≤ s → k ≤ l → Produces (BacktrackGenFor.gen (P := fun n => EvM n) (G := SGen) s l) n :=
  BacktrackGenForComplete.complete n h

end Specimen.Correctness.CompleteOfTest4
