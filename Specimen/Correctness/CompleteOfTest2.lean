import Specimen
import Specimen.Basalt
import Specimen.Correctness.CompleteOf

/-! A delegated premise and an unconstrained draw. -/

namespace Specimen.Correctness.CompleteOfTest2
open Basalt Specimen.Correctness

inductive Lk : List Nat → Nat → Nat → Prop where
  | now : ∀ x xs, Lk (x :: xs) 0 x
  | later : ∀ x xs n y, Lk xs n y → Lk (x :: xs) (n + 1) y

inductive Tm where
  | lit (n : Nat)
  | var (i : Nat)
  | add (a b : Tm)

inductive Ok : List Nat → Tm → Prop where
  | lit : ∀ Γ n, Ok Γ (.lit n)
  | var : ∀ Γ i v, Lk Γ i v → Ok Γ (.var i)
  | add : ∀ Γ a b, Ok Γ a → Ok Γ b → Ok Γ (.add a b)

set_option specimen.emitBasalt true
set_option specimen.emitComplete true
set_option specimen.richOutput false

derive_mutual generator (fun Γ => ∃ t, Ok Γ t)

/-- Every well-scoped term is generated, at every large enough size. -/
example (Γ : List Nat) (t : Tm) (h : Ok Γ t) :
    ∃ n, ∀ s l, n ≤ s → n ≤ l → Produces (BacktrackGenFor.gen (P := fun t => Ok Γ t) (G := SGen) s l) t :=
  BacktrackGenForComplete.complete t h

#print axioms specimen_gen_Specimen_Correctness_CompleteOfTest2_Ok_1__Specimen_Correctness_CompleteOfTest2_Specimen_Correctness_CompleteOfTest2.instComplete

end Specimen.Correctness.CompleteOfTest2
