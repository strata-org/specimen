import Specimen
import Specimen.Basalt
import Specimen.Correctness.CompleteOf

/-! Floors that depend on a call's inputs: a pair type needs a term with one `mk` per pair. -/

namespace Specimen.Correctness.FloorTest
open Basalt Specimen.Correctness

inductive Ty where
  | nat
  | prod (a b : Ty)
  deriving Repr, DecidableEq

inductive Tm where
  | z
  | s (t : Tm)
  | mk (a b : Tm)
  deriving Repr

inductive HasTy : Tm → Ty → Prop where
  | z : HasTy .z .nat
  | s : ∀ t, HasTy t .nat → HasTy (.s t) .nat
  | mk : ∀ a b A B, HasTy a A → HasTy b B → HasTy (.mk a b) (.prod A B)

/-- The least size a term of type `τ` needs: one per pair. -/
def μ : Ty → Nat
  | .nat => 0
  | .prod a b => 1 + μ a + μ b

set_option specimen.emitBasalt true
set_option specimen.richOutput false

namespace Div
scoped derive_mutual generator (fun τ => ∃ t, HasTy t τ)
end Div

namespace Uniform
set_option specimen.sizeSplit true in
scoped derive_mutual generator (fun τ => ∃ t, HasTy t τ)
end Uniform

namespace Floors
set_option specimen.sizeSplit true in
set_option specimen.splitFloors "Specimen.Correctness.FloorTest.HasTy:Specimen.Correctness.FloorTest.μ" in
scoped derive_mutual generator (fun τ => ∃ t, HasTy t τ)
end Floors

namespace Derived
set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
scoped derive_mutual generator (fun τ => ∃ t, HasTy t τ)
end Derived

#print Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived.floor
/-- The derived floor is `μ`. -/
example : ∀ τ, Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived.floor τ = μ τ := by
  intro τ; induction τ with
  | nat => decide
  | prod a b iha ihb =>
    simp only [Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived.floor, iha, ihb, μ]
    simp [Specimen.SizeSplit.minFloor, Specimen.SizeSplit.minFloor.minFloorAux]

#specimen_body Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived
#specimen_body Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors
set_option pp.proofs false in
#print Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors.body

end Specimen.Correctness.FloorTest
