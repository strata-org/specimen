import Specimen
import Specimen.Basalt
import Specimen.Correctness.FloorOf

/-! Floors for an interleaving relation (the shape of Cedar's `CapMerge`). -/

namespace Specimen.Correctness.FloorMergeTest
open Basalt Specimen.Correctness

inductive Mrg : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat) → Prop where
  | nil : Mrg [] [] []
  | left : ∀ x k c₁ c₂ c, Mrg c₁ c₂ c → Mrg ((x, k) :: c₁) c₂ ((x, k) :: c)
  | right : ∀ x k c₁ c₂ c, Mrg c₁ c₂ c → Mrg c₁ ((x, k) :: c₂) ((x, k) :: c)
  | both : ∀ x k c₁ c₂ c, Mrg c₁ c₂ c → Mrg ((x, k) :: c₁) ((x, k) :: c₂) ((x, k) :: c)

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.sizeSplit true
set_option specimen.deriveFloors true
set_option specimen.emitSound true

derive_mutual generator (fun a b => ∃ c, Mrg a b c)

end Specimen.Correctness.FloorMergeTest
