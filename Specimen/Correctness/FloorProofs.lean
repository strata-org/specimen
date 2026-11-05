import Specimen.Correctness.FloorTest
import Specimen.Correctness.SplitLaws
import Specimen.Correctness.SureLaws

/-! The derived floors' generator succeeds from exactly `μ τ`. -/

namespace Specimen.Correctness.FloorTest
open Basalt Specimen.Correctness

local notation "WF" => Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors (G := SGen)

/-- **Never below the floor.** A success at size `n` has `μ τ ≤ n`. -/
theorem floors_lower : ∀ (fuel iS n : Nat) (τ : Ty), succObs.spec (WF fuel iS n τ) (fun _ => μ τ ≤ n)
  | 0, _, _, _ => by
    rw [Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors.eq_1]
    walk
  | f + 1, iS, n, τ => by
    have ih := floors_lower f iS
    rw [Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors.eq_body]
    delta Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors.body
    cases n <;> walk
    all_goals first
      | (simp only [μ]; omega)
      | (rename_i ps hl hs _ _ h₁ _ h₂
         match ps, hl with
         | [p₀, p₁], _ =>
           simp only [SizeSplit.sizeAt, List.getD_cons_zero, List.getD_cons_succ, List.sum_cons,
             List.sum_nil] at h₁ h₂ hs
           simp only [μ]; omega)

#print axioms floors_lower

/-- **Always from the floor.** At every size from `μ τ` on, the generator succeeds surely. -/
theorem floors_sure : ∀ (fuel iS n : Nat) (τ : Ty), μ τ ≤ n → n < fuel → sok (WF fuel iS n τ) = 1
  | 0, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, iS, n, τ, hμ, hf => by
    have ih := floors_sure f iS
    rw [Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors.eq_body]
    delta Floors.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Floors.body
    cases n <;> cases τ <;> simp only [μ] at hμ <;> (try omega) <;>
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.or_true, Bool.or_false, Bool.true_or,
        Bool.false_or, ↓reduceIte, reduceCtorEq]
    · -- size zero: the constant, or a truncation retried into it
      refine sok_backtrack_of_sure (fun p hp => ?_) ⟨_, List.mem_cons_self, Nat.succ_pos _, sok_pure _⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact total_of_sok (sok_pure _)
      · dsimp only; exact total_truncations _
    · -- a natural: the constant, or a successor of one
      refine sok_backtrack_of_sure (fun p hp => total_of_sok ?_) ⟨_, List.mem_cons_self, Nat.succ_pos _,
        sok_pure _⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact sok_pure _
      · exact sok_bind_one (ih _ _ (by simp [μ]) (by omega)) fun _ => sok_pure _
    · -- a pair: a split meeting both floors, then each side from its floor
      refine sok_backtrack_of_sure (fun p hp => total_of_sok ?_) ⟨_, List.mem_cons_self, Nat.succ_pos _, ?_⟩ <;>
      · first | (simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp) | skip
        refine sok_bind_one_of_support (sok_draw _ _) fun ps hps => ?_
        obtain ⟨hl, hsum, hfl⟩ := draw_parts hps
        have hfl := hfl (by simp only [List.sum_cons, List.sum_nil]; omega)
        match ps, hl, hfl with
        | [p₀, p₁], _, .cons h₀ (.cons h₁ .nil) =>
          simp only [SizeSplit.sizeAt, List.getD_cons_zero, List.getD_cons_succ]
          simp only [List.sum_cons, List.sum_nil] at hsum
          exact sok_bind_one (ih _ _ h₀ (by omega)) fun _ =>
            sok_bind_one (ih _ _ h₁ (by omega)) fun _ => sok_pure _

#print axioms floors_sure

/-- **The floors are exactly the threshold.** With fuel to spare, the derived generator of terms of type
`τ` succeeds surely at every size from `μ τ`, and never below it. -/
theorem floors_zero_one (fuel iS n : Nat) (τ : Ty) (hf : n < fuel) :
    sok (WF fuel iS n τ) = if μ τ ≤ n then 1 else 0 := by
  split
  · exact floors_sure fuel iS n τ ‹_› hf
  · exact sok_eq_zero fun x hx => ‹¬ μ τ ≤ n› (floors_lower fuel iS n τ x hx)

#print axioms floors_zero_one

end Specimen.Correctness.FloorTest

namespace Specimen.Correctness.FloorTest
open Basalt Specimen.Correctness

local notation "WD" => Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived (G := SGen)

/-- **Never below the derived floor.** -/
theorem derived_lower : ∀ (fuel iS n : Nat) (τ : Ty), succObs.spec (WD fuel iS n τ)
    (fun _ => Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived.floor τ ≤ n)
  | 0, _, _, _ => by
    rw [Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived.eq_1]
    walk
  | f + 1, iS, n, τ => by
    have ih := derived_lower f iS
    rw [Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived.eq_body]
    delta Derived.specimen_gen_Specimen_Correctness_FloorTest_HasTy_0__Specimen_Correctness_FloorTest_Specimen_Correctness_FloorTest_Derived.body
    cases n <;> walk
    all_goals floor_close

#print axioms derived_lower

end Specimen.Correctness.FloorTest
