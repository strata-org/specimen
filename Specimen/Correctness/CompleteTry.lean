import Specimen
import Specimen.Basalt
import Specimen.Correctness.ReachClose
import Specimen.Correctness.StepOf

namespace Specimen.Correctness.CompleteTry
open Basalt Specimen.Correctness

inductive Tree where
  | leaf
  | node (l r : Tree)

inductive WT : Tree → Prop where
  | leaf : WT .leaf
  | node : ∀ l r, WT l → WT r → WT (.node l r)

namespace Div
set_option specimen.emitBasalt true in
set_option specimen.richOutput false in
scoped derive_mutual generator (∃ t, WT t)
end Div

namespace Split
set_option specimen.emitBasalt true in
set_option specimen.sizeSplit true in
set_option specimen.richOutput false in
scoped derive_mutual generator (∃ t, WT t)
end Split

#specimen_body Div.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Div
#specimen_body Split.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Split
set_option pp.proofs false
#print Div.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Div.body
#print Split.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Split.body

local notation "WD" => Div.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Div (G := SGen)
local notation "WS" => Split.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Split (G := SGen)

theorem div_complete : ∀ t, WT t → ∃ n, ∀ fuel iS sz, n ≤ sz → sz < fuel → Produces (WD fuel iS sz) t := by
  intro t h
  induction h with
  | leaf =>
    refine ⟨0, fun fuel iS sz _ hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine produces_of_reach ?_
    rw [Div.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Div.eq_body]
    delta Div.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Div.body
    cases sz <;> walk
  | node l r _ _ ihl ihr =>
    obtain ⟨n₁, h₁⟩ := ihl
    obtain ⟨n₂, h₂⟩ := ihr
    refine ⟨2 * (n₁ + n₂) + 1, fun fuel iS sz hn hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    refine produces_of_reach ?_
    rw [Div.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Div.eq_body]
    delta Div.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Div.body
    walk
    reach_close

theorem split_complete : ∀ t, WT t → ∃ n, ∀ fuel iS sz, n ≤ sz → sz < fuel → Produces (WS fuel iS sz) t := by
  intro t h
  induction h with
  | leaf =>
    refine ⟨0, fun fuel iS sz _ hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine produces_of_reach ?_
    rw [Split.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Split.eq_body]
    delta Split.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Split.body
    cases sz <;> walk
  | node l r _ _ ihl ihr =>
    obtain ⟨n₁, h₁⟩ := ihl
    obtain ⟨n₂, h₂⟩ := ihr
    refine ⟨2 * (n₁ + n₂) + 1, fun fuel iS sz hn hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    refine produces_of_reach ?_
    rw [Split.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Split.eq_body]
    delta Split.specimen_gen_Specimen_Correctness_CompleteTry_WT_0__Specimen_Correctness_CompleteTry_Specimen_Correctness_CompleteTry_Split.body
    walk
    reach_close

#print axioms split_complete

end Specimen.Correctness.CompleteTry
