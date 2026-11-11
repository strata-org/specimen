import Specimen
import Specimen.Basalt
import Specimen.Correctness.SearchFinds
import Specimen.Correctness.SoundOf

/-! A derived enumerator's search finds only what it produces: `SearchFinds`, walked. -/

set_option specimen.emitBasalt true
namespace SearchFindsTest
open Basalt Specimen Specimen.Correctness

inductive Between : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, lo ≤ hi → Between lo hi lo
  | there : ∀ lo hi n, Between (lo + 1) hi n → Between lo hi n

set_option specimen.richOutput false
derive_mutual enumerator (fun lo hi => ∃ n, Between lo hi n)

theorem between_searchFinds : ∀ (fuel iS sz lo hi : Nat),
    SearchFinds (specimen_enum_SearchFindsTest_Between_2__Specimen_Correctness_SearchFindsTest_SearchFindsTest (G := Search) fuel iS sz lo hi) (specimen_enum_SearchFindsTest_Between_2__Specimen_Correctness_SearchFindsTest_SearchFindsTest (G := SGen) fuel iS sz lo hi) := by
  intro fuel
  induction fuel with
  | zero => intro iS sz lo hi; unfold specimen_enum_SearchFindsTest_Between_2__Specimen_Correctness_SearchFindsTest_SearchFindsTest; walk
  | succ fuel ih => intro iS sz lo hi; unfold specimen_enum_SearchFindsTest_Between_2__Specimen_Correctness_SearchFindsTest_SearchFindsTest; walk [ih]

#print axioms between_searchFinds

end SearchFindsTest
namespace SearchFindsTest
#check @specimen_enum_SearchFindsTest_Between_2__Specimen_Correctness_SearchFindsTest_SearchFindsTest
open Lean Elab Command in
#eval show CommandElabM Unit from do
  for (n, c) in (← getEnv).constants.map₂.toList do
    if (n.toString.splitOn "EnumFor").length > 1 && (n.toString.splitOn "Between").length > 1 then
      logInfo m!"{n} := {c.value!}"
end SearchFindsTest
