import Specimen
import Specimen.Basalt
import Specimen.Enum.Laws
import Basalt.Walk.Entry
import Specimen.Correctness.GenInterpSPMF

/-!
# A derived generator's and enumerator's law, walked

`Between` derived under `specimen.emitBasalt` as a generator and as an enumerator, each with a `DecOpt`
premise, a recursive constructor and the size-0 truncation label, read at `ExceptT Exhaustion Finite`:
what it lists is exactly what it can succeed with at the sampler, `ExceptT Exhaustion (OptionT SPMF)`
(`EnumeratesWith`), at every fuel and size. Induction on the fuel the worker recurses on, and `walk` at each level; the two differ only in
their schedules, so the one proof shape serves both.
-/

set_option specimen.emitBasalt true

namespace DerivedEnumLaw

open Basalt Specimen

inductive Between : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, lo ≤ hi → Between lo hi lo
  | there : ∀ lo hi n, Between (lo + 1) hi n → Between lo hi n

#guard_msgs(drop info, drop warning) in
derive_mutual generator (fun lo hi => ∃ n, Between lo hi n)

/-- The derived `Between` generator, read as an enumeration with labels, lists exactly what it can
succeed with at the sampler, at every fuel and size: one `walk` per fuel level. -/
theorem between_enumeratesWith : ∀ (fuel iS sz lo hi : Nat),
    EnumeratesWith (specimen_gen_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw (G := ExceptT Exhaustion Finite) fuel iS sz lo hi)
      (specimen_gen_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw (G := ExceptT Exhaustion (OptionT SPMF)) fuel iS sz lo hi) := by
  intro fuel
  induction fuel with
  | zero => intro iS sz lo hi; unfold specimen_gen_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw; walk
  | succ fuel ih => intro iS sz lo hi; unfold specimen_gen_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw; walk [ih]

/-- info: 'DerivedEnumLaw.between_enumeratesWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms between_enumeratesWith

#guard_msgs(drop info, drop warning) in
derive_mutual enumerator (fun lo hi => ∃ n, Between lo hi n)

/-- The derived `Between` enumerator, read where checkers read it, lists exactly what it can succeed
with at the sampler. -/
theorem between_enum_enumeratesWith : ∀ (fuel iS sz lo hi : Nat),
    EnumeratesWith (specimen_enum_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw (G := ExceptT Exhaustion Finite) fuel iS sz lo hi)
      (specimen_enum_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw (G := ExceptT Exhaustion (OptionT SPMF)) fuel iS sz lo hi) := by
  intro fuel
  induction fuel with
  | zero => intro iS sz lo hi; unfold specimen_enum_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw; walk
  | succ fuel ih => intro iS sz lo hi; unfold specimen_enum_DerivedEnumLaw_Between_2__SpecimenTest_Correctness_DerivedEnumLaw_DerivedEnumLaw; walk [ih]

/-- info: 'DerivedEnumLaw.between_enum_enumeratesWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms between_enum_enumeratesWith

end DerivedEnumLaw
