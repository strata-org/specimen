import Specimen
import Specimen.Basalt
import Specimen.Enum.Laws
import Basalt.Walk.Entry

/-!
# A derived enumerator's search answers what its enumeration lists, walked

`Between` derived under `specimen.emitBasalt` as an enumerator, with a `DecOpt` premise, a recursive
constructor and the size-0 truncation label: at `Specimen.Search` its answer to every continuation is
the disjunction of what it lists at `ExceptT Exhaustion Finite` (`SearchesAs`), at every fuel and size.
Induction on the fuel the worker recurses on, and `walk` at each level, as for `EnumeratesWith`.
-/

set_option specimen.emitBasalt true

namespace DerivedSearchLaw

open Basalt Specimen

inductive Between : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, lo ≤ hi → Between lo hi lo
  | there : ∀ lo hi n, Between (lo + 1) hi n → Between lo hi n

#guard_msgs(drop info, drop warning) in
derive_mutual enumerator (fun lo hi => ∃ n, Between lo hi n)

/-- The derived `Between` enumerator, run as a search, answers every continuation as the disjunction
of what it lists, at every fuel and size. -/
theorem between_searchesAs : ∀ (fuel iS sz lo hi : Nat),
    SearchesAs (specimen_enum_DerivedSearchLaw_Between_2__SpecimenTest_Correctness_DerivedSearchLaw_DerivedSearchLaw (G := ExceptT Exhaustion Finite) fuel iS sz lo hi)
      (specimen_enum_DerivedSearchLaw_Between_2__SpecimenTest_Correctness_DerivedSearchLaw_DerivedSearchLaw (G := Search) fuel iS sz lo hi) := by
  intro fuel
  induction fuel with
  | zero => intro iS sz lo hi; unfold specimen_enum_DerivedSearchLaw_Between_2__SpecimenTest_Correctness_DerivedSearchLaw_DerivedSearchLaw; walk
  | succ fuel ih => intro iS sz lo hi; unfold specimen_enum_DerivedSearchLaw_Between_2__SpecimenTest_Correctness_DerivedSearchLaw_DerivedSearchLaw; walk [ih]

/-- info: 'DerivedSearchLaw.between_searchesAs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms between_searchesAs

end DerivedSearchLaw
