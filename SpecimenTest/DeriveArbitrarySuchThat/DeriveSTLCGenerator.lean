import Plausible.Gen
import Specimen.DecOpt
import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import SpecimenTest.DeriveDecOpt.DeriveSTLCChecker
import Specimen.DeriveConstrainedProducer

/-! Snapshot test: derived constrained generator for well-typed STLC terms. -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

#guard_msgs(drop info) in
derive_generator (fun Γ τ => ∃ (x : Nat), lookup Γ x τ)

#guard_msgs(drop info) in
derive_generator (fun Γ x => ∃ (τ : type), lookup Γ x τ)

#guard_msgs(drop info) in
derive_generator (fun G e => ∃ (t : type), typing G e t)
-- set_option trace.plausible.deriving.results true
#guard_msgs(drop info) in
#time derive_generator (fun G t => ∃ (e : term), typing G e t)

-- To sample from this generator and print out 10 successful examples using the `Repr`
-- instance for `term`, we can run the following:
-- #eval Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => typing [] e $ .Fun .Nat .Nat) 3) 3

namespace STLCGeneratorTest

inductive Foo {α} [h : Inhabited α] : α → Prop where
| foo c : Foo c

#guard_msgs(drop info) in
derive_generator fun α [Inhabited α] => ∃ c : α, Foo c

end STLCGeneratorTest
