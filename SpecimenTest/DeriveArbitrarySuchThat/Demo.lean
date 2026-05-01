import Plausible.Arbitrary
import Specimen.Enumerators
import Plausible.DeriveArbitrary
import Specimen.DeriveEnum
import Specimen.GeneratorCombinators
import Specimen.EnumeratorCombinators
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveEnum
import Plausible.Gen
import SpecimenTest.CedarExample.CedarWellTypedTermGenerator

/-! Demo of constrained generator, enumerator, and checker derivation. -/

open Plausible
open Arbitrary

inductive Color where | red | green | blue
  deriving Repr, DecidableEq, Arbitrary

#eval printSamples Color

inductive Nat' where | zero | succ : Nat' → Nat'
  deriving Repr, DecidableEq, Arbitrary

#eval printSamples Nat'

inductive Cube : Nat → Prop where
| cube n : Cube (n * n * n)

derive_generator (∃ (m : _), Cube m)

theorem cubes_small {n} : Cube n → n <= 27 := sorry

#eval ArbitrarySizedSuchThat.printSamples (fun c => Cube c) 6

-- Test cubes_small with both generators
#eval do
  -- Test with regular Nat generator
  let natSamples := List.range 10
  let natResults ← natSamples.mapM (fun _ => runArbitrary (α := Nat) 10)
  let cubes := [0, 1, 8, 27, 64]
  IO.println s!"Nat samples: {natResults.map (fun n => (n, if n ∈ cubes then repr (decide (n <= 27)) else "discarded"))}"

  -- Test with Cube generator
  let cubeResults ← natSamples.mapM (fun _ => Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Cube n) 10) 10)
  IO.println s!"Cube samples: {cubeResults.map (fun n => (n, decide (n <= 27)))}"
