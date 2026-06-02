import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import SpecimenTest.DeriveDecOpt.DeriveSTLCChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveSTLCGenerator

/-! Test: multi-output constrained generation for STLC.

    Derives multi-output generators for lookup and typing using the standard
    `derive_generator` (which allows multiple existential outputs at the top level).
    Single-output sub-calls (e.g. TAdd's `typing Γ e .Nat`) use the instances
    already derived in DeriveSTLCGenerator. -/

open Plausible

set_option guard_msgs.diff true

-- Multi-output lookup (recursive — needs multiOutput for self-recursive sub-calls)
#guard_msgs(drop info, drop warning) in
derive_generator_multi (fun τ => ∃ (Γ : List type) (x : Nat), lookup Γ x τ)

#guard_msgs(drop info, drop warning) in
derive_generator_multi (∃ (Γ : List type) (x : Nat) (τ : type), lookup Γ x τ)

-- Multi-output typing: generates (term × type) given a context.
-- TAdd's sub-call `typing Γ e .Nat` uses the single-output instance from DeriveSTLCGenerator.
#guard_msgs(drop info, drop warning) in
derive_generator (fun Γ => ∃ (e : term) (τ : type), typing Γ e τ)

-- Verify the instance
#guard_msgs(drop info, drop warning) in
#check (inferInstance : ArbitrarySizedSuchThat (term × type) (fun (e, τ) => typing [] e τ))

-- Sample: generate a well-typed closed term along with its type
#eval do
  let sample ← Gen.run
    (ArbitrarySizedSuchThat.arbitrarySizedST (fun (p : term × type) => typing [] p.1 p.2) 5) 10
  return repr sample
