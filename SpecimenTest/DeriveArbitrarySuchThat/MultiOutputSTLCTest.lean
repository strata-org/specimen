import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import SpecimenTest.DeriveDecOpt.DeriveSTLCChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveSTLCGenerator

/-! Test: multi-output constrained generation for STLC.
    Generate both a well-typed term AND its type given a context. -/

open Plausible

set_option guard_msgs.diff true

-- Generate both a term and its type given a context Γ (standard mode)
#guard_msgs(drop info, drop warning) in
derive_generator (fun Γ => ∃ (e : term) (τ : type), typing Γ e τ)

/-! ## Multi-output mode for non-recursive relations -/

-- Multi-output lookup: all three as outputs
#guard_msgs(drop info, drop warning) in
derive_generator_multi (∃ (Γ : List type) (x : Nat) (τ : type), lookup Γ x τ)

-- Multi-output lookup: τ as input, Γ and x as outputs
#guard_msgs(drop info, drop warning) in
derive_generator_multi (fun τ => ∃ (Γ : List type) (x : _), lookup Γ x τ)

-- Verify the instance type
#guard_msgs(drop info, drop warning) in
#check (inferInstance : ArbitrarySizedSuchThat (term × type) (fun (e, τ) => typing [] e τ))

-- Sample: generate a well-typed closed term along with its type
#eval do
  let sample ← Gen.run
    (ArbitrarySizedSuchThat.arbitrarySizedST (fun (p : term × type) => typing [] p.1 p.2) 5) 10
  return repr sample

-- Generate both an index and a type from a lookup judgment given a context
#guard_msgs(drop info, drop warning) in
derive_generator (fun Γ => ∃ (x : Nat) (τ : type), lookup Γ x τ)

-- Sample: generate a valid (index, type) pair for a non-empty context
#eval do
  let ctx : List type := [.Nat, .Fun .Nat .Nat, .Nat]
  let sample ← Gen.run
    (ArbitrarySizedSuchThat.arbitrarySizedST (fun (p : Nat × type) => lookup ctx p.1 p.2) 5) 10
  return repr sample
