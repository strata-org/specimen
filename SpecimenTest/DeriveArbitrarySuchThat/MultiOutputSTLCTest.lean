import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import SpecimenTest.DeriveDecOpt.DeriveSTLCChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveSTLCGenerator

/-! Test: auto-derive dependency discovery for STLC.

    With `specimen.autoDeriveDeps true`, derive_mutual discovers that typing
    depends on lookup instances even when they're not explicitly listed. -/

open Plausible

set_option guard_msgs.diff true

-- Auto-derives missing lookup and typing sub-instances from a single top-level spec.
#guard_msgs(drop info) in
set_option specimen.autoDeriveDeps true in
derive_mutual
  (∃ (Γ : List type) (e : term) (τ : type), typing Γ e τ)

-- Sample: generate a valid (context, index) pair for a fixed type
#guard_msgs(drop info) in
#eval! do
  let sample ← Gen.run
    (ArbitrarySizedSuchThat.arbitrarySizedST (fun (p : List type × Nat) => lookup p.1 p.2 (.Fun (.Fun .Nat .Nat) .Nat)) 2) 2
  return repr sample
