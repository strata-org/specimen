import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import SpecimenTest.DeriveDecOpt.DeriveSTLCChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveSTLCGenerator

/-! Test: mutual multi-output constrained generation for STLC.

    Uses derive_mutual to derive all input/output splits of `typing` and `lookup`
    simultaneously. The mutual block handles circular dependencies between
    "all outputs" typing (needs "τ fixed" for TAdd) and
    "τ fixed" typing (needs "all outputs" for TApp). -/

open Plausible

set_option guard_msgs.diff true

-- Derive all mutual dependencies together
#guard_msgs(drop info, drop warning) in
derive_mutual
  (∃ (Γ : List type) (x : Nat) (τ : type), lookup Γ x τ),
  (fun τ => ∃ (Γ : List type) (x : Nat), lookup Γ x τ),
  (∃ (Γ : List type) (e : term) (τ : type), typing Γ e τ),
  (fun τ => ∃ (Γ : List type) (e : term), typing Γ e τ)

-- -- Verify instances
-- #guard_msgs(drop info, drop warning) in
-- #check (inferInstance : ArbitrarySizedSuchThat (List type × term × type) (fun (Γ, e, τ) => typing Γ e τ))

-- #guard_msgs(drop info, drop warning) in
-- #check (inferInstance : ArbitrarySizedSuchThat (List type × term) (fun (Γ, e) => typing Γ e .Nat))

-- -- Sample: generate a well-typed term with its context and type
-- #eval! do
--   let sample ← Gen.run
--     (ArbitrarySizedSuchThat.arbitrarySizedST (fun (p : List type × term × type) => typing p.1 p.2.1 p.2.2) 3) 10
--   return repr sample

/-! ## Dependency discovery example

    With `specimen.autoDeriveDeps true`, derive_mutual discovers that typing
    depends on lookup instances even when they're not explicitly listed.
    Currently reports what's needed; full auto-derivation is WIP. -/

-- With autoDeriveDeps, derive_mutual auto-derives missing lookup and typing[1] deps.
-- Note: typing[1,2] must still be listed explicitly (schedule-dependent discovery limitation).
#guard_msgs(drop info, drop warning) in
set_option specimen.autoDeriveDeps true in
derive_mutual
  (∃ (Γ : List type) (e : term) (τ : type), typing Γ e τ),
  (fun τ => ∃ (Γ : List type) (e : term), typing Γ e τ),
  (fun Γ => ∃ (e : term) (τ : type), typing Γ e τ)
