import Plausible.Arbitrary
import Plausible.Gen
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary

/-! Tests for *delegated producers*.

    When an equality premise constrains an output variable through a function
    application that cannot be inverted (e.g. `Γ[i]? = some τ`, list indexing),
    the deriver checks whether an `ArbitrarySizedSuchThat` instance exists for
    the whole equality, viewed as a property of the output variable
    (`fun i => Γ[i]? = some τ`). If so, it *delegates* production of the output
    to that instance instead of falling back to generate-and-test (generate the
    variable unconstrained, then filter with a `DecOpt` check).

    The complementary no-instance case (generate-and-test fallback) is covered
    by `GetElemPremiseTest`. -/

open Plausible

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true

/-- A tiny term language with a de-Bruijn variable. -/
inductive DTm : Type where
  | var (i : Nat)
  deriving Repr, BEq

deriving instance Arbitrary for DTm

/-- A hand-written delegated producer for the list-indexing lookup. It is
    *deterministic*: it always returns the **last** index of `Γ` whose entry is
    `τ` (or `0` if none). This determinism is what the test below keys on:
    generate-and-test would return assorted random indices, so observing the
    same specific index every time witnesses that production was delegated to
    this instance. -/
instance (Γ : List Nat) (τ : Nat) :
    ArbitrarySizedSuchThat Nat (fun i => Γ[i]? = some τ) where
  arbitrarySizedST _ := do
    return ((List.range Γ.length).filter (fun i => Γ[i]? = some τ)).getLast?.getD 0

inductive DHasTy : List Nat → DTm → Nat → Prop where
  | var : Γ[i]? = some τ → DHasTy Γ (.var i) τ

-- Derivation succeeds with the delegated instance in scope.
#guard_msgs(drop info) in
derive_generator (fun Γ τ => ∃ e : DTm, DHasTy Γ e τ)

-- With context `[7, 7, 7]` and target `7`, the delegated instance always
-- returns the last matching index, `2`. If production had instead fallen back
-- to generate-and-test, the index would vary with the seed. We sample across
-- many seeds and confirm every result is exactly `DTm.var 2`, witnessing
-- delegation. (`Gen.run` throws on generation failure, so a non-`var 2` result
-- — or a failure — makes this `#eval` error and the test fail.)
#guard_msgs(drop info) in
#eval show IO Unit from do
  let results ← (List.range 25).mapM (fun s =>
    Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
      (fun e => DHasTy [7, 7, 7] e 7) 5) (s + 1))
  unless results.all (· == DTm.var 2) do
    throw (IO.userError s!"expected all `DTm.var 2` (delegation), got {repr results}")
