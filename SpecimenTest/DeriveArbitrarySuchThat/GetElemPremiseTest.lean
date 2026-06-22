import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary

/-! Tests for `derive_generator` on inductive relations whose premises are
    headed by functions carrying unrepresentable implicit/instance arguments,
    such as list indexing (`xs[i]?`, i.e. `getElem?`).

    `getElem?` takes a "validity" argument that elaborates to the dependent
    lambda `fun as i => i < as.length`. Previously the schedule classifier
    (`exprToConstructorExpr`) tried to convert this lambda and aborted. The
    classifier now drops unrepresentable arguments in implicit/instance
    positions (replacing them with a hole that elaboration re-infers), so such
    premises classify like any other function application and reach the usual
    generate-and-test fallback (an `Arbitrary` binding plus a `DecOpt` check on
    the equality). -/

open Plausible

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true

/-- A tiny term language with a de-Bruijn variable. -/
inductive Tm : Type where
  | var (i : Nat)
  deriving Repr

deriving instance Arbitrary for Tm

/-- A typing relation whose `var` rule looks the variable's type up in the
    context by list indexing — `Γ[i]? = some τ` — rather than via an auxiliary
    inductive `lookup` relation. -/
inductive HasTy : List Nat → Tm → Nat → Prop where
  | var : Γ[i]? = some τ → HasTy Γ (.var i) τ

-- This previously failed with:
--   exprToConstructorExpr can only handle free variables, constants, and
--   applications. Attempted to convert: fun as i => i < as.length
-- It should now derive a generator (generate `i`, then check `Γ[i]? = some τ`).
#guard_msgs(drop info) in
derive_generator (fun Γ τ => ∃ e : Tm, HasTy Γ e τ)
