import Plausible.Arbitrary
import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary

/-! # Delegated producers and *repeated variables* in the equality premise.

    The delegated-producer path (see `DelegatedProducerTest`) lets the scheduler
    *produce* an output variable `v` out of an equality premise `lhs = rhs`
    whenever an `ArbitrarySizedSuchThat`/`EnumSizedSuchThat` instance resolves for
    the whole equality viewed as `fun v => lhs = rhs`. These tests cover how that
    path behaves when the output variable is *repeated* in the premise.

    ## Delegation only fires for the whole equality

    A variable is delegable only if a producer instance for the *entire* equality
    resolves. The generic library instances (`ArbitrarySizedSuchThat.lean`) are
    `fun x => x = val` and `fun x => val = x`, with `val` independent of the bound
    `x`. So a premise whose output sits under a function application whose head is
    not the bare variable — `f (g x) = true`, `h x = x`, `p x x = true` — does not
    delegate under the generic instances alone, and stays on the sound
    generate-and-test path (`Arbitrary` bind + `DecOpt` check). The `NoDelegation`
    section asserts these derivations still compile.

    ## Repeated variables when delegation does fire

    When a matching instance is supplied the output is produced from the equality,
    and a repeated variable has two sub-cases:

    - **Within one argument** — `f i i = true` (`f i i` is a single argument of
      `Eq`): `i` is contributed once, schedule `[i] ← (f i i) = true`.

    - **Across arguments** — `g i = i` (`i` is both the LHS argument `g i` and the
      bare RHS argument `i`): the whole equality is still delegated to a *single*
      producer call, so `i` must be bound exactly once, giving `[i] ← (g i) = i`.
      A delegable variable therefore occupies a single producible slot and is
      emitted a single time, regardless of how many argument positions it spans.
      The `CrossArg` and `NoArbitrary` sections exercise this; `NoArbitrary` in
      particular checks that no surplus unconstrained `Arbitrary` step is emitted
      for the repeat (which would spuriously require an `Arbitrary` instance for a
      value that is never used). -/

open Plausible

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true

namespace DelegatedProducerRepeatedVarTest

/-- A tiny term language with a de-Bruijn variable. -/
inductive Tm : Type where
  | var (i : Nat)
  deriving Repr, BEq

deriving instance Arbitrary for Tm

/-! ## `NoDelegation`: output under a function application, only generic instances.

    No equality-producer instance resolves for these predicates, so `i` is *not*
    delegable and the deriver uses generate-and-test. Each derivation should still
    compile (its soundness is the ordinary generate-and-test guarantee, covered by
    `GetElemPremiseTest`). -/

namespace NoDelegation

/-- Non-invertible inner function (no ASST instance for it). -/
def g (n : Nat) : Nat := n + 1
/-- Outer boolean predicate. -/
def f (n : Nat) : Bool := n % 2 == 0
/-- A function with the repeated-variable shape `h i = i`. -/
def h (n : Nat) : Nat := n * 2
/-- A binary boolean predicate for the `p i i` shape. -/
def p (a b : Nat) : Bool := a == b

/-- Output nested under two applications: `f (g i) = true`. -/
inductive S1 : Tm → Prop where
  | mk : f (g i) = true → S1 (.var i)

#guard_msgs(drop info) in
derive_generator (fun _u : Unit => ∃ e : Tm, S1 e)

/-- Repeated output across arguments, no matching instance: `h i = i`. -/
inductive S2a : Tm → Prop where
  | mk : h i = i → S2a (.var i)

#guard_msgs(drop info) in
derive_generator (fun _u : Unit => ∃ e : Tm, S2a e)

/-- Repeated output within one argument, no matching instance: `p i i = true`. -/
inductive S2b : Tm → Prop where
  | mk : p i i = true → S2b (.var i)

#guard_msgs(drop info) in
derive_generator (fun _u : Unit => ∃ e : Tm, S2b e)

end NoDelegation

/-! ## `WithinArg`: repeated variable within a single argument (`f i i = true`).

    A matching instance is supplied, so `i` is delegable. The repeat is within
    the single `Eq` argument `f i i`, so `i` is produced once: `[i] ← f i i = true`.
    The instance deterministically returns `0`, and `p 0 0 = true`, so every
    sample is `Tm.var 0` — witnessing that production really was delegated. -/

namespace WithinArg

def p (a b : Nat) : Bool := a == b

instance : ArbitrarySizedSuchThat Nat (fun i => p i i = true) where
  arbitrarySizedST _ := return 0

inductive R : Tm → Prop where
  | mk : p i i = true → R (.var i)

#guard_msgs(drop info) in
derive_generator (fun _u : Unit => ∃ e : Tm, R e)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let results ← (List.range 25).mapM (fun s =>
    Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => R e) 5) (s + 1))
  unless results.all (· == Tm.var 0) do
    throw (IO.userError s!"expected all `Tm.var 0` (delegation), got {repr results}")

end WithinArg

/-! ## `CrossArg`: delegable variable repeated across both arguments (`g i = i`).

    `g i = i` has the unique fixpoint `0` (`g 0 = 0`; `g` decrements otherwise),
    and the supplied instance returns it. `i` spans both `Eq` arguments (`g i` and
    the bare `i`) but is produced once, so the schedule is `[i] ← (g i) = i` and
    every sample is `Tm.var 0` — witnessing that production was delegated. -/

namespace CrossArg

def g (n : Nat) : Nat := if n = 0 then 0 else n - 1

instance : ArbitrarySizedSuchThat Nat (fun i => g i = i) where
  arbitrarySizedST _ := return 0

inductive R : Tm → Prop where
  | mk : g i = i → R (.var i)

#guard_msgs(drop info) in
derive_generator (fun _u : Unit => ∃ e : Tm, R e)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let results ← (List.range 25).mapM (fun s =>
    Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => R e) 5) (s + 1))
  unless results.all (· == Tm.var 0) do
    throw (IO.userError s!"expected all `Tm.var 0` (cross-arg delegation), got {repr results}")

end CrossArg

/-! ## `NoArbitrary`: cross-argument delegation for a type with **no** `Arbitrary`.

    A delegable variable that spans both arguments must be produced solely by the
    delegated call, with no surplus unconstrained `Arbitrary` step for the repeat.
    Here the delegable variable `i` has type `Idx`, which has an equality-producer
    instance but deliberately *no* `Arbitrary` instance: if a spurious `i ← Idx`
    step were emitted, derivation would fail to synthesize `Arbitrary Idx` for a
    value that is never used. The derivation should compile and every sample
    should be the fixpoint. -/

namespace NoArbitrary

/-- A type with an equality-producer instance below, but deliberately NO
    `Arbitrary` instance. -/
inductive Idx : Type where
  | mk (n : Nat)
  deriving Repr, BEq

def g (i : Idx) : Idx := match i with | .mk n => .mk (n - 1)

/-- Wrapper term whose variable carries an `Idx`. It has no `Arbitrary` instance
    either (that would require `Arbitrary Idx`); the delegated producer supplies
    the `Idx` directly. -/
inductive ITm : Type where
  | var (i : Idx)
  deriving Repr, BEq

/-- `g i = i` has the fixpoint `Idx.mk 0`; the instance returns it. -/
instance : ArbitrarySizedSuchThat Idx (fun i => g i = i) where
  arbitrarySizedST _ := return (.mk 0)

inductive R : ITm → Prop where
  | mk : g i = i → R (.var i)

-- Compiles with no `Arbitrary Idx` in scope: `i` is produced only by the
-- delegated call, so no unconstrained step requiring `Arbitrary Idx` is emitted.
#guard_msgs(drop info) in
derive_generator (fun _u : Unit => ∃ e : ITm, R e)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let results ← (List.range 25).mapM (fun s =>
    Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => R e) 5) (s + 1))
  unless results.all (· == ITm.var (.mk 0)) do
    throw (IO.userError s!"expected all `ITm.var (Idx.mk 0)`, got {repr results}")

end NoArbitrary

end DelegatedProducerRepeatedVarTest
