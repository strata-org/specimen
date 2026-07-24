import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators

open Plausible

-- All definitions live under the `BoundedBuffer` namespace. This is not merely
-- cosmetic: `derive_mutual` with `autoDeriveDeps` emits auto-named dependency
-- instances (e.g. an `EnumSizedSuchThat` for `Eq`), and without a namespace those
-- names (`instEnumSizedSuchThatEq_specimenTest`) collide at import time with the
-- identically-named instance derived in `DeriveEnumSuchThat/DeriveRegExpMatchEnumerator`.
-- The namespace prefixes the generated names and keeps them distinct.
namespace BoundedBuffer

-- Bounded Queue: Specification

abbrev BB := (List String) × Nat

inductive BBCmd where
| Put (v : String)
| Get
| Size
deriving Repr

inductive BBResult where
| PutOk
| GetOk (v : String)
| SizeOk (n : Nat)
| Error
deriving Repr

abbrev BBTrace := List (BBCmd × BBResult)

inductive WithinCapacity : List String → Nat → Prop where
| mk : s.length ≤ c → WithinCapacity s c

-- Evaluation without error; error'ing evaluation defined further down
inductive BBSafeStep : BB → BBCmd → BBResult → BB → Prop where
-- NOTE: We write `WithinCapacity (v :: s) c` rather than the equivalent
-- `WithinCapacity s' c` (with `s' = List.concat s v`). The scheduler should
-- be able to bind s' via the equality first and then DecOpt-check it, but
-- currently it fails to generate Put operations in that formulation.
-- Possible bug: the scheduler doesn't recognize that a DecOpt premise on an
-- output variable can be scheduled after an equality that fully determines it.
| PutOp: ∀ s s' c v,
    WithinCapacity (v :: s) c →
    s' = List.concat s v →
    BBSafeStep (s,c) (BBCmd.Put v) BBResult.PutOk (s',c)
| GetOp: ∀ s c v,
    WithinCapacity (v :: s) c → BBSafeStep (v :: s, c) BBCmd.Get (BBResult.GetOk v) (s,c)
| SizeOp: ∀ s c,
    WithinCapacity s c → BBSafeStep (s,c) BBCmd.Size (BBResult.SizeOk (List.length s)) (s,c)

-- Error-free trace
inductive SafeBBTrace : BB -> BBTrace -> BB -> Prop where
| WF_Empty: ∀ s c, WithinCapacity s c → SafeBBTrace (s,c) [] (s,c)
| WF_Op: ∀ s s' s'' cmd res ps,
    BBSafeStep s cmd res s' ->
    SafeBBTrace s' ps s'' ->
    SafeBBTrace s ((cmd, res)::ps) s''

-- Generating safe traces (no ErrResult ever generated)

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

instance (s : List String) (c : Nat) : DecOpt (WithinCapacity s c) where
  decOpt _ := if s.length ≤ c then .ok true else .ok false

instance (c : Nat) : ArbitrarySizedSuchThat (List String) (fun s => WithinCapacity s c) where
  arbitrarySizedST _ := do
    let n ← Gen.choose Nat 0 c (by omega)
    (List.range n.val).mapM (fun _ => Arbitrary.arbitrary)

-- The backward direction of `SafeBBTrace` must generate a capacity `c` from a
-- given list `s`; it needs a capacity that admits the list (`s.length ≤ c`).
-- When both directions were co-derived in one `derive_mutual`, this dependency
-- was synthesized in that shared context; now that `BackwardGenerator` derives
-- the backward direction on its own, we provide the instance explicitly here.
instance (s : List String) : ArbitrarySizedSuchThat Nat (fun c => s.length ≤ c) where
  arbitrarySizedST _ := do
    let extra ← Gen.choose Nat 0 s.length (by omega)
    return s.length + extra

instance instArbitraryString : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault "A" ["A", "B", "C", "D", "E", "F", "G", "H", "I"]

-- An unconstrained `Arbitrary BBCmd` is needed by `BBStep.ErrStep`, which
-- generates a command freely and then checks `¬ CanStep`.
deriving instance Arbitrary for BBCmd

-- Only the forward generator is derived here. The (poor-quality) backward
-- generator `(fun s => ∃ t i, SafeBBTrace i t s)` lives in `BackwardGenerator`.
#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun i => ∃ t s, SafeBBTrace i t s)

-- Generating traces that admit errors (via `BBStep` / `EveryBBTrace`).

-- `CanStep bb c` reifies the existential `∃ r bb', BBSafeStep bb c r bb'` as a named
-- inductive. This is needed so that the negated premise in `BBStep.ErrStep`
-- reads as `¬ CanStep bb c` (a `Not` applied to an inductive head), which the
-- scheduler can lower to a negated check. Writing `¬(∃ r bb', ...)` directly
-- fails: the scheduler's `Not`-unwrapping expects a constructor/inductive head
-- under the `Not`, but finds a bare `Exists`-lambda that `exprToConstructorExpr`
-- cannot classify. The derived `DecOpt (CanStep bb c)` is backed by an
-- enumerator of the `BBSafeStep` witnesses (enumerate, succeed if any exists), so
-- `¬ CanStep` becomes "enumerate all steps; there are none".
inductive CanStep : BB → BBCmd → Prop where
| intro : ∀ bb c r bb', BBSafeStep bb c r bb' → CanStep bb c

inductive BBStep : BB → BBCmd → BBResult → BB → Prop where
| SafeStep: ∀ bb c r bb', BBSafeStep bb c r bb' → BBStep bb c r bb'
| ErrStep: ∀ bb c, ¬ CanStep bb c → BBStep bb c BBResult.Error bb

inductive EveryBBTrace : BB -> BBTrace -> BB -> Prop where
| All_Empty: ∀ s c, EveryBBTrace (s,c) [] (s,c)
| All_Op: ∀ s s' s'' cmd res ps,
    BBStep s cmd res s' ->
    EveryBBTrace s' ps s'' ->
    EveryBBTrace s ((cmd, res)::ps) s''

#guard_msgs(drop info, drop warning) in
derive_mutual
  generator (fun i => ∃ t s, EveryBBTrace i t s)

end BoundedBuffer

/-

### Open questions

- The `WithinCapacity` guard on `GetOp` and `SizeOp` was added to constrain
  the backward generator. For error testing it means the spec considers *any*
  operation on an over-capacity state invalid, even though that state can't
  arise in practice. We may want to distinguish "unreachable invalid" from
  "reachable invalid" (Get on empty, Put on full).

### Note from ErnestNG

I wonder if an alternative approach is to interleave generation with execution,
i.e. build up the command sequence one instruction at a time, and at each step:

1. Determine what the set of callable commands is given the current state
(i.e. the set of instructions that won't cause a crash in the current state)
2. Sample a random command from this set
3. Execute this command on both the model + implementation
4. Repeat steps 1-3 above

In the [Testing Noninterference Quickly](https://catalin-hritcu.github.io/publications/testing-noninterference-icfp2013.pdf) paper (Hritcu et al. ICFP '13), they
call this technique "generation by execution", and it seems to be effective
for their use case (generating stack machine instruction sequences that don't
cause a crash in order to test noninterference).

One of Leo's MS students at UMD also uses this "generation by execution"
technique to generate random API calls to test a C queue implementation
(section 3 of [this MS thesis](https://drum.lib.umd.edu/items/894f193b-3791-4d0a-900b-86363cbae75f)).

I wonder if it's possible for a Specimen-derived generator to embody this
"generation by execution" paradigm, or if this is fundamentally impossible,
since it requires interleaving generation and execution and a Specimen
generator only generates commands ahead of time.

-/
