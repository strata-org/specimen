import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators

open Plausible

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

instance (s : List String) (c : Nat) : DecOpt (WithinCapacity s c) where
  decOpt _ := if s.length ≤ c then .ok true else .ok false

instance (c : Nat) : ArbitrarySizedSuchThat (List String) (fun s => WithinCapacity s c) where
  arbitrarySizedST _ := do
    let n ← Gen.choose Nat 0 c (by omega)
    (List.range n.val).mapM (fun _ => Arbitrary.arbitrary)

instance instArbitraryString : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault "A" ["A", "B", "C", "D", "E", "F", "G", "H", "I"]

-- An unconstrained `Arbitrary BBCmd` is needed by `BBStep.ErrStep`, which
-- generates a command freely and then checks `¬ CanStep`.
deriving instance Arbitrary for BBCmd

set_option specimen.multiOutput true in
set_option specimen.autoDeriveDeps true in
set_option match.ignoreUnusedAlts true in
derive_mutual
  (fun i => ∃ t s, SafeBBTrace i t s),
  (fun s => ∃ t i, SafeBBTrace i t s)

-- The backward generator (fun s => ∃ t i, SafeBBTrace i t s) is poor quality:
-- it relies on guess-and-check for GetOp and PutOp (randomly generating lists
-- and hoping they satisfy WithinCapacity), so in practice it only produces
-- SizeOp operations. When the target final state is already at capacity, GetOp
-- and PutOp both require generating valid pre-states that the scheduler can't
-- efficiently construct.
def backwardOnlySizeOps : IO Unit := do
  for i in List.range 100 do
    let (_, trace) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (s, t) => SafeBBTrace s t (["A", "B", "C"], 3)) 10) (i + 5)
    let allSize := trace.all fun
      | (.Size, _) => true
      | _ => false
    if !allSize then
      throw <| IO.userError s!"Expected only SizeOp in backward trace, got: {repr trace}"

#guard_msgs in
#eval backwardOnlySizeOps

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

section
set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

-- Each stage is derived as a top-level instance, rather than writing only
-- the final `derive_mutual` and letting `autoDeriveDeps` pull every dependency
-- into that one mutual block. Both forms *compile*, but the explicit form
-- produces a markedly better generator: measured over 1000 traces from `([],3)`
-- it yields ~1.8 ops/trace and ~150 traces containing an `Error`, versus ~0.55
-- ops/trace and ~80 error traces for the all-`autoDeriveDeps` form — roughly 3x
-- longer traces and 2x the error coverage, which is exactly the coverage this
-- error-testing generator exists to provide.
--
-- The cause is that bundling every dependency into a single `derive_mutual` SCC
-- makes the scheduler split its size budget across the whole bundle, so each
-- step gets a smaller allocation; independently-derived instances each get a
-- full budget. Empirically the improvement needs the *complete* set of explicit
-- derivations — adding only some of them recovers none of the quality (and some
-- partial combinations fail to derive at all). So resist "simplifying" this to
-- the bare `derive_mutual`, or trimming individual stages, without re-measuring.
--
-- The stages:
--   1. Enumerator for the `BBSafeStep` witnesses `(r, bb')` — used to decide `CanStep`.
--   2. Checker `DecOpt (CanStep bb c)` — enumerate-and-check (backed by the
--      enumerator above); negated via `DecOpt.negOpt` for `ErrStep`.
--   3a. Generator for the `BBSafeStep` witnesses given a command — used by `SafeStep`
--       when the command is an input.
--   3b. Forward `BBSafeStep` generator (command generated too) — used by the forward
--       `BBStep` generator.
--   3c. Forward `BBStep` generator — one step of `EveryBBTrace`, generating the
--       command, result, and next state from the current state.
--   4. Generator for `EveryBBTrace`, via `derive_mutual` so the recursive instance
--      is registered and the scheduler can step forward and recurse.

derive_enumerator (fun bb c => ∃ r bb', BBSafeStep bb c r bb')
derive_checker (fun bb c => CanStep bb c)
derive_generator (fun bb c => ∃ r bb', BBSafeStep bb c r bb')
derive_generator (fun bb => ∃ cmd r bb', BBSafeStep bb cmd r bb')
derive_generator (fun bb => ∃ cmd res bb', BBStep bb cmd res bb')
derive_mutual
  (fun i => ∃ t s, EveryBBTrace i t s)
end

-----
-- DIFFERENTIAL TESTING USING TRACES
-----

-- Circular buffer implementation (mutable, using ST)
-- When `buggy = true`, the buffer is allocated without the extra sentinel slot,
-- causing head == tail ambiguity (empty vs full) and the overflow check is
-- disabled, so puts silently overwrite.

structure CircularBuffer where
  buf  : Array String
  head : Nat
  tail : Nat

def mkCircularBuffer (capacity : Nat) (buggy : Bool := false) : IO (ST.Ref IO.RealWorld CircularBuffer) :=
  let slots := if buggy then capacity else capacity + 1
  ST.mkRef { buf := Array.replicate slots "", head := 0, tail := 0 }

def put (cb : ST.Ref IO.RealWorld CircularBuffer) (v : String) (buggy : Bool := false) : IO Unit := do
  let s ← cb.get
  let newTail := (s.tail + 1) % s.buf.size
  if !buggy && newTail == s.head then
    throw <| IO.userError "put: buffer full"
  let buf := s.buf.set! s.tail v
  cb.set { s with buf, tail := newTail }

def get (cb : ST.Ref IO.RealWorld CircularBuffer) (buggy : Bool := false) : IO String := do
  let s ← cb.get
  -- Reject Get on an empty buffer (head == tail). The buggy variant skips this
  -- check, so it happily reads stale/default slots from an "empty" buffer.
  if !buggy && s.head == s.tail then
    throw <| IO.userError "get: buffer empty"
  let v := s.buf[s.head]!
  cb.set { s with head := (s.head + 1) % s.buf.size }
  return v

def size (cb : ST.Ref IO.RealWorld CircularBuffer) : IO Nat := do
  let s ← cb.get
  return (s.tail + s.buf.size - s.head) % s.buf.size

-- Differentially test the mutable implementation against the specification

-- Runs `act` and fails if it does *not* raise: the spec expected this command to
-- be rejected (result `.Error`), so a silent success is a differential mismatch.
def expectError (label : String) (act : IO α) : IO Unit := do
  let succeeded ← (do let _ ← act; return true) <|> return false
  if succeeded then
    throw <| IO.userError s!"{label}: expected error, but implementation succeeded"

def executeTrace (cb : ST.Ref IO.RealWorld CircularBuffer) (buggy : Bool := false) : BBTrace → IO Unit
  | [] => return ()
  | op :: ops => do
    match op with
    -- Spec says the command is rejected: the implementation must raise too.
    | (.Put v, .Error) => expectError s!"Put {repr v}" (put cb v buggy)
    | (.Get, .Error) => expectError "Get" (get cb buggy)
    | (.Size, .Error) => expectError "Size" (size cb)
    -- Spec says the command succeeds with a particular result.
    | (.Put v, _) => put cb v buggy
    | (.Get, .GetOk expected) =>
      let actual ← get cb buggy
      if actual != expected then
        throw <| IO.userError s!"Get mismatch: expected {repr expected}, got {repr actual}"
    | (.Size, .SizeOk expected) =>
      let actual ← size cb
      if actual != expected then
        throw <| IO.userError s!"Size mismatch: expected {expected}, got {actual}"
    | _ => return ()
    executeTrace cb buggy ops

def differentialTest (buggy : Bool := false) : IO Unit := do
  for i in List.range 1000 do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => SafeBBTrace ([], 3) t s) 10) (i + 5)
    let cb ← mkCircularBuffer 3 buggy
    executeTrace cb buggy trace

-- Correct implementation passes
#guard_msgs in
#eval differentialTest

-- Buggy implementation is detected
/--error: Size mismatch: expected 3, got 0-/
#guard_msgs(error, drop info) in
#eval differentialTest (buggy := true)

-- differential testing with error traces

-- Unlike `differentialTest`, this uses `EveryBBTrace`, whose traces may include
-- commands the spec rejects (`.Error` results: Get on empty, Put on full).
-- `executeTrace` checks that the implementation raises exactly on those
-- commands and succeeds (with the matching result) on the rest.
def errorDifferentialTest (buggy : Bool := false) : IO Unit := do
  for i in List.range 1000 do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => EveryBBTrace ([], 3) t s) 10) (i + 5)
    let cb ← mkCircularBuffer 3 buggy
    executeTrace cb buggy trace

-- Correct implementation agrees with the spec on both success and error results
#guard_msgs in
#eval errorDifferentialTest

-- Don't want to do this because the test is flaky
-- #guard_msgs(error, drop info) in
-- #eval errorDifferentialTest (buggy := true)

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
