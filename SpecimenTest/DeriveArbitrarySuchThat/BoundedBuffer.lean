import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators

open Plausible

namespace BoundedBuffer

-- Bounded Queue: Specification

abbrev BB := (List String) × Nat

inductive BBAPI where
| Put (s_in : String)
| Get (s_out : String)
| Size (n_out : Nat)
deriving Repr

inductive WithinCapacity : List String → Nat → Prop where
| mk : s.length ≤ c → WithinCapacity s c

instance (s : List String) (c : Nat) : DecOpt (WithinCapacity s c) where
  decOpt _ := if s.length ≤ c then .ok true else .ok false

instance (c : Nat) : ArbitrarySizedSuchThat (List String) (fun s => WithinCapacity s c) where
  arbitrarySizedST _ := do
    let n ← Gen.choose Nat 0 c (by omega)
    (List.range n.val).mapM (fun _ => Arbitrary.arbitrary)

inductive BBStep : BB → BBAPI → BB → Prop where
-- NOTE: We write `WithinCapacity (v :: s) c` rather than the equivalent
-- `WithinCapacity s' c` (with `s' = List.concat s v`). The scheduler should
-- be able to bind s' via the equality first and then DecOpt-check it, but
-- currently it fails to generate Put operations in that formulation.
-- Possible bug: the scheduler doesn't recognize that a DecOpt premise on an
-- output variable can be scheduled after an equality that fully determines it.
| PutOp: ∀ s s' c v,
    WithinCapacity (v :: s) c →
    s' = List.concat s v →
    BBStep (s,c) (BBAPI.Put v) (s',c)
| GetOp: ∀ s c v,
    WithinCapacity (v :: s) c → BBStep (v :: s, c) (BBAPI.Get v) (s,c)
| SizeOp: ∀ s c,
    WithinCapacity s c → BBStep (s,c) (BBAPI.Size (List.length s)) (s,c)

abbrev BBTrace := List BBAPI

inductive WF_BBTrace : BB -> BBTrace -> BB -> Prop where
| WF_Empty: ∀ s c, WithinCapacity s c → WF_BBTrace (s,c) [] (s,c)
| WF_Op: ∀ s s' s'' p ps,
    BBStep s p s' ->
    WF_BBTrace s' ps s'' ->
    WF_BBTrace s (p::ps) s''

-- Generating well formed traces

instance instArbitraryString : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault "A" ["A", "B", "C", "D", "E", "F", "G", "H", "I"]

set_option specimen.multiOutput true in
set_option specimen.autoDeriveDeps true in
set_option match.ignoreUnusedAlts true in
derive_mutual
  (fun i => ∃ t s, WF_BBTrace i t s),
  (fun s => ∃ t i, WF_BBTrace i t s)

-- The backward generator (fun s => ∃ t i, WF_BBTrace i t s) is poor quality:
-- it relies on guess-and-check for GetOp and PutOp (randomly generating lists
-- and hoping they satisfy WithinCapacity), so in practice it only produces
-- SizeOp operations. When the target final state is already at capacity, GetOp
-- and PutOp both require generating valid pre-states that the scheduler can't
-- efficiently construct.
def backwardOnlySizeOps : IO Unit := do
  for i in List.range 100 do
    let (_, trace) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (s, t) => WF_BBTrace s t (["A", "B", "C"], 3)) 10) (i + 5)
    let allSize := trace.all fun
      | .Size _ => true
      | _ => false
    if !allSize then
      throw <| IO.userError s!"Expected only SizeOp in backward trace, got: {repr trace}"

#guard_msgs in
#eval backwardOnlySizeOps

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

def get (cb : ST.Ref IO.RealWorld CircularBuffer) : IO String := do
  let s ← cb.get
  let v := s.buf[s.head]!
  cb.set { s with head := (s.head + 1) % s.buf.size }
  return v

def size (cb : ST.Ref IO.RealWorld CircularBuffer) : IO Nat := do
  let s ← cb.get
  return (s.tail + s.buf.size - s.head) % s.buf.size

-- Differentially test the mutable implementation against the specification

def executeTrace (cb : ST.Ref IO.RealWorld CircularBuffer) (buggy : Bool := false) : List BBAPI → IO Unit
  | [] => return ()
  | op :: ops => do
    match op with
    | .Put v => put cb v buggy
    | .Get expected =>
      let actual ← get cb
      if actual != expected then
        throw <| IO.userError s!"Get mismatch: expected {repr expected}, got {repr actual}"
    | .Size expected =>
      let actual ← size cb
      if actual != expected then
        throw <| IO.userError s!"Size mismatch: expected {expected}, got {actual}"
    executeTrace cb buggy ops

def differentialTest (buggy : Bool := false) : IO Unit := do
  for i in List.range 1000 do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => WF_BBTrace ([], 3) t s) 10) (i + 5)
    let cb ← mkCircularBuffer 3 buggy
    executeTrace cb buggy trace

-- Correct implementation passes
#guard_msgs in
#eval differentialTest

-- Buggy implementation is detected
/--error: Size mismatch: expected 3, got 0-/
#guard_msgs(error, drop info) in
#eval differentialTest (buggy := true)

end BoundedBuffer

/-
## Next steps: Testing error handling (non-well-formed traces)

The current tests confirm that well-formed traces (generated via `WF_BBTrace`)
execute correctly against the circular buffer implementation. The next goal is
to also confirm that *non*-well-formed traces produce errors — i.e., that the
imperative implementation correctly rejects invalid operations (putting into a
full buffer, getting from an empty one).

### The challenge

`BBAPI` currently embeds expected outputs (`Get s_out`, `Size n_out`) directly
in the operation. This conflates two concerns:
  1. What *command* the caller issues (Put a value, Get, query Size)
  2. What *result* the system should produce (the dequeued value, the count)

For well-formed trace testing this is fine: the generator produces commands with
their correct expected results baked in. But for error testing we need to
generate *arbitrary* command sequences — including ones that violate
preconditions — without needing to know the correct output in advance.

### Proposed refactoring

Separate the command from the observation:

```
inductive BBCmd where
| Put (v : String)
| Get
| Size

inductive BBResult where
| PutOk
| GetOk (v : String)
| SizeOk (n : Nat)
| Error (msg : String)
```

The specification (`BBStep`) would relate a state and a `BBCmd` to a
`BBResult` and a next state. A trace is then `List BBCmd`, and executing it
against the imperative implementation produces a `List BBResult`.

This idea is similar to what's done in [quickcheck-state-machine](https://github.com/stevana/quickcheck-state-machine#readme)

### Testing strategy

1. **Generate arbitrary `List BBCmd`**: Random sequences of Put/Get/Size with
   random arguments, without regard to well-formedness. Use `deriving Arbitrary`
   for `BBCmd`.

2. **Execute against both models in lockstep**: For each command in the trace,
   run it against:
   - The abstract model (list-based state), which determines whether the
     operation is valid and what the correct result is.
   - The imperative circular buffer.

3. **Compare outcomes at each step**:
   - If the abstract model says the command is valid: the imperative code
     should succeed with the same result.
   - If the abstract model says the command is invalid (Get on empty, Put on
     full): the imperative code should raise an error.
   - If the imperative code raises an error when the abstract model says it
     should succeed (or vice versa): test failure.

4. **Derive a checker**: Use `derive_checker` for `BBStep` so we can
   efficiently validate whether a given (state, command, result, next-state)
   tuple is a valid transition. This would let us check well-formedness of
   prefixes without maintaining the abstract state by hand — though for this
   test the manual abstract-state approach may be simpler.

### Open questions

- Should `Size` ever be "invalid"? In the current spec it always succeeds
  (querying size has no precondition beyond `WithinCapacity`). If we keep
  `WithinCapacity` on `SizeOp`, then Size on a state that somehow violates
  capacity is invalid — but that can't happen if we start from a valid state
  and only apply valid operations. So Size errors would only arise if the
  implementation itself corrupted state.

- Do we need to test Get with a *wrong* expected value, or just Get on an
  empty buffer? The former tests output correctness (already covered by
  `executeTrace`), the latter tests precondition enforcement. With the
  `BBCmd`/`BBResult` split, this distinction becomes natural.

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
