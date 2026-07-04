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
    let mut xs : List String := []
    for _ in List.range n.val do
      let v ← Arbitrary.arbitrary
      xs := v :: xs
    return xs

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

instance instKeyValueStoreArbitraryString : Arbitrary String where
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

#eval backwardOnlySizeOps

-----
-- DIFFERENTIAL TESTING USING TRACES
-----

-- Circular buffer implementation (mutable, using ST)

structure CircularBuffer where
  buf  : Array String
  head : Nat
  tail : Nat

def mkCircularBuffer (capacity : Nat) : IO (ST.Ref IO.RealWorld CircularBuffer) :=
  ST.mkRef { buf := Array.replicate (capacity + 1) "", head := 0, tail := 0 }

def mkCircularBufferBuggy (capacity : Nat) : IO (ST.Ref IO.RealWorld CircularBuffer) :=
  ST.mkRef { buf := Array.replicate capacity "", head := 0, tail := 0 }
  -- This implementation is buggy because it creates ambiguity: When
  -- head = tail, is the buffer empty or full?

def put (cb : ST.Ref IO.RealWorld CircularBuffer) (v : String) : IO Unit := do
  let s ← cb.get
  let newTail := (s.tail + 1) % s.buf.size
  -- COMMENT OUT THE NEXT TWO LINES TO SEE THE BUG (and the lines further down)
  if newTail == s.head then
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

def executeTrace (cb : ST.Ref IO.RealWorld CircularBuffer) : List BBAPI → IO Unit
  | [] => return ()
  | op :: ops => do
    match op with
    | .Put v => put cb v
    | .Get expected =>
      let actual ← get cb
      if actual != expected then
        throw <| IO.userError s!"Get mismatch: expected {repr expected}, got {repr actual}"
    | .Size expected =>
      let actual ← size cb
      if actual != expected then
        throw <| IO.userError s!"Size mismatch: expected {expected}, got {actual}"
    executeTrace cb ops

def differentialTest : IO Unit := do
  for i in List.range 100 do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => WF_BBTrace ([], 3) t s) 10) (i + 5)
    let cb ← mkCircularBuffer 3
    -- REPLACE THE ABOVE WITH THE LINE BELOW TO INTRODUCE A BUG
    -- let cb ← mkCircularBufferBuggy 3
    executeTrace cb trace

#guard_msgs in
#eval differentialTest

end BoundedBuffer
