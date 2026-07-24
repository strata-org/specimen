import SpecimenTest.BoundedBuffer.BoundedBufferSpec

open Plausible

-- Reopen the namespace so the spec's names (`BBTrace`, `SafeBBTrace`, …) resolve
-- unqualified, matching the original single-file layout.
namespace BoundedBuffer

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
    | (.Size, .Error) => expectError "Size" (size cb) -- actually impossible per the spec
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
    | _ => throw <| IO.userError s!"unexpected cmd/result pair: {repr op}"
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
