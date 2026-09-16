import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import Specimen.GeneratorCombinators
import Plausible.Attr

/-!
# Backward generation of state-machine traces

Generating API-call traces *backward*: given a desired end state, derive a trace of
operations and a consistent starting state that reaches it. The structure of the end state
drives each step, so this is construction rather than search.

The domain is a minimal key-value store — state is an association list newest-entry-first,
operations are `Set k v` / `Get k` / `Delete k`, results are `Ok` / `Found v` / `NotFound`.

`Trace s₁ ops s₂` is derived with `s₂` as the input and `ops`, `s₁` as outputs. Each `cons`
step picks an operation that could have produced the current target, inverts it to recover
the state before that operation, and recurses on that state. If the target holds `("A","1")`,
a backward `Set` step yields a predecessor lacking that entry, which becomes the next target.

The relations are written to make that inversion possible: separate arguments rather than
tupled input/output bundles, and no opaque function-call equalities, so each constructor can
be structurally decomposed instead of guessed.
-/

open Plausible

namespace BackwardTrace

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------

/-- API operations on the store. -/
inductive Op where
  | Set (k : String) (v : String)   -- upsert: add (k,v) to the front
  | Get (k : String)                 -- look up the first entry for key k
  | Delete (k : String)              -- remove all entries for key k
deriving Repr, DecidableEq

/-- Result of an operation. -/
inductive Res where
  | Ok                               -- Set / Delete always succeed
  | Found (v : String)               -- Get when key exists
  | NotFound                         -- Get / Delete when key absent
deriving Repr, DecidableEq

abbrev KVState := List (String × String)

----------------------------------------------------------------------
-- State-level sub-relations (invertible, separate args)
----------------------------------------------------------------------

/-- `HasKey k v s` — the first entry for `k` in `s` has value `v`. -/
inductive HasKey : String → String → KVState → Prop where
  | here  : ∀ k v rest,             HasKey k v ((k, v) :: rest)
  | there : ∀ k v k' v' rest,
      k ≠ k' → HasKey k v rest →    HasKey k v ((k', v') :: rest)

/-- `NoKey k s` — key `k` does not appear in `s`. -/
inductive NoKey : String → KVState → Prop where
  | nil  : ∀ k,                     NoKey k []
  | cons : ∀ k k' v rest,
      k ≠ k' → NoKey k rest →       NoKey k ((k', v) :: rest)

/-- `Removed k s s'` — `s'` is `s` with all `(k, _)` entries dropped. -/
inductive Removed : String → KVState → KVState → Prop where
  | nil  : ∀ k,                     Removed k [] []
  | drop : ∀ k v rest s',
      Removed k rest s' →           Removed k ((k, v) :: rest) s'
  | keep : ∀ k k' v rest s',
      k ≠ k' → Removed k rest s' →  Removed k ((k', v) :: rest) ((k', v) :: s')

----------------------------------------------------------------------
-- Step relation (separate args, no function calls)
----------------------------------------------------------------------

/-- `Step pre op result post` — one API-call step. All four arguments are
    independent, so the scheduler can fix any subset as inputs and produce
    the rest. -/
inductive Step : KVState → Op → Res → KVState → Prop where
  | set : ∀ k v s,
      Step s (Op.Set k v) Res.Ok ((k, v) :: s)
  | getOk : ∀ k v s,
      HasKey k v s →
      Step s (Op.Get k) (Res.Found v) s
  | getNotFound : ∀ k s,
      NoKey k s →
      Step s (Op.Get k) Res.NotFound s
  | deleteOk : ∀ k v s s',
      HasKey k v s →
      Removed k s s' →
      Step s (Op.Delete k) Res.Ok s'
  | deleteNotFound : ∀ k s,
      NoKey k s →
      Step s (Op.Delete k) Res.NotFound s

----------------------------------------------------------------------
-- Trace (separate args)
----------------------------------------------------------------------

/-- `Trace s₁ ops s₂` — running `ops` from state `s₁` lands in state `s₂`. -/
inductive Trace : KVState → List (Op × Res) → KVState → Prop where
  | nil  : ∀ s, Trace s [] s
  | cons : ∀ s1 op res s2 rest s3,
      Step s1 op res s2 →
      Trace s2 rest s3 →
      Trace s1 ((op, res) :: rest) s3

----------------------------------------------------------------------
-- Executable oracle (for soundness checks)
----------------------------------------------------------------------

/-- Apply a single operation to a state. Matches `Step` exactly. -/
def runOp (s : KVState) (op : Op) : KVState :=
  match op with
  | .Set k v => (k, v) :: s
  | .Get _   => s
  | .Delete k => s.filter (·.1 != k)

/-- Run a whole trace from a starting state. -/
def runTrace (s : KVState) (ops : List (Op × Res)) : KVState :=
  ops.foldl (fun st (op, _) => runOp st op) s

----------------------------------------------------------------------
-- Instances & Derivation
----------------------------------------------------------------------

instance : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault "A" ["A", "B", "C", "D"]

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

-- Forward generator: fix start state, generate trace + end state.
#guard_msgs(drop info) in
derive_mutual
  generator (fun (s1 : KVState) => ∃ ops s2, Trace s1 ops s2)

-- Backward generator: fix end state, generate trace + start state.
#guard_msgs(drop info) in
derive_mutual
  generator (fun (s3 : KVState) => ∃ ops s1, Trace s1 ops s3)

-- Test 1: target `[("A","1")]` has content, so backward chaining must produce traces that
-- construct it. Soundness is checked by running each trace forward through the oracle.

/-- info: PASS -/
#guard_msgs in
#eval (do
  let target : KVState := [("A", "1")]
  let mut nonTrivial := 0
  for i in List.range 200 do
    let size := 5 + i % 10
    match ← Gen.runChecked
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (s1, ops) => Trace s1 ops target) size) size with
    | .ok (s1, ops) =>
      if ops.length > 0 then
        nonTrivial := nonTrivial + 1
        -- Verify soundness: forward oracle must land on the target
        let landed := runTrace s1 ops
        if landed != target then
          throw <| IO.userError
            s!"UNSOUND: {repr s1} + {repr ops} → {repr landed} ≠ {repr target}"
    | _ => pure ()
  -- We expect a substantial fraction of non-trivial traces
  if nonTrivial < 50 then
    throw <| IO.userError s!"Too few non-trivial traces: {nonTrivial}/200"
  IO.println "PASS"
  : IO Unit)

-- Test 2: target `[]`. Reachable by Deletes from a richer predecessor and by Gets returning
-- NotFound. A Set can never be the last step, though Sets may appear earlier in the trace.

/-- info: PASS -/
#guard_msgs in
#eval (do
  let target : KVState := []
  let mut nonTrivial := 0
  for i in List.range 200 do
    let size := 5 + i % 10
    match ← Gen.runChecked
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (s1, ops) => Trace s1 ops target) size) size with
    | .ok (s1, ops) =>
      if ops.length > 0 then
        nonTrivial := nonTrivial + 1
        let landed := runTrace s1 ops
        if landed != target then
          throw <| IO.userError
            s!"UNSOUND: {repr s1} + {repr ops} → {repr landed} ≠ {repr target}"
    | _ => pure ()
  if nonTrivial < 50 then
    throw <| IO.userError s!"Too few non-trivial traces: {nonTrivial}/200"
  IO.println "PASS"
  : IO Unit)

-- Test 3: the other direction — start `[]` and let the end state be the output. Checks that
-- the generator reaches varied end states rather than only empty ones.

/-- info: PASS -/
#guard_msgs in
#eval (do
  let start : KVState := []
  let mut withData := 0
  for i in List.range 200 do
    let size := 5 + i % 10
    match ← Gen.runChecked
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (ops, s2) => Trace start ops s2) size) size with
    | .ok (ops, s2) =>
      -- Verify soundness
      let landed := runTrace start ops
      if landed != s2 then
        throw <| IO.userError
          s!"UNSOUND: {repr start} + {repr ops} → {repr landed} ≠ {repr s2}"
      if s2.length > 0 then withData := withData + 1
    | _ => pure ()
  -- Expect at least some traces that produce non-empty end states
  if withData < 20 then
    throw <| IO.userError s!"Too few traces with data: {withData}/200"
  IO.println "PASS"
  : IO Unit)

-- Test 4: a two-key target needs both `Set "A" "1"` and `Set "B" "2"`, ordered around any
-- intervening deletes — multi-step backward constraint propagation.

/-- info: PASS -/
#guard_msgs in
#eval (do
  let target : KVState := [("B", "2"), ("A", "1")]
  let mut nonTrivial := 0
  for i in List.range 200 do
    let size := 8 + i % 10
    match ← Gen.runChecked
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (s1, ops) => Trace s1 ops target) size) size with
    | .ok (s1, ops) =>
      if ops.length > 0 then
        nonTrivial := nonTrivial + 1
        let landed := runTrace s1 ops
        if landed != target then
          throw <| IO.userError
            s!"UNSOUND: {repr s1} + {repr ops} → {repr landed} ≠ {repr target}"
    | _ => pure ()
  if nonTrivial < 30 then
    throw <| IO.userError s!"Too few non-trivial traces: {nonTrivial}/200"
  IO.println "PASS"
  : IO Unit)

end BackwardTrace
