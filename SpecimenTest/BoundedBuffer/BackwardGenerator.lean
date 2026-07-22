import SpecimenTest.BoundedBuffer.BoundedBufferSpec

open Plausible

-- Reopen the namespace so the spec's names resolve unqualified, and so this
-- file's own `derive_mutual` auto-named instances are prefixed (avoiding the
-- import-time collision described in `BoundedBufferSpec.lean`).
namespace BoundedBuffer

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

-- The backward generator (fun s => ∃ t i, SafeBBTrace i t s) is poor quality:
-- it relies on guess-and-check for GetOp and PutOp (randomly generating lists
-- and hoping they satisfy WithinCapacity), so in practice it only produces
-- SizeOp operations. When the target final state is already at capacity, GetOp
-- and PutOp both require generating valid pre-states that the scheduler can't
-- efficiently construct.

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun s => ∃ t i, SafeBBTrace i t s)

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

end BoundedBuffer
