import Specimen.Interp.Correspondence
import SpecimenTest.Interp.BSTInterpTest

/-!
# The interpreter's leaves against the instances Lean can synthesise

`InterpEnv.correspondence` exists because the two drifted silently and the consequences were hard to
trace back. On Cedar it reported **21** disagreements; closing them took fifteen leaves, and six of the
twenty-one turned out to be false positives from an index-base bug in the check itself.

This pins the expected report for `BSTInterpTest`'s `leaves`, which is *not* clean — and should not be.
`Between` has a checker leaf and no `DecOpt Between` instance, and that single fact explains a failure
that took a long time to read back to its cause:

* the interpreter satisfies `Between[1,2]` from the leaf and brings up **3** modes;
* the compiled path must build `Between` from its definition, brings up **12**, and fails three `LE.le`
  modes with "not inductive and has no Decidable instance";
* which surfaces, far downstream, as `failed to synthesize ArbitrarySizedSuchThat Nat (fun m => a_3 ≤ m)`
  — naming neither `Between` nor the leaf responsible.

So pinning it is the point: this is why `PinnedOrderTest`'s `[1,0,2]` order lowers identically on both
sides and still cannot be *emitted*. Should someone add a `DecOpt Between` instance, this test fails and
says so, which is the correct outcome — the pinning restriction would have lifted.
-/

open Lean Schedules Specimen Specimen.Interp SpecimenTest.InterpBST

namespace SpecimenTest.Correspondence

/-- `Between` has a checker leaf with no instance behind it. Nothing else disagrees. -/
def expected : List String := ["  leaf but no instance : Between[] as Checker"]

#eval show Elab.Command.CommandElabM Unit from do
  let cs ← Elab.Command.liftTermElabM (leaves.correspondence specs)
  let got := cs.map Correspondence.render
  if got == expected then
    IO.println s!"[correspond] BST leaves match the expected report ({got.length} known disagreement)"
  else
    throwError "correspondence report changed.\nexpected:\n{"\n".intercalate expected}\n\
      got:\n{"\n".intercalate got}"

end SpecimenTest.Correspondence
