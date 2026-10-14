import Specimen.Interp.DataflowCore
import Specimen.Interp.Preschedule
/-!
# Dataflow through an installed schedule

Blame follows a chain. A step rejects on values it **reads**, and each of those was bound by exactly one
earlier step — or came in as an input. So when a step keeps rejecting, the candidates for the cause are
the step itself, then the premises that *produced* what it read, then theirs, and — once the chain reaches
the constructor's inputs — the caller that chose those inputs. This module computes that structure over
an installed schedule; it is pure, and decides nothing about what to try.

**The walk is over the bound set, not per step kind.** Any name a step mentions that is already bound is
a read; any other is a binding. The per-kind rules one would write first are wrong in two places: a
delegated `SuchThat` binds variables that are not among its listed outputs, and a `MutRec` call's
arguments are already filtered to its inputs. The bound-set rule gets both right without knowing either.

Steps are mapped back to premises through the provenance recorded at lowering (`CtorProvenance`), never
by re-lowering. A step with no origin belongs to the conclusion prologue: what it binds is
**input-determined**, since the prologue only destructures inputs.
-/

open Lean Schedules

namespace Specimen.Interp.Dataflow

/-- The steps a premise emitted, by the recorded provenance. -/
def stepsOfPremise (origins : List (Option PlanStep)) (i : Nat) : List Nat :=
  origins.zipIdx.filterMap (fun (o, j) => if o == some (.use i) then some j else none)

/-- The premises that produced what the steps `idxs` read, and whether any of those reads came from the
    inputs (directly, or through the conclusion prologue).

    A variable bound by an `inst` step maps to every premise that mentions it: generating it blind is what
    those premises did not do, so moving any of them could make one produce it instead. -/
def producersOf (inputs : List Name) (steps : List ScheduleStep) (origins : List (Option PlanStep))
    (c : CtorSpec) (idxs : List Nat) : List Nat × Bool := Id.run do
  let fs := flows inputs steps
  let mut prems : List Nat := []
  let mut readsInputs := false
  for i in idxs do
    for v in ((fs[i]?).map (·.reads)).getD [] do
      match binderOf inputs fs v i with
      | some .input => readsInputs := true
      | some (.step j) =>
        match (origins[j]?).bind id with
        | some (.use p) => prems := prems ++ [p]
        | some (.inst w) =>
          prems := prems ++ (c.hypotheses.zipIdx.filterMap (fun (h, p) =>
            if h.2.any (fun a => (varsInConstructorExpr a).contains w) then some p else none))
        | none => readsInputs := true
      | none => pure ()
  return (prems.eraseDups, readsInputs)

/-- The chain behind a blamed premise, breadth-first: level 0 is the premise itself, level `k + 1` the
    premises that produced what level `k` read and that no earlier level contains. Dataflow runs forward,
    so the chain cannot cycle; `maxLevels` is a backstop. `readsInputs` records whether any level read the
    mode's inputs, which is what licenses looking at the caller once the local levels are exhausted. -/
structure Chain where
  levels : List (List Nat)
  readsInputs : Bool
  deriving Repr, Inhabited

def chainOf (inputs : List Name) (steps : List ScheduleStep) (origins : List (Option PlanStep))
    (c : CtorSpec) (premise : Nat) (maxLevels : Nat := 8) : Chain := Id.run do
  let mut levels : List (List Nat) := [[premise]]
  let mut seen : List Nat := [premise]
  let mut readsInputs := false
  let mut frontier := [premise]
  for _ in List.range maxLevels do
    let idxs := frontier.flatMap (stepsOfPremise origins)
    let (prems, ri) := producersOf inputs steps origins c idxs
    readsInputs := readsInputs || ri
    let next := prems.filter (!seen.contains ·)
    if next.isEmpty then break
    levels := levels ++ [next]
    seen := seen ++ next
    frontier := next
  return { levels, readsInputs }

end Specimen.Interp.Dataflow
