import Specimen.Interp.Env

/-!
# Dataflow through a schedule — the part the runtime needs

The pure core of `Interp.Dataflow`: which names each step reads and binds, who bound a name, and whether
a step's rejection was decided by the mode's inputs alone. Split out so `Interp.Gen` can use it to tell
"no constructor could apply to these inputs" from "a constructor tried and failed" without depending on
lowering. See `Interp.Dataflow` for the design.
-/

open Lean Schedules

namespace Specimen.Interp.Dataflow

/-- Every variable a source mentions. -/
def sourceVars : Source → List Name
  | .NonRec (_, args) | .Rec _ args | .MutRec _ args => args.flatMap varsInConstructorExpr

/-- Every name a step mentions, reads and bindings alike. -/
def mentions : ScheduleStep → List Name
  | .Match _ v p => v :: varsInConstructorExpr (constructorExprOfPattern p)
  | .Check src _ => sourceVars src
  | .SuchThat outs src _ => outs.map (·.1) ++ sourceVars src
  | .Unconstrained v src _ =>
    v :: (match src with | .Rec _ args | .MutRec _ args => args.flatMap varsInConstructorExpr | _ => [])

/-- What one step reads and binds. -/
structure StepFlow where
  reads : List Name
  binds : List Name
  deriving Repr, Inhabited, BEq

/-- The bound-set walk: a mentioned name that is already bound is read; any other is bound by this step.
    `inputs` are bound before the first step. `Match` is the one exception to "mentioned and bound means
    read" being enough: its scrutinee is always a read, and its pattern variables always binds, even if
    one shadows an earlier name, because that is what the step does at run time. -/
def flows (inputs : List Name) (steps : List ScheduleStep) : List StepFlow := Id.run do
  let mut bound := inputs
  let mut out : List StepFlow := []
  for st in steps do
    let flow : StepFlow := match st with
      | .Match _ v p =>
        { reads := [v], binds := (varsInConstructorExpr (constructorExprOfPattern p)).eraseDups }
      | _ =>
        let ms := (mentions st).eraseDups
        { reads := ms.filter bound.contains, binds := ms.filter (!bound.contains ·) }
    bound := bound ++ flow.binds
    out := out ++ [flow]
  return out

/-- Who bound a variable as seen from a given step. -/
inductive Binder where
  /-- An input of the mode. -/
  | input
  /-- Step `idx` of the schedule. -/
  | step (idx : Nat)
  deriving Repr, BEq, Inhabited

/-- The latest binder of `v` strictly before step `before`: the most recent step that bound it, else an
    input, else nothing. -/
def binderOf (inputs : List Name) (fs : List StepFlow) (v : Name) (before : Nat) : Option Binder :=
  let prior := (fs.take before).zipIdx.filter (fun (f, _) => f.binds.contains v)
  match prior.getLast? with
  | some (_, j) => some (.step j)
  | none => if inputs.contains v then some .input else none

/-- The names that are determined by the inputs alone before step `upTo`: the inputs, plus anything a
    `Match` on an already input-determined name binds. -/
def inputDetermined (inputs : List Name) (steps : List ScheduleStep) (upTo : Nat) : List Name := Id.run do
  let mut det := inputs
  for (st, i) in steps.zipIdx do
    if i ≥ upTo then break
    match st with
    | .Match _ v p =>
      if det.contains v then det := det ++ varsInConstructorExpr (constructorExprOfPattern p)
    | _ => pure ()
  return det

/-- Whether step `i` is a *passive* step — a `Match` or `Check` — all of whose reads are determined by the
    inputs. When such a step rejects, no reordering of this constructor's premises can help: the values it
    looked at were fixed by whoever called the mode. -/
def failsOnInputs (inputs : List Name) (steps : List ScheduleStep) (i : Nat) : Bool :=
  match steps[i]? with
  | some (.Match ..) | some (.Check ..) =>
    let det := inputDetermined inputs steps i
    ((flows inputs steps)[i]?).any (fun f => f.reads.all det.contains)
  | _ => false

/-- Whether step `i` is a call — a `SuchThat` or `Unconstrained` that consults another producer — all of
    whose reads are input-determined. A callee that then finds no constructor applicable was handed values
    this mode did not choose. -/
def callReadsOnlyInputs (inputs : List Name) (steps : List ScheduleStep) (i : Nat) : Bool :=
  match steps[i]? with
  | some (.SuchThat ..) | some (.Unconstrained ..) =>
    let det := inputDetermined inputs steps i
    ((flows inputs steps)[i]?).any (fun f => f.reads.all det.contains)
  | _ => false

end Specimen.Interp.Dataflow
