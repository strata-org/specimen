import SpecimenTest.Interp.BSTInterpTest

/-!
# Provenance describes the schedule that is installed

Blame attribution maps a rejecting step back to the premise that emitted it, so a mutation has something
to move. It used to rebuild that map by re-lowering `PlanBook.planFor`, which is a *different* plan from
the installed one whenever lowering repaired a booked order, chose the first resolvable plan, or worked
from an instantiated spec. The map is now recorded when the schedule is lowered (`CtorProvenance`); these
tests pin that it describes what actually runs.
-/

open Lean Schedules Specimen Specimen.Interp SpecimenTest.InterpBST

namespace SpecimenTest.InterpProvenance

/-- Every derived constructor schedule has provenance, one origin per step, and its recorded plan lowers
    again to a schedule of the same length (the installed one may additionally have been linked, which
    rewrites steps one for one). -/
def consistent (env : InterpEnv) : Bool :=
  env.relations.toList.all (fun ((key, rs) : SpecKey × RelSchedule) =>
    rs.allSchedules.all (fun (ctor, sched) =>
      match rs.provenanceOf? ctor, specs.find? (·.inductiveName == key.inductiveName) with
      | some p, some rel =>
        match rel.ctors.find? (·.ctorName == ctor) with
        | some c =>
          p.origins.length == sched.1.length &&
          (match rescheduleLowered rel key c p.plan with
           | .ok low => low.schedule.1.length == sched.1.length
           | .error _ => false)
        | none => false
      | _, _ => false))

-- The default closure: every constructor of every mode carries consistent provenance.
/-- info: true -/
#guard_msgs in
#eval match leaves.deriveClosureWith specs [bstKey] ({} : PlanBook) with
  | .error _ => false
  | .ok env => consistent env

/-- `BstNode` booked as `[1, 0, 2]`: `BST lo x l` first, so it produces `x` and `l` — a call to `BST[1,2]`,
    a mode this order alone mints, which `linkMutualCalls` rewrites into a `MutRec`. -/
def reordered : PlanBook := ({} : PlanBook).set bstKey ``BST.BstNode ([1, 0, 2].map PlanStep.use)

-- The rewrite keeps the recorded origins aligned: the step that calls `BST[1,2]` is still attributed to
-- premise 1, and the whole closure stays consistent.
/-- info: (true, true, true) -/
#guard_msgs in
#eval match leaves.deriveClosureWith specs [bstKey] reordered with
  | .error _ => (false, false, false)
  | .ok env =>
    match env.relations[bstKey]? with
    | none => (false, false, false)
    | some rs =>
      match rs.ctorSchedule? ``BST.BstNode, rs.provenanceOf? ``BST.BstNode with
      | some sched, some p =>
        let mutIdx := sched.1.findIdx? (fun (st : ScheduleStep) => match st with
          | .SuchThat _ (.MutRec ..) _ => true | _ => false)
        (mutIdx.isSome,
         mutIdx.any (fun i => (p.origins[i]?).bind id == some (PlanStep.use 1)),
         consistent env)
      | _, _ => (false, false, false)

-- Replacing a constructor's schedule by hand drops its provenance: the replacement did not come from
-- that plan, and keeping the old map would attribute its steps to the wrong premises.
/-- info: (true, false) -/
#guard_msgs in
#eval match leaves.deriveClosureWith specs [bstKey] ({} : PlanBook) with
  | .error _ => (false, true)
  | .ok env =>
    match env.relations[bstKey]? with
    | none => (false, true)
    | some rs =>
      let before := (rs.provenanceOf? ``BST.BstNode).isSome
      let after := ((rs.withCtorSchedule ``BST.BstNode expectedBstNode).provenanceOf? ``BST.BstNode).isSome
      (before, after)

end SpecimenTest.InterpProvenance
