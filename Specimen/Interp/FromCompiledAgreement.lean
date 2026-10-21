import Specimen.Interp.FromCompiled
import Specimen.Interp.ScheduleEquiv

/-!
# Is the compiled start faithful?

`Interp.FromCompiled` seeds learning from the deriver's settled premise orders. This module checks the
claim that makes that meaningful — that the closure the interpreter then *samples* runs the schedules the
deriver emitted — using `Interp.ScheduleEquiv`, which is sound: it may call two equivalent schedules
different, never two different ones the same. Anything it cannot model is reported as `outside`, and
only `agree` counts as agreement.

Kept separate from `FromCompiled` so the comparator, which reads type shapes from the environment, is not
a dependency of seeding itself.
-/

open Lean Schedules Specimen Specimen.Interp

namespace Specimen.Interp

/-! ## Is the start faithful? The closure that is sampled, against what the deriver emitted -/

/-- Every constructor and relation shape the round trip can need. That is what the specs mention, which
    covers everything an interpreted schedule can mention since the interpreter lowers from the specs,
    plus what the deriver's schedules mention. -/
def DeriverChoice.shapes (c : DeriverChoice) (specs : List RelSpec) : Meta.MetaM ScheduleEquiv.Shapes := do
  let (cs, rs) := ScheduleEquiv.specMentions specs
  let mut ctors := cs
  let mut rels := rs
  for (_, e) in c.memo.toList do
    match e with
    | .done ind =>
      for (_, s) in ind.baseSchedules ++ ind.recSchedules do
        let (cs', rs') := ScheduleEquiv.scheduleMentions s
        ctors := ctors ++ cs'
        rels := rels ++ rs'
    | _ => pure ()
  ScheduleEquiv.Shapes.build ctors rels

/-- What comparing a closure with the deriver's schedules found. Only `agree` counts as agreement. A
    constructor that differs, falls outside the comparator, or has nothing to compare with is listed,
    never folded into the count. That separation is what the first round trip lacked: its "1756 of 1870"
    and "820 of 861" both came from a comparator that could not tell a swapped input or a dropped
    dictionary from agreement (`Specimen.Interp.ScheduleEquiv`). -/
structure Agreement where
  agree : Nat := 0
  /-- `(mode · constructor, kind of the first difference, the difference)`. -/
  differ : List (String × String × String) := []
  /-- `(mode · constructor, why the comparator cannot certify it)`. -/
  outside : List (String × String) := []
  /-- Generator constructors in the closure with no compiled schedule: a mode the deriver found an
      instance for (`alreadyExists`), or never derived. -/
  uncompared : List String := []

def Agreement.compared (a : Agreement) : Nat := a.agree + a.differ.length + a.outside.length

def Agreement.render (a : Agreement) : String :=
  let kinds := a.differ.foldl (fun acc (_, k, _) =>
    match acc.find? (·.1 == k) with
    | some _ => acc.map (fun p => if p.1 == k then (k, p.2 + 1) else p)
    | none => acc ++ [(k, 1)]) ([] : List (String × Nat))
  let head := s!"[round-trip] {a.agree} of {a.compared} compared generator constructor(s) agree · \
    {a.differ.length} differ · {a.outside.length} outside the comparator · {a.uncompared.length} with \
    no compiled schedule"
  let kindLines := kinds.map (fun (k, n) =>
    let ex := (a.differ.find? (·.2.1 == k)).map (fun (l, _, d) => s!"\n      e.g. {l}: {d.take 400}")
    s!"  {n}× {k}{ex.getD ""}")
  let outLines := (a.outside.take 4).map (fun (l, w) => s!"  outside: {l}: {w.take 300}")
  "\n".intercalate (head :: kindLines ++ outLines)

/-- Compares every generator constructor of `env` with the schedule the deriver emitted for it, using
    `ScheduleEquiv.compareSchedules`. `env` is a closure built from this choice's book, and `leaves` is the
    environment it was built on.

    This compares the closure that is actually *sampled*, not the recorded orders lowered one by one,
    because a start is faithful only if what runs matches. Four things are handled here rather than in the
    comparator:

    * **Instantiated modes.** A closure key carries its instantiation (`MapContains[3]@(0:Attr, …)`),
      and the memo's keys do not. So the deriver's schedule is looked up without `typeArgs`, and it is read
      with the closure's instantiation for that key, recovered from the call sites that asked for it
      (`depKeysTyped`), in place of its type parameters. Without that, every instantiated mode falls into
      "never derived" and out of the count.
    * **Mutual linking.** The memo holds schedules from before `linkMutualCalls`, and the closure's
      schedules are linked. So the compiled side is first linked against the closure's own sibling table,
      and the `MutRec` names then agree.
    * **Leaves.** A callee answered by a `leaves` producer or checker reads its arguments from the end
      (`Bridge`'s convention), so a leading dictionary is harmless there. A callee the closure interprets
      is read strictly, since there `bindInputs` needs the exact arity.
    * **Dispatch.** The comparator certifies `dispatchInputs := false`. With dispatch on, the order of a
      schedule's leading input matches changes the weights, and that is not compared. -/
def DeriverChoice.agreement (c : DeriverChoice) (shapes : ScheduleEquiv.Shapes) (leaves env : InterpEnv)
    (specs : List RelSpec) : Agreement := Id.run do
  let groups := mutualGroups specs
  let modes := env.relations.toList
  let allModes : List (Name × List Nat × Name × DeriveSort) :=
    modes.map (fun (k, r) => (k.inductiveName, k.outputIndices, r.recFnName, k.deriveSort))
  let siblingsOf := fun (key : SpecKey) =>
    let family := (groups.find? (fun g => g.contains key.inductiveName)).getD [key.inductiveName]
    allModes.filter (fun (n, idxs, _, srt) =>
      family.contains n
        && !(n == key.inductiveName && idxs == key.outputIndices && srt == key.deriveSort))
  let insts := modes.flatMap (fun (_, r) => r.depKeysTyped (includeChecks := true))
  let interpreted := fun (n : Name) (outs : List Nat) =>
    modes.any (fun (k, _) =>
      k.inductiveName == n && k.outputIndices == outs && k.deriveSort == .Generator)
  let trailing : List (Name × List Nat) :=
    (leaves.producers.toList.filterMap (fun (k, _) =>
      if interpreted k.inductiveName k.outputIndices then none
      else some (k.inductiveName, k.outputIndices)))
    ++ leaves.checkers.toList.map (fun (n, _) => (n, []))
  let mut out : Agreement := {}
  -- With `dispatchInputs` the order of a schedule's leading input matches decides which branches are
  -- filtered, and so the counts the weight function sees. The comparator does not model that, so it
  -- certifies nothing here rather than something wrong.
  if env.dispatchInputs then
    for (key, rel) in modes do
      if key.deriveSort != .Generator then continue
      for (ctor, _) in rel.allSchedules do
        out := { out with outside := out.outside ++
          [(s!"{renderSpecKey key} · {ctor}", "dispatchInputs is on; only dispatch off is certified")] }
    return out
  for (key, rel) in modes do
    if key.deriveSort != .Generator then continue
    let ind? : Option InductiveSchedule :=
      match (c.memo[({ key with typeArgs := [] } : SpecKey)]? : Option MemoEntry) with
      | some (MemoEntry.done ind) => if ind.alreadyExists then none else some ind
      | _ => none
    let sibs := siblingsOf key
    -- The interpreter drops argument positions by what the closure *recorded* for the relation; the
    -- comparator reads the compiled side by the relation's declared shape. If they disagree, the
    -- interpreter reading is not of the program `Gen` runs, so nothing in this mode is certified.
    let declared := (shapes.rels[key.inductiveName]?).map (·.typePositions)
    let positionsAgree := match declared with
      | some ps => rel.typeArgIndices.isEmpty || ps.all rel.typeArgIndices.contains
                     && rel.typeArgIndices.all ps.contains
      | none => false
    -- A constructor the deriver scheduled that the closure lacks is a real difference in *what the
    -- generator can produce*, not a detail of one schedule, so it is reported, never skipped.
    if let some ind := ind? then
      let interpCtors := rel.allSchedules.map (·.1)
      for (ctor, _) in ind.baseSchedules ++ ind.recSchedules do
        unless interpCtors.contains ctor do
          out := { out with differ := out.differ ++
            [(s!"{renderSpecKey key} · {ctor}", "missing constructor",
              "the deriver scheduled it; the closure has no schedule for it")] }
    for (ctor, sched) in rel.allSchedules do
      let label := s!"{renderSpecKey key} · {ctor}"
      unless positionsAgree do
        out := { out with outside := out.outside ++ [(label, s!"closure records type/instance positions \
          {rel.typeArgIndices} but the relation declares {declared}")] }
        continue
      let some ind := ind? | out := { out with uncompared := out.uncompared ++ [label] }; continue
      -- Base versus recursive bucket decides `numBase`/`numRec`, which the weight function reads.
      let inRec := fun (xs : List (Name × Schedule)) => xs.any (·.1 == ctor)
      if inRec rel.recSchedules != inRec ind.recSchedules then
        out := { out with differ := out.differ ++ [(label, "bucket",
          s!"recursive in {if inRec rel.recSchedules then "the closure" else "the deriver"} only")] }
        continue
      let scheds := ind.baseSchedules ++ ind.recSchedules
      let some (_, comp) := scheds.find? (·.1 == ctor) | out := { out with uncompared := out.uncompared ++ [label] }; continue
      let interpSide : ScheduleEquiv.Side :=
        { reading := .interp, rel := key.inductiveName, argNames := rel.argNames,
          outputIndices := key.outputIndices, selfFn := rel.recFnName, trailingLeaves := trailing,
          typeIdxOf := env.typeArgIndicesOf }
      let compiledSide : ScheduleEquiv.Side :=
        { reading := .compiled, rel := key.inductiveName, argNames := ind.argNames,
          outputIndices := key.outputIndices, selfFn := ind.recFnName,
          siblings := sibs.map (fun (n, idxs, f, _) => (f, n, idxs)),
          inst := ((insts.find? (·.1 == key)).map (·.2)).getD [] }
      match ScheduleEquiv.compareSchedules shapes interpSide compiledSide sched
          (rewriteMutualCalls comp.1 sibs, comp.2) with
      | .same => out := { out with agree := out.agree + 1 }
      | .differ k d => out := { out with differ := out.differ ++ [(label, k, d)] }
      | .outside w => out := { out with outside := out.outside ++ [(label, w)] }
  return out

end Specimen.Interp
