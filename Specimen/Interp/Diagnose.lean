import Specimen.Interp.Blame

/-!
# Diagnosing a constructor that rarely succeeds

The procedure that found why Cedar's `binaryAppContains` almost never succeeds, as a tool. Searching over
reorderings and keeping whatever raised total coverage found nothing there; asking *why* one constructor
fails found two causes in an hour, and the fixes follow from the causes.

1. **Measure the constructor in isolation.** `ctorRates` runs it directly — at the root, on inputs its
   dispatch guard accepts, with the full environment for its sub-calls — so what is measured is its
   success *given that it was picked*, independent of its weight, and every failure names its step.
2. **Localize.** The failing step is the one most failures stop at.
3. **Ask what the failing step read.** A premise that bound something the failing step reads, while
   reading nothing itself, chose it **blind** (`blindProducers`): `contains`' `LubCompat t₂ elemTy`
   invents an element type before any expression exists to have one. The candidate fixes are the anchor
   moves that put one of the blind premise's anchors *ahead* of it, so that it gets an input (`orderCandidates`)
   — for `contains`, `[1,0,2]` and `[2,0,1]`. No other orders are tried.
4. **Ask whether the failing step had enough size.** Floors of 1–3 for the failing premise
   (`InterpEnv.premiseFloor`): the set operand needs size 2, which an even split denies it below size 5.
5. **Combine** the best order and the best floor — on `contains` neither helped alone — and **accept** only
   if the combination beats the baseline on *both* seed sets. Total coverage is the caller's guard; it is
   too noisy to judge one constructor by.

Sizing that applies everywhere (the remainder split) is not diagnosed here: it is set on the environment
the caller passes, for the baseline and every candidate alike.
-/

open Lean Schedules

namespace Specimen.Interp

/-- One size's worth of isolated runs. -/
structure CtorRate where
  size : Nat
  tried : Nat := 0
  ok : Nat := 0
  deriving Repr, Inhabited

/-- Isolated runs of one constructor: rates per size, and how many failures stopped at each step. -/
structure CtorRun where
  rates : List CtorRate := []
  failedAt : List (Nat × Nat) := []
  /-- Runs that ended in interpreter misconfiguration. Counted apart from failures: a candidate with any
      is broken, not bad — and measuring it as bad is how a missing checker once hid the right fix. -/
  internal : Nat := 0
  firstInternal : Option String := none
  deriving Repr, Inhabited

def CtorRun.ok (r : CtorRun) : Nat := r.rates.foldl (· + ·.ok) 0
def CtorRun.tried (r : CtorRun) : Nat := r.rates.foldl (· + ·.tried) 0

def CtorRun.render (r : CtorRun) : String :=
  s!"{r.ok}/{r.tried} [" ++ " ".intercalate (r.rates.map (fun c => s!"s{c.size}:{c.ok}/{c.tried}")) ++ "]" ++
    (if r.internal == 0 then "" else s!" · {r.internal} internal error(s): {(r.firstInternal.getD "").take 120}")

/-- Runs constructor `ctor` of mode `key` directly, `n` times per size and per input vector its guard
    accepts, and tallies successes and the step each failure stopped at. `size` is the budget the
    constructor would be entered with, as `interpRelSchedule` passes it: `size - 1` to its schedule. -/
def InterpEnv.ctorRates (env : InterpEnv) (key : SpecKey) (ctor : Name) (inputsList : List (List Val))
    (sizes : List Nat) (n : Nat) (seed : Nat) : IO CtorRun := do
  let some rel := env.relations[key]? | return {}
  let some sched := rel.ctorSchedule? ctor | return {}
  let usable := inputsList.filter (RelSchedule.guardPassesWith rel.inputNames sched.1)
  let mut rates : List CtorRate := []
  let mut failedAt : List (Nat × Nat) := []
  let mut internal := 0
  let mut firstInternal : Option String := none
  for s in sizes do
    let mut rate : CtorRate := { size := s }
    for ins in usable do
      let outs ← runSeeded (some (seed * 1000 + s))
        (attemptN n (runCtor env rel ctor (env.fuel - 1) s (s - 1) ins sched)) s
      for o in outs do
        rate := { rate with tried := rate.tried + 1 }
        match o with
        | .ok _ => rate := { rate with ok := rate.ok + 1 }
        | .error e =>
          if isInterpError e then
            internal := internal + 1
            if firstInternal.isNone then firstInternal := some (toString (repr e))
          else if let some i := rejectStepIdx? e then
            failedAt := match failedAt.find? (·.1 == i) with
              | some _ => failedAt.map (fun (j, k) => if j == i then (j, k + 1) else (j, k))
              | none => failedAt ++ [(i, 1)]
    rates := rates ++ [rate]
  return { rates, failedAt := failedAt.mergeSort (fun a b => b.2 ≤ a.2), internal, firstInternal }

/-- `ctorRates` on recorded entries (`withEntries`): each entry is run `n` times with the inputs and
    sizes it was actually entered with, and rates are grouped by that size. This is what makes a
    constructor that only ever runs as a sub-call testable at all. -/
def InterpEnv.ctorRatesAt (env : InterpEnv) (key : SpecKey) (ctor : Name) (entries : List CtorEntry)
    (n : Nat) (seed : Nat) : IO CtorRun := do
  let some rel := env.relations[key]? | return {}
  let some sched := rel.ctorSchedule? ctor | return {}
  let mut rates : List CtorRate := []
  let mut failedAt : List (Nat × Nat) := []
  let mut internal := 0
  let mut firstInternal : Option String := none
  for ((ins, initSize, size'), idx) in entries.zipIdx do
    let outs ← runSeeded (some (seed * 1000 + idx))
      (attemptN n (runCtor env rel ctor (env.fuel - 1) initSize size' ins sched)) initSize
    let mut rate : CtorRate := (rates.find? (·.size == size' + 1)).getD { size := size' + 1 }
    for o in outs do
      rate := { rate with tried := rate.tried + 1 }
      match o with
      | .ok _ => rate := { rate with ok := rate.ok + 1 }
      | .error e =>
        if isInterpError e then
          internal := internal + 1
          if firstInternal.isNone then firstInternal := some (toString (repr e))
        else if let some i := rejectStepIdx? e then
          failedAt := match failedAt.find? (·.1 == i) with
            | some _ => failedAt.map (fun (j, k) => if j == i then (j, k + 1) else (j, k))
            | none => failedAt ++ [(i, 1)]
    rates := if rates.any (·.size == rate.size) then rates.map (fun r => if r.size == rate.size then rate else r)
      else rates ++ [rate]
  return { rates := rates.mergeSort (fun a b => a.size ≤ b.size), failedAt := failedAt.mergeSort (fun a b => b.2 ≤ a.2),
           internal, firstInternal }

/-- The premises that bound a variable step `i` reads **uninformed**: while reading none of the other
    values step `i` checks it against, so nothing it knew could steer it towards what step `i` accepts.
    `(variable, premise)` pairs.

    "Read nothing" was the first criterion, and it found `binaryAppContains` (`LubCompat` invents an
    element type from scratch) but missed `hasAttrActionFf`, whose `MapNotContainsKey ety ets` produces
    `ety` as any key absent from the entity schema — it reads `ets`, but the failing
    `MapContainsPairKey ety … acts` needs `ety` to be an *action* type, which only `acts` knows. -/
def blindProducers (inputs : List Name) (steps : List ScheduleStep) (origins : List (Option PlanStep))
    (i : Nat) : List (Name × Nat) :=
  let fs := Dataflow.flows inputs steps
  let reads := ((fs[i]?).map (·.reads)).getD []
  reads.filterMap (fun v =>
    match Dataflow.binderOf inputs fs v i with
    | some (.step j) =>
      match (origins[j]?).bind id, fs[j]? with
      | some (.use p), some f =>
        let others := reads.filter (· != v)
        if f.reads.all (fun r => !others.contains r) then some (v, p) else none
      | _, _ => none
    | _ => none)

/-- Every premise that bound a variable step `i` reads (inputs and the prologue excluded).

    These, not only the uninformed ones, are where an order fix can come from. Reading the right inputs
    does not make a producer constrained by them: Cedar's `NotActionDescendentOf` reads `acts` and still
    accepts nearly any pair of UIDs, and `DescendentOf[2,3]` reads `ets` and `acts` yet yields an `ety₁`
    that `ValidEntityType` then rejects every time. `blindProducers` is the label; the measurement decides. -/
def readProducers (inputs : List Name) (steps : List ScheduleStep) (origins : List (Option PlanStep))
    (i : Nat) : List (Name × Nat) :=
  let fs := Dataflow.flows inputs steps
  (((fs[i]?).map (·.reads)).getD []).filterMap (fun v =>
    match Dataflow.binderOf inputs fs v i with
    | some (.step j) => match (origins[j]?).bind id with
      | some (.use p) => some (v, p)
      | _ => none
    | _ => none)

/-- Whether everything step `i` reads is fixed by the inputs (directly, or destructured from them by the
    prologue) — whatever the step's kind, a producer as much as a check. -/
def readsOnlyInputs (inputs : List Name) (steps : List ScheduleStep) (i : Nat) : Bool :=
  let det := Dataflow.inputDetermined inputs steps i
  ((Dataflow.flows inputs steps)[i]?).any (fun f => f.reads.all det.contains)

/-- The anchor moves that put an anchor of premise `p` ahead of it, repaired and deduplicated, without
    the installed schedule — and only those `derive_mutual` could be pinned to: a plan whose `inst`s are
    not all forced (`PlanBook.unpinnableInsts`) measures a generator no build can ship. -/
def orderCandidates (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (installed : Plan) (p : Nat) :
    List Plan :=
  let bare : Plan := installed.filter (fun st => match st with | .use _ => true | .inst _ => false)
  let installedSteps := (repair rel key c installed).toOption.map (·.2.1)
  let moves := (c.anchorsOf p).flatMap (fun q => (Plan.anchorMoves c bare q).filter (fun pl =>
    match pl.useIndex? q, pl.useIndex? p with
    | some iq, some ip => iq < ip
    | _, _ => false))
  (moves.foldl (fun (acc : List (Plan × List ScheduleStep)) pl =>
    match repair rel key c pl with
    | .ok (pl', sched) =>
      if installedSteps == some sched.1 || acc.any (·.2 == sched.1)
          || (PlanBook.unpinnableInsts rel key c pl').isSome then acc
      else acc ++ [(pl', sched.1)]
    | .error _ => acc) []).map (·.1)

/-- What `diagnose` found for one constructor. Runs are on two seed sets, `(A, B)`. -/
structure Diagnosis where
  key : SpecKey
  ctor : Name
  baseline : CtorRun × CtorRun
  failingPremise : Option Nat := none
  blind : List (Name × Nat) := []
  order : Option (Plan × CtorRun × CtorRun) := none
  floor : Option (Nat × CtorRun × CtorRun) := none
  combined : Option (CtorRun × CtorRun) := none
  accepted : Bool := false
  note : String := ""
  deriving Inhabited

/-- Beats `b` on both seed sets. -/
private def beatsBoth (a b : CtorRun × CtorRun) : Bool := a.1.ok > b.1.ok && a.2.ok > b.2.ok

private def total (a : CtorRun × CtorRun) : Nat := a.1.ok + a.2.ok

def Diagnosis.render (d : Diagnosis) : String :=
  let pair := fun (a : CtorRun × CtorRun) => s!"A {a.1.render} · B {a.2.render}"
  let lines :=
    [s!"{if d.accepted then "✔" else " "} {renderSpecKey d.key} · {d.ctor}",
     s!"    baseline  {pair d.baseline}",
     s!"    fails at  {match d.failingPremise with | some p => s!"premise {p}" | none => "—"}" ++
       (if d.blind.isEmpty then "" else
        " · reads blind: " ++ ", ".intercalate (d.blind.map (fun (v, p) => s!"{v} (chosen by premise {p})")))] ++
    (match d.order with | some (pl, a, b) => [s!"    order {renderPlan pl}  {pair (a, b)}"] | none => []) ++
    (match d.floor with | some (f, a, b) => [s!"    floor ≥{f}  {pair (a, b)}"] | none => []) ++
    (match d.combined with | some ab => [s!"    combined  {pair ab}"] | none => []) ++
    (if d.note.isEmpty then [] else [s!"    {d.note}"])
  "\n".intercalate lines

/-- Diagnoses constructor `ctor` of mode `key` and tries the fixes its diagnosis names.

    `envFor book` builds the environment to measure a book in (the caller's sizing, weights and leaves
    applied); `start` is the installed book. Floors are layered onto whatever `premiseFloor` the
    environment already has. -/
def diagnose (specs : List RelSpec) (envFor : PlanBook → IO (Option InterpEnv)) (start : PlanBook)
    (key : SpecKey) (ctor : Name) (inputsList : List (List Val)) (sizes : List Nat := [3, 4, 5, 6, 8])
    (n : Nat := 30) (seedA : Nat := 101) (seedB : Nat := 201) (entries : List CtorEntry := []) :
    IO Diagnosis := do
  let some env ← envFor start | return { key, ctor, baseline := ({}, {}), note := "the start book does not build" }
  -- Recorded entries when there are any — the inputs and sizes the constructor really gets; otherwise
  -- `inputsList` at `sizes`.
  let runs := fun (e : InterpEnv) => do
    if entries.isEmpty then
      return (← e.ctorRates key ctor inputsList sizes n seedA, ← e.ctorRates key ctor inputsList sizes n seedB)
    else
      let k := max 1 (n / 4)
      return (← e.ctorRatesAt key ctor entries k seedA, ← e.ctorRatesAt key ctor entries k seedB)
  let base ← runs env
  let mut d : Diagnosis := { key, ctor, baseline := base }
  -- A misconfigured environment says nothing about the constructor: diagnosing it anyway produced
  -- "impossible" verdicts for Strata's `eq` and `quant` whose real cause was a missing `PUnit` leaf.
  if base.1.internal + base.2.internal > 0 then
    return { d with note := s!"not diagnosed: the baseline hits {base.1.internal + base.2.internal} \
      interpreter error(s) — {((base.1.firstInternal.orElse (fun _ => base.2.firstInternal)).getD "").take 160}" }
  let some rel := specs.find? (·.inductiveName == key.inductiveName) | return { d with note := "no spec" }
  let some c := rel.ctors.find? (·.ctorName == ctor) | return { d with note := "no such constructor" }
  let some rs := env.relations[key]? | return { d with note := "mode not in the closure" }
  let some prov := rs.provenanceOf? ctor | return { d with note := "no provenance" }
  let some (steps, _) := rs.ctorSchedule? ctor | return { d with note := "no schedule" }
  let failures := base.1.failedAt ++ base.2.failedAt
  let some (stepIdx, _) := failures.head? | return { d with note := "no failures to diagnose" }
  let failingPremise := match (prov.origins[stepIdx]?).bind id with | some (.use p) => some p | _ => none
  let blind := blindProducers rs.inputNames steps prov.origins stepIdx
  let producers := readProducers rs.inputNames steps prov.origins stepIdx
  d := { d with failingPremise, blind }
  -- Nothing the constructor chose reaches the failing step, and it never succeeds: its inputs decide it.
  if producers.isEmpty && base.1.ok + base.2.ok == 0 && readsOnlyInputs rs.inputNames steps stepIdx then
    return { d with note := "impossible on these inputs: the failing step reads only what the inputs \
      determine, and no recorded entry succeeds — the cause is the caller, or the environment" }
  -- Information: the anchor moves that give a blind premise an input.
  let mut bestOrder : Option (Plan × CtorRun × CtorRun) := none
  let mut broken : List String := []
  for p in (producers.map (·.2)).eraseDups do
    for pl in orderCandidates rel key c prov.plan p do
      let some e ← envFor (start.set key ctor pl) | continue
      let r ← runs e
      if r.1.internal + r.2.internal > 0 then
        broken := broken ++ [s!"order {renderPlan pl}: {r.1.internal + r.2.internal} internal error(s), \
          {(r.1.firstInternal.orElse (fun _ => r.2.firstInternal)).getD ""}"]
        continue
      if bestOrder.all (fun (_, a, b) => total r > total (a, b)) then bestOrder := some (pl, r.1, r.2)
  d := { d with order := bestOrder, note := "; ".intercalate broken }
  -- Budget: a floor for the failing premise, on the start's order.
  let withFloor := fun (e : InterpEnv) (f : Nat) =>
    match failingPremise with
    | none => e
    | some p =>
      let prior := (e.premiseFloor[ctor]?).getD []
      { e with premiseFloor := e.premiseFloor.insert ctor ((prior.filter (·.1 != p)) ++ [(p, f)]) }
  let mut bestFloor : Option (Nat × CtorRun × CtorRun) := none
  if failingPremise.isSome then
    for f in [1, 2, 3] do
      let r ← runs (withFloor env f)
      if bestFloor.all (fun (_, a, b) => total r > total (a, b)) then bestFloor := some (f, r.1, r.2)
  d := { d with floor := bestFloor }
  -- Combine whatever helped, and accept on both seed sets.
  let orderHelps := bestOrder.any (fun (_, a, b) => total (a, b) > total base)
  let floorHelps := bestFloor.any (fun (_, a, b) => total (a, b) > total base)
  let book := match bestOrder, orderHelps with
    | some (pl, _, _), true => start.set key ctor pl
    | _, _ => start
  if orderHelps || floorHelps then
    let some e ← envFor book | return { d with note := "the combined book does not build" }
    let e := match bestFloor, floorHelps with
      | some (f, _, _), true => withFloor e f
      | _, _ => e
    let r ← runs e
    d := { d with combined := some r, accepted := beatsBoth r base }
  return d

end Specimen.Interp
