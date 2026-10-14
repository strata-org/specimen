import Specimen
import Specimen.Interp

/-!
# Do the interpreter's leaves and the compiled environment's instances agree?

An `InterpEnv` registers what its schedules bottom out at by hand — `withArbitrary`, `addChecker`,
`addProducer`. The compiled pipeline resolves the same things by typeclass synthesis. Nothing checked the
two against each other, and they drifted **in both directions**, each time with a cause that was hard to
read back from the symptom:

* `cedarLeaves` had no `ValidDatetime`/`ValidDuration` producer, while `TypeOfLean.lean` has had
  hand-written `ArbitrarySizedSuchThat` instances for both all along. Datetime and duration expressions
  were therefore unreachable *in the interpreter only*, silently biasing every Cedar measurement against
  four extension-function families. Forcing the rule showed the cost: absorbed failures 8028/9002 without
  the producers against 371/678 with them.
* `BSTInterpTest`'s `leaves` registers a checker for `Between`, which has no `DecOpt Between`
  counterpart. So the interpreter satisfies `Between[1,2]` from a leaf and brings up **3** modes, while
  the compiled path must build `Between` from its definition, brings up **12**, and fails three `LE.le`
  modes with "not inductive and has no Decidable instance". That failure then surfaced far downstream as
  `failed to synthesize ArbitrarySizedSuchThat Nat (fun m => a_3 ≤ m)` — naming neither `Between` nor the
  leaf responsible.

The consequence is worse than an inconvenience: a plan can be *measurable* in the interpreter and
*unemittable* by the pipeline, so a tuning result transfers silently wrongly. This module asks the
pipeline's own question — `instanceExistsFor`, extracted from `deriveBestInductiveSchedule` for exactly
this purpose — about each of an `InterpEnv`'s leaves, and about each mode the specs could want.

Kept out of `Specimen.Interp` on purpose: `Interp` does not depend on the compile-time deriver, and that
independence is worth keeping. This is a tool, imported by tests and probes.
-/

open Lean Schedules Specimen Specimen.Interp

namespace Specimen.Interp

/-- A disagreement between an `InterpEnv`'s leaves and what Lean can synthesise. -/
inductive Correspondence where
  /-- The interpreter has a leaf; the compiled environment cannot synthesise the instance. Plans relying
      on this leaf lower and measure here, and fail to emit there. -/
  | leafOnly (key : SpecKey)
  /-- Lean can synthesise the instance; the interpreter has no leaf. The interpreter will either derive
      the relation itself — fine, if slower — or report a missing leaf, and in the `ValidDatetime` case it
      quietly could not produce at all. -/
  | instanceOnly (key : SpecKey)
  deriving Repr

def Correspondence.render : Correspondence → String
  | .leafOnly k => s!"  leaf but no instance : {renderSpecKey k}"
  | .instanceOnly k => s!"  instance but no leaf: {renderSpecKey k}"

/-- The leaf registrations that would close the `instanceOnly` gaps, as Lean source for an
    `InterpEnv` builder.

    Only the checker case is mechanical, and it is also the bulk of the work: closing Cedar's
    twenty-one gaps took fifteen leaves, and thirteen of them were `addChecker … (checkerOfDecOptN …)`
    lines differing only in name and arity. Those are emitted ready to paste.

    Producers are emitted as `TODO` comments instead, because there is no mechanical shape: a producer
    has to delegate to the right `ArbitrarySizedSuchThat` instance at the right output positions, and for
    a polymorphic relation it cannot be keyed by name at all (see `mapNotContainsKeyCheck`, which had to
    be written at the `Val` level for exactly that reason). Naming the mode is the useful part.

    Arity above three is also a comment: `checkerOfDecOpt1/2/3` is where `Bridge` stops. -/
def Correspondence.toLeafSource (cs : List Correspondence) (specs : List RelSpec) : String :=
  let arityOf := fun (n : Name) =>
    match specs.find? (fun r => r.inductiveName == n) with
    | some rel => (rel.argNames.length) - rel.typeArgIndices.length
    | none => 0
  let line := fun (c : Correspondence) =>
    match c with
    | .leafOnly _ => none
    | .instanceOnly k =>
      let n := toString k.inductiveName
      if k.deriveSort == .Checker then
        let a := arityOf k.inductiveName
        let poly := (specs.find? (fun r => r.inductiveName == k.inductiveName)).any
          (fun r => !r.typeArgIndices.isEmpty)
        if a == 0 || a > 3 then
          some s!"  -- TODO checker for {n}: value arity {a}, and `checkerOfDecOpt` stops at 3"
        else if poly then
          -- `addChecker` keys on the relation *name*, so one leaf serves every instantiation; a
          -- `checkerOfDecOptN` fixes the element type and therefore cannot. `mapNotContainsKeyCheck`
          -- is the worked example.
          some s!"  -- TODO checker for {n}: polymorphic, so `checkerOfDecOpt{a}` would fix the element \
            type — write it at the `Val` level instead (cf. `mapNotContainsKeyCheck`)"
        else
          some s!"  let e := e.addChecker ``{n} (checkerOfDecOpt{a} {n})"
      else
        let outs := "[" ++ ", ".intercalate (k.outputIndices.map toString) ++ "]"
        some s!"  -- TODO producer for {n} at outputs {outs}: addProducer a key with \
          inductiveName := ``{n}, outputIndices := {outs}, deriveSort := .Generator"
  let lines := cs.filterMap line
  if lines.isEmpty then "-- no mechanically fillable gaps" else "\n".intercalate lines

/-- Every mode of every spec, at the sorts a generator closure can want.

    **Type-level positions are skipped, and that is not cosmetic.** `instanceExistsFor` reads `argTypes`
    off the raw inductive type, so for `MapContains {α β : Type} : α → β → Map α β → Prop` position 0 is
    `Type`. Asking about output index `[0]` then trips its early return —

      if nonSortOutputIndices.isEmpty && key.outputIndices.length > 0 then pure true

    — which answers "instance exists" without synthesising anything. Before this filter, the report
    claimed eight missing producers on Cedar (`MapContains[0]`, `SetContains[0]`, `MapNotContainsKey[0]`
    and so on) when CedarGen contains **no** `ArbitrarySizedSuchThat` instance for any of them. Every one
    was on a polymorphic relation — precisely the set where the interpreter's position basis and the raw
    type's diverge. -/
private def candidateKeys (specs : List RelSpec) : List SpecKey :=
  specs.flatMap (fun rel =>
    let arity := rel.argNames.length
    let valuePos := (List.range arity).filter (fun i => !rel.typeArgIndices.contains i)
    -- Single-output modes and the all-outputs mode: enough to catch a missing producer without
    -- enumerating the powerset, which on Cedar's arities would be thousands of synthesis calls.
    let singles := valuePos.map (fun i =>
      ({ inductiveName := rel.inductiveName, outputIndices := [i],
         deriveSort := .Generator } : SpecKey))
    let allOut : SpecKey := { inductiveName := rel.inductiveName, outputIndices := valuePos, deriveSort := .Generator }
    let chk : SpecKey := { inductiveName := rel.inductiveName, outputIndices := [], deriveSort := .Checker }
    -- Deduped: for a relation with one value position the single-output mode *is* the all-outputs mode,
    -- so without this every such relation is reported (and counted) twice — which is what the four
    -- `Valid*` extension relations did.
    List.eraseDups (singles ++ [allOut, chk]))

/-- Compares an `InterpEnv`'s leaves against what Lean can synthesise, both directions.

    `specs` bounds the search: only relations the interpreter might schedule are considered, at
    single-output modes plus the all-outputs mode plus the checker. That is deliberately not the full
    powerset of output positions — on Cedar's arities that would be thousands of `synthInstance?` calls
    for little extra signal. -/
def InterpEnv.correspondence (env : InterpEnv) (specs : List RelSpec) :
    Lean.Elab.TermElabM (List Correspondence) := do
  let mut out : List Correspondence := []
  for key in candidateKeys specs do
    let hasInstance ← try instanceExistsFor key catch _ => pure false
    let hasLeaf :=
      if key.deriveSort == .Checker then env.checkers.contains key.inductiveName
      else (env.producers.contains key) || (env.relations.contains key)
    if hasLeaf && !hasInstance then
      out := out ++ [.leafOnly key]
    else if hasInstance && !hasLeaf then
      out := out ++ [.instanceOnly key]
  return out

/-- A report, or a line saying the two agree. -/
def InterpEnv.correspondenceReport (env : InterpEnv) (specs : List RelSpec) : Lean.Elab.TermElabM String := do
  let cs ← env.correspondence specs
  if cs.isEmpty then
    return s!"[correspond] ok: leaves and instances agree across {specs.length} relation(s)"
  else
    return s!"[correspond] {cs.length} disagreement(s) across {specs.length} relation(s):\n"
      ++ "\n".intercalate (cs.map Correspondence.render)

end Specimen.Interp
