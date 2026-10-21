import Specimen.Interp.Value
import Specimen.Interp.Env
import Specimen.Interp.Gen
import Specimen.Interp.Validate
import Specimen.Interp.CheckEnum
import Specimen.Interp.Bridge
import Specimen.Interp.Deriving
import Specimen.Interp.Preschedule
import Specimen.Interp.Extract
import Specimen.Interp.Runner
import Specimen.Interp.Learn

/-!
# Interpreting schedules at runtime

`derive_mutual` turns a `Schedules.Schedule` into Lean source and elaborates it. That is the right
thing for production — the generated code is typed and fast — but it makes experimenting expensive:
every "what if this step came first?" costs a full derivation, which on a large mutual family is
minutes.

This directory runs a schedule *as data* instead. It is opt-in: `import Specimen` does not load it. No `MetaM`, no elaboration, no metaprogramming:
build an `InterpEnv`, call `InterpEnv.generate`, get a `Plausible.Gen` of untyped values.

Running a schedule is only half of it. Trying a *different* schedule means reordering the
constructor's premises, and that is not a permutation of the steps: reordering changes which
variables are still unbound when each premise runs, so it changes what each premise produces, whether
it is a producer or a check at all, and which spec — at which output mode — it calls. So
`Interp.Preschedule` does the scheduling at runtime too, from the constructor's premises as data, and
derives any mode a reordering asks for. Nothing recompiles.

## The pieces

| Module | Role |
| --- | --- |
| `Interp.Value` | `Val`, the untyped value the interpreter manipulates, and evaluation/matching of `ConstructorExpr`/`Pattern` against it |
| `Interp.Env` | `RelSchedule` (a schedule as runtime data) and `InterpEnv` (schedules + leaf interpretations) |
| `Interp.Gen` | `interpRel`: the generator interpreter, faithful to what the pipeline emits, attributing each discard to the step that caused it |
| `Interp.CheckEnum` | `interpChecker`/`interpEnumRel`: the other two sorts, in one module because a checker enumerates its candidates and an enumerator checks its premises |
| `Interp.Validate` | `InterpEnv.check`: every unresolvable step, reported up front rather than swallowed by `backtrack` |
| `Interp.Bridge` | `ToVal`/`OfVal` and lifting helpers, so existing `Arbitrary`/`DecOpt` instances and plain Lean functions become leaves |
| `Interp.Preschedule` | `RelSpec`/`CtorSpec` (a relation as data), `reschedule` (plan → schedule), `deriveMode`/`deriveClosure` (bring up the modes a plan needs), and the plan mutations |
| `Interp.Extract` | `#specimen_relspec` / `derive_relspec`: read a real inductive and get its `RelSpec`, so nothing has to be written by hand |
| `Interp.Runner` | `sample`, `profileCtor`, `sweepPlans`, `tunePlan`: the experiment loop that makes two plans comparable |
| `Interp.Learn` | `PlanBook`, `closureStats`, `rootCauses`, `learnSchedules`: the closure-wide loop, with blame pushed down through call frames and a fixpoint to stop at |

## A session

```lean
open Specimen Specimen.Interp

-- 1. The relations, as data: premises and conclusions, no ordering chosen yet.
--    `derive_relspec` reads the declaration; it does not run the derivation pipeline.
derive_relspec MyRel
derive_relspec MyDep
def specs : List RelSpec := [myRelRelSpec, myDepRelSpec]

-- 2. The leaves the schedules bottom out at.
def leaves : InterpEnv :=
  (({} : InterpEnv).withArbitrary ``Nat Nat).withDecidable2 ``LE.le (fun a b : Nat => a ≤ b)

-- 3. Derive the mode you want, plus everything it needs.
#eval match leaves.deriveClosure specs [myKey] with
  | .error e => IO.println e
  | .ok env => IO.println env.checkReport   -- `backtrack` would otherwise hide a missing leaf

-- 4. Measure, and see where the attempts go.
#eval do IO.println (renderProfile (← env.profileCtor myKey ``MyRel.node (size := 5)))

-- 5. Compare every candidate plan, or let the discards pick the next mutation.
#eval do IO.println (renderPlanSweep myCtor (← leaves.sweepPlans specs myRelSpec myKey
  ``MyRel.node (size := 5)))
#eval do
  let (best, trace) ← leaves.tunePlan specs myRelSpec myKey ``MyRel.node (size := 5)
  IO.println (renderTune myCtor trace)
```

Three kinds of bad news are kept apart, because the fixes differ. Interpreter *misconfiguration*
carries an `[interp] ` prefix and means a leaf or a mode is missing; a *discard* carries
`[interp:reject:<step>] ` and means the schedule rejected the attempt at a named step; running out of
fuel means neither. `RunStats` counts all three separately, `CtorProfile` breaks the discards down per
step, and `InterpEnv.runCtorOnce` runs one constructor with no backtracking so nothing is absorbed.

## Scope

All three producer sorts are interpreted: generators (`Interp.Gen`), and checkers and enumerators
(`Interp.CheckEnum`). Theorem schedules are not. Failure means something different in each sort — a
failed check refutes a checker but only prunes an enumerator — and `Interp.CheckEnum` documents the
correspondence step by step against the emitted code.
-/
