# The runtime schedule interpreter

`derive_mutual` turns a schedule into Lean source and elaborates it. The generated code is typed and fast, but every "what if this premise came first?" costs a full derivation — minutes on a large mutual family. `Specimen.Interp` runs a schedule *as data* instead: build an `InterpEnv`, call `InterpEnv.generate`, and get a `Plausible.Gen` of untyped values, with no `MetaM` and no recompilation anywhere in the loop.

It is opt-in. `import Specimen` does not load it; write `import Specimen.Interp`. The library builds as its own root (`lakefile.toml` lists `Specimen.Interp` under the `Specimen` library's roots), so `lake build` compiles it even though nothing imports it by default.

## What it does

Reordering a constructor's premises is not a permutation of compiled steps: it changes which variables are unbound when each premise runs, so it changes what each premise produces, whether it is a producer or a check at all, and which mode it calls. The interpreter therefore schedules at runtime too — `Interp.Preschedule` takes the premises as data, replans them, and derives any mode the new order asks for.

The entry points, in the order a session uses them:

- `derive_relspec R` / `#specimen_relspec R` (`Interp.Extract`) read a real inductive and produce its `RelSpec` — the relation as data, premises and conclusion, no order chosen. Nothing is written by hand.
- `InterpEnv` (`Interp.Env`) holds the schedules and the leaves they bottom out at. Existing `Arbitrary`/`DecOpt` instances and plain functions become leaves through `Interp.Bridge` (`withArbitrary`, `withDecidable2`, `withFunc1`, …); `deriving ToVal, OfVal` (`Interp.Deriving`) points the interpreter at a project's own types.
- `InterpEnv.deriveClosure` brings up a mode plus everything it needs, and `InterpEnv.check` (`Interp.Validate`) reports every unresolvable step up front instead of letting `backtrack` absorb it.
- `InterpEnv.generate` (`Interp.Gen`) interprets a generator faithfully to what the pipeline emits, attributing each discard to the step that caused it. `interpChecker` and `interpEnumRel` (`Interp.CheckEnum`) interpret the other two sorts.
- `Interp.Runner` (`sample`, `profileCtor`, `sweepPlans`, `tunePlan`) makes two plans comparable; `Interp.Learn` (`learnSchedules`) runs the closure-wide loop, pushing blame down through call frames; `Interp.Diagnose` names the premise order or floor change that would fix a constructor that rarely succeeds.

The umbrella module `Specimen/Interp.lean` carries a worked session and the full module table.

## Reading the output

Three kinds of bad news stay apart because the fixes differ: `[interp] ` means a leaf or mode is missing (misconfiguration); `[interp:reject:<step>] ` means the schedule rejected an attempt at a named step (a discard); running out of fuel is neither. `RunStats` counts the three separately, and `CtorProfile` breaks discards down per step.

Two trace classes follow the compiled deriver's side of the same story: `trace.specimen.pinnedOrders` reports when the interpreter starts from the orders the compiled derivation settled on, and `trace.specimen.droppedCtors` (from the deriver itself) reports constructors a mode was derived without.
