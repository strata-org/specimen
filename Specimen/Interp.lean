import Specimen.Interp.Value
import Specimen.Interp.Env
import Specimen.Interp.Gen
import Specimen.Interp.Validate
import Specimen.Interp.CheckEnum
import Specimen.Interp.Bridge
import Specimen.Interp.Deriving
import Specimen.Interp.Preschedule
import Specimen.Interp.Extract

/-!
# Interpreting schedules at runtime

`derive_mutual` turns a `Schedules.Schedule` into Lean source and elaborates it. This directory runs a
schedule *as data* instead: build an `InterpEnv`, call `InterpEnv.generate`, get a `Plausible.Gen` of
untyped values — no elaboration, so trying a different schedule costs nothing to recompile.

Opt-in: `import Specimen` does not load it. Import `Specimen.Interp`.
-/
