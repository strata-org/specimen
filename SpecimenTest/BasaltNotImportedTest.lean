import Specimen

/-!
# Specimen without `Specimen.Basalt`

The default configuration: `import Specimen` does not load Basalt, and deriving works without it. With
`specimen.emitBasalt` set but the import missing, deriving stops with an error naming the import
instead of failing inside the generated code.

The file pins the flag off, since the default configuration is what it tests.
-/

set_option specimen.emitBasalt false

namespace BasaltNotImportedTest

-- `import Specimen` does not bring Basalt's classes into scope.
/-- info: false -/
#guard_msgs in
#eval show Lean.MetaM Bool from do return (← Lean.getEnv).contains `BacktrackGenFor

inductive Between : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, lo ≤ hi → Between lo hi lo
  | there : ∀ lo hi n, Between (lo + 1) hi n → Between lo hi n

#guard_msgs(warning, drop info) in
derive_generator (fun lo hi => ∃ n, Between lo hi n)

inductive Small : Nat → Prop where
  | zero : Small 0
  | one : Small 1

/--
error: `specimen.emitBasalt` requires `import Specimen.Basalt` in this file: derived generators are emitted against Basalt's `Gen`, `BacktrackGen` and `BacktrackGenFor`
-/
#guard_msgs in
set_option specimen.emitBasalt true in
derive_generator ∃ n, Small n

end BasaltNotImportedTest
