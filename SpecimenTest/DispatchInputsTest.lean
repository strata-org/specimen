import Specimen
import Specimen.Basalt

/-!
# `specimen.dispatchInputs`: a derived generator skips constructors its inputs cannot match

`Kind b n` has one constructor per value of the input `b`, each matching it at its first step. With
dispatch on, the emitted branch list keeps a constructor only when its leading input pattern fits, so
`backtrack` never picks a branch that fails at once. The weights are not recounted after the filter: a
dropped branch would have failed on every run with these inputs, so the distribution is unchanged.

Pinned below: the guarded list appears in the emitted code with dispatch on and not with it off, and the
generator still produces only valid values.
-/

open Plausible

inductive Kind : Bool → Nat → Prop where
  | zero : Kind true 0
  | pos : ∀ n, Kind false (n + 1)

namespace On
set_option specimen.richOutput false in
set_option specimen.textOutput 3 in
set_option specimen.dispatchInputs true in
/-- List.filterMap -/
#guard_msgs (substring := true, whitespace := lax) in
scoped derive_mutual (fun (b : Bool) => ∃ n, Kind b n)
end On

namespace Off
set_option specimen.richOutput false in
set_option specimen.textOutput 3 in
set_option specimen.dispatchInputs false in
-- `backtrack [`, without the namespace, so the pin also holds under `specimen.emitBasalt`.
/-- backtrack [ -/
#guard_msgs (substring := true, whitespace := lax) in
scoped derive_mutual (fun (b : Bool) => ∃ n, Kind b n)
end Off

-- Every generated value is valid, and none of the 200 runs fails.
open On in
/-- info: (200, true) -/
#guard_msgs in
#eval show IO (Nat × Bool) from do
  let mut ok := 0
  let mut valid := true
  for i in List.range 200 do
    let b := i % 2 == 0
    match ← (Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Kind b n) 5) 5).toBaseIO with
    | .ok n => ok := ok + 1; valid := valid && (if b then n == 0 else n > 0)
    | .error _ => pure ()
  return (ok, valid)
