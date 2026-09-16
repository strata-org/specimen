import Plausible.Gen

open Plausible

/-! # Runtime helpers for compiled theorem tests

Small combinators referenced by the code `specimen_test` emits. The test loop and shrink
descent themselves are generated in `Specimen/Tactic.lean`, not defined here.
-/

namespace Specimen

/-- Returns `true` iff the result is `.ok true`. Used by compiled `validShrinks` functions. -/
def isOkTrue : Except GenError Bool → Bool
  | .ok true => true
  | _ => false

/-- Fair round-robin interleave of multiple lists.
    `interleave [[a,b,c], [1,2], [x,y,z,w]] = [a, 1, x, b, 2, y, c, z, w]` -/
partial def interleave (lists : List (List α)) : List α :=
  let rec go (remaining : List (List α)) (acc : List α) : List α :=
    let step := remaining.filterMap fun
      | [] => none
      | h :: t => some (h, t)
    match step with
    | [] => acc.reverse
    | _ =>
      let heads := step.map Prod.fst
      let tails := step.map Prod.snd
      go tails (heads.reverse ++ acc)
  go lists []

end Specimen
