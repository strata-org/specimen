import Specimen
import Specimen.Basalt

/-!
# Regression: derived workers recurse structurally on `fuel`

Every derived worker takes `fuel`, `initSize` and `size`, all `Nat`. Left to find the recursive
argument itself, Lean tries each combination of the changing `Nat` parameters across a mutual block and
gives up past ten, falling back to well-founded recursion, whose unfolding lemma the kernel checks
eagerly; on a large block that check can exhaust memory. A cycle of four relations is the smallest block
past the limit (two candidates per worker, sixteen combinations).

The check fails if any worker in the block was compiled by well-founded recursion, which packs a mutual
block into a `_mutual` definition and its arguments into a `_unary` one. It has to hold with
`specimen.emitBasalt` both off and on, since the two emit their own `termination_by` clauses.
-/

mutual
inductive Cycle0 : Nat → Prop where
  | z : Cycle0 0
  | s : Cycle1 n → Cycle0 (n + 1)
inductive Cycle1 : Nat → Prop where
  | s : Cycle2 n → Cycle1 (n + 1)
inductive Cycle2 : Nat → Prop where
  | s : Cycle3 n → Cycle2 (n + 1)
inductive Cycle3 : Nat → Prop where
  | s : Cycle0 n → Cycle3 (n + 1)
end

#guard_msgs(warning, drop info) in
derive_mutual generator (∃ n, Cycle0 n)

open Lean in
run_cmd do
  let packed := (← getEnv).constants.map₂.toList.filterMap fun (n, _) =>
    match n with
    | .str _ s => if s == "_mutual" || s == "_unary" then some n else none
    | _ => none
  unless packed.isEmpty do
    throwError "derived workers compiled by well-founded recursion: {packed}"
