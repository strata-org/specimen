import Specimen
import Specimen.Basalt

/-!
# Enumerators under `specimen.emitBasalt`, reached from checkers

Two shapes the flag-off path never reaches. An enumerator for a relation with a type parameter draws
its unconstrained values through `Basalt.ArbitrarySized`, so that is its parameter's binder. A checker
that calls an enumerator of its own `derive_mutual` block reaches the Basalt worker directly, and reads
it as `Specimen.BasaltBridge` reads one.
-/

set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true
set_option guard_msgs.diff true

namespace BasaltEnumeratorTest

/-! ## A type parameter -/

inductive Mem {α : Type} : α → List α → Prop where
  | here : ∀ x xs, Mem x (x :: xs)
  | there : ∀ x y xs, Mem x xs → Mem x (y :: xs)

/-- Checking `Uses n` searches for a list containing `n`: an enumerator for `∃ l, Mem n l`. -/
inductive Uses : Nat → Prop where
  | mk : ∀ n l, Mem n l → Uses n

#guard_msgs(drop info) in
derive_mutual checker (fun n => Uses n)

#guard match DecOpt.decOpt (Uses 3) 2 with | .ok true => true | _ => false

/-! ## A checker and an enumerator in one block -/

mutual
/-- Checking `P n` enumerates an `m` with `Q n m`. -/
inductive P : Nat → Prop where
  | mk : ∀ n m, Q n m → P n
/-- Enumerating an `m` with `Q n m` checks `P` on the predecessor of the input. -/
inductive Q : Nat → Nat → Prop where
  | base : Q 0 0
  | step : ∀ n m, P n → Q (n + 1) m
end

#guard_msgs(drop info) in
derive_mutual checker (fun n => P n)

#guard match DecOpt.decOpt (P 2) 6 with | .ok true => true | _ => false

-- At a budget too small to reach `Q 0 0`, the answer is inconclusive, not a refutation.
#guard match DecOpt.decOpt (P 2) 4 with | .error _ => true | .ok _ => false

end BasaltEnumeratorTest
