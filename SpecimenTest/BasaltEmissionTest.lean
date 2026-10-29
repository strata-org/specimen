import Specimen
import Specimen.Basalt

/-!
# Generators derived under `specimen.emitBasalt`

The rest of the suite exercises the Basalt path only when the whole library is built with the flag on.
This file sets it itself, so the default build covers the main emission shapes: a `DecOpt` premise, a
recursive call, a delegated `BacktrackGenFor` producer, an unconstrained value of a datatype with a
derived `Basalt.ArbitraryFueled`, and `derive_mutual` with and without inputs. Each is checked to
register a `BacktrackGenFor` instance and to generate only values satisfying its relation, run at
`Plausible.Gen` through the bridge from seeded streams.

Every relation is declared here: a module compiled without the flag cannot serve one compiled with it.
-/

open Plausible

set_option specimen.emitBasalt true

namespace BasaltEmissionTest

/-- Every sample satisfies `p`, and at least half the draws succeeded, so the check is not vacuous. -/
def allSatisfy (xs : Array (Option α)) (p : α → Bool) : Bool :=
  xs.all (·.all p) && 2 * (xs.filter Option.isSome).size ≥ xs.size

/-- A `DecOpt` premise and a recursive call. -/
inductive Between : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, lo ≤ hi → Between lo hi lo
  | there : ∀ lo hi n, Between (lo + 1) hi n → Between lo hi n

-- The emitted shape: branches as functions, and at size 0 the recursive constructor as its
-- conclusion, cut off where it matches. `there`'s conclusion constrains no input, so it always does.
/-- (1, fun (_ : Unit) => Specimen.truncated)] -/
#guard_msgs (substring := true, whitespace := lax) in
derive_generator (fun lo hi => ∃ n, Between lo hi n)

example (lo hi : Nat) : BacktrackGenFor Nat (fun n => Between lo hi n) := inferInstance

-- Generated values lie in `[lo, hi]`.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let xs ← Gen.sampleWithSeed 100
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Between 3 8 n) 10) 10 20261014
  return allSatisfy xs fun n => 3 ≤ n && n ≤ 8

/-- A premise only a hand-written producer can solve: the deriver cannot invert `n % 4 = 1`. -/
inductive OneMod4 : Nat → Prop where
  | mk : n % 4 = 1 → OneMod4 n

instance : BacktrackGenFor Nat (fun n => n % 4 = 1) where
  gen size _ := do
    let k ← chooseNat 0 size
    pure (4 * k + 1)

#guard_msgs(drop info) in
derive_generator ∃ n, OneMod4 n

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let xs ← Gen.sampleWithSeed 100
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => OneMod4 n) 10) 10 20261014
  return allSatisfy xs fun n => n % 4 == 1

/-- A datatype drawn unconstrained, through its derived `Basalt.ArbitraryFueled`. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
  deriving Repr

deriving instance Basalt.ArbitraryFueled for Tree

inductive Elem : Nat → Tree → Prop where
  | here : Elem x (.node l x r)
  | left : Elem x l → Elem x (.node l y r)

def Tree.elem (x : Nat) : Tree → Bool
  | .leaf => false
  | .node l y r => x == y || l.elem x || r.elem x

#guard_msgs(drop info) in
derive_generator (fun x => ∃ t, Elem x t)

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let ts ← Gen.sampleWithSeed 100
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun t => Elem 7 t) 10) 10 20261014
  return allSatisfy ts fun t => t.elem 7

/-- Input dispatch: `τ` is matched by each constructor's conclusion, so the branch list is filtered by
it (and each branch sits inside `List.filterMap`, with no expected type of its own). -/
inductive Ty | nat | bool
  deriving Repr, DecidableEq

inductive Expr
  | lit (n : Nat)
  | isPos (n : Nat)
  | add (l r : Expr)
  deriving Repr

inductive HasType : Expr → Ty → Prop
  | lit (n) : HasType (.lit n) .nat
  | isPos (n) : n ≠ 0 → HasType (.isPos n) .bool
  | add (l r) : HasType l .nat → HasType r .nat → HasType (.add l r) .nat

def Expr.typeOf : Expr → Option Ty
  | .lit _ => some .nat
  | .isPos n => if n ≠ 0 then some .bool else none
  | .add l r => if l.typeOf == some .nat && r.typeOf == some .nat then some .nat else none

set_option specimen.dispatchInputs true in
/-- List.filterMap -/
#guard_msgs (substring := true, whitespace := lax) in
derive_generator (fun τ => ∃ e, HasType e τ)

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let es ← Gen.sampleWithSeed 100
    (fun i => ArbitrarySizedSuchThat.arbitrarySizedST
      (fun e => HasType e (if i % 2 = 0 then .nat else .bool)) 10) 10 20261014
  return allSatisfy es fun e => e.typeOf.isSome

/-- `derive_mutual` with an input. -/
inductive Below : Nat → Nat → Prop where
  | zero : Below 0 (n + 1)
  | succ : Below m n → Below (m + 1) (n + 1)

#guard_msgs(drop info, drop warning) in
derive_mutual (fun n => ∃ m, Below m n)

example (n : Nat) : BacktrackGenFor Nat (fun m => Below m n) := inferInstance

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let xs ← Gen.sampleWithSeed 100
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun m => Below m 6) 10) 10 20261014
  return allSatisfy xs fun m => m < 6

/-- `derive_mutual` with no inputs, the second branch-emission path. -/
inductive Even : Nat → Prop where
  | z : Even 0
  | ss : ∀ n, Even n → Even (n + 2)

#guard_msgs(drop info, drop warning) in
derive_mutual generator (∃ n, Even n)

example : BacktrackGenFor Nat (fun n => Even n) := inferInstance

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let xs ← Gen.sampleWithSeed 100
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Even n) 10) 10 20261014
  return allSatisfy xs fun n => n % 2 == 0

end BasaltEmissionTest
