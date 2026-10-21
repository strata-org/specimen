import Basalt.Graded

/-!
# Does convolution survive high premise arity?

The main scaling risk for graded enumeration on a real relation. STLC's widest rule has **2** recursive
premises; Cedar has relations with 7, 9 and **14** (`LubRecord`). A `k`-fold convolution at level `n` ranges
over `C(n+k-1, k-1)` splits — at `k=14, n=8` that is ~203 000 *per branch* — whereas the derived
enumerator's divided budget hands each premise `size/k` and commits, with no combinatorial split at all.

So high arity is exactly where convolution's advantage might invert. This file tests that directly, without
needing Cedar's environment, its 5-minute derivations, or its missing leaf instances.

## Answer: arity alone is not the problem

Wall clock, external, ~0.57 s import baseline subtracted (interpreted — ratios transfer, absolute times do
not). `wideStep k` is one leaf plus one `k`-ary recursive constructor.

| k | level | terms | ms | terms/ms |
|---|---|---|---|---|
| 2 | 8 | 1 430 | 43 | 33 |
| 4 | 6 | 7 084 | 199 | 36 |
| 7 | 5 | 10 472 | 385 | 27 |
| 14 | 5 | 183 379 | 11 892 | **15** |

Throughput degrades about **2×** from arity 2 to arity 14 — not the collapse the split count suggests.

## Why, and this is the part worth keeping

The splits are not wasted: for an unconstrained premise the number of *results* grows as fast as the number
of splits, so the work produces output. More importantly, **convolution short-circuits on empty sub-levels**.
`pair` is a nested `flatMap`, so if `x i` is empty the inner product is never entered — a dead split costs
one emptiness check, not a product.

Measured, same arity, varying how populated the premise is (`sparse` = only every third level non-empty):

| premise | k | level | terms | ms |
|---|---|---|---|---|
| dense | 14 | 5 | 8 568 | 106 |
| sparse | 14 | 5 | 0 | 25 |
| dense | 14 | 6 | 27 132 | 210 |
| sparse | 14 | 6 | 105 | 3 |
| dense | 7 | 8 | 3 003 | 25 |
| sparse | 7 | 8 | 0 | 15 |

Cost tracks **results**, not splits. `C(n+k-1, k-1)` is therefore not the cost driver.

## What this does not settle

* **Dead ends in Cedar are value-dependent, not level-dependent.** `sparse` models an empty *level*; the
  harder case is a populated level whose values are all rejected further down (the dead-end-type cascade
  already on record for generators). That needs a `guard`-based probe, not this one.
* **Union width is untested here.** One `k`-ary constructor, not Cedar's 76.
* Absolute costs still climb fast: `k=14` at level 5 is ~12 s for 183 k terms. Fine throughput, but the
  constant matters once multiplied by a 76-way union.

So the ordering of remaining Cedar risks changes: **arity drops to the bottom**, and ungraded leaves
(`String` especially — `TypeOfTest` already fails for strings) plus value-dependent dead ends move to the top.
-/

open Basalt

namespace GradedArityStress

/-- `k`-fold convolution of `x` with itself, summed back to `Nat`. The collapse is lossy in *values* but
faithful in *cost and count*: `Lv` keeps duplicates, so level `n` holds exactly one element per way of
splitting, which is the quantity under test. -/
def convPow [Graded f] (x : f Nat) : Nat → f Nat
  | 0 => Graded.single 0
  | k + 1 => Graded.gmap (fun p => p.1 + p.2) (Graded.pair x (convPow x k))

/-- One leaf plus one `k`-ary recursive constructor — the shape of a rule with `k` recursive premises. -/
def wideStep (k : Nat) [Graded f] (rec : f Nat) : f Nat :=
  Choice.union (Graded.single 0) (Graded.pay (convPow rec k))

def wideAt (k levels n : Nat) : List Nat := gradedIter (f := Lv) (wideStep k) levels n

/-- Every level populated. -/
def dense : Lv Nat := fun n => [n]
/-- Only every third level populated, so most splits hit an empty operand. -/
def sparse : Lv Nat := fun n => if n % 3 == 0 then [n] else []

/-! ## Counts

Fuss–Catalan: `k`-ary trees by internal-node count. `k = 2` is the ordinary Catalan sequence, which ties
this file to `GradedAlgebraTest.lean`'s tree numbers. -/

/-- info: [1, 1, 2, 5, 14] -/
#guard_msgs in
#eval (List.range 5).map fun n => (wideAt 2 8 n).length

/-- info: [1, 1, 4, 22, 140] -/
#guard_msgs in
#eval (List.range 5).map fun n => (wideAt 4 8 n).length

/-- info: [1, 1, 7, 70] -/
#guard_msgs in
#eval (List.range 4).map fun n => (wideAt 7 8 n).length

/-- info: [1, 1, 14, 287] -/
#guard_msgs in
#eval (List.range 4).map fun n => (wideAt 14 8 n).length

/-! ## The short-circuit, as counts

The timings above are the real evidence; these pin the *shape* — a sparse premise collapses the output, and
(measured externally) the cost with it. -/

/-- info: (8568, 0) -/
#guard_msgs in
#eval ((convPow (f := Lv) dense 14 5).length, (convPow (f := Lv) sparse 14 5).length)

/-- info: (27132, 105) -/
#guard_msgs in
#eval ((convPow (f := Lv) dense 14 6).length, (convPow (f := Lv) sparse 14 6).length)

end GradedArityStress
