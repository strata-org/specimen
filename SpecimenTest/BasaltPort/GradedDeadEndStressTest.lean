import Basalt.Graded

/-!
# Value-dependent dead ends: does the generator's cascade survive grading?

`GradedArityStressTest.lean` settled the *level*-dependent case: `pair` is a nested `flatMap`, so an empty
sub-level costs one emptiness check and the product is never entered. It explicitly left open the harder
case, which is the one on record for the random generators: a **populated** level whose values all lead
nowhere. Two shapes, and they behave differently, so both are measured here.

* **`guard`** — a populated level every element of which the predicate rejects.
* **A doomed index** — `bindC` hands the continuation an auxiliary value (a type) at whose index the
  relation has no base case, so that sub-enumeration is empty at every level but only *discoverably* so.
  This is the enumerator's exact image of the recorded generator pathology.

## Answer

**The retry-driven exponential is gone; an exponential remains, and it is the carrier's fault, not the
algebra's.**

1. `guard` has no short-circuit of its own and cannot have one: `filterMap` builds level `n` in full and
   tests every element. Emptiness is a property of the *output*, known only after the last element.
2. The *enclosing* `pair` then treats that empty result exactly like an empty level — so a fully-rejected
   guard in **first operand position** is free, and in **last** position costs the whole prefix product.
   Dead-end cost is therefore a *scheduling* quantity, not a fixed one.
3. A doomed index costs `(k+1)^n` demands on the recursive occurrence for `k` rules at level `n`, and it
   is **independent of premise arity** — the doomed first premise short-circuits the rest of every rule,
   verbatim as in the arity file. That is the factor grading removes: `backtrack` re-selects earlier
   premises after a later one fails, so its cost per level is `k^arity`; convolution's is `k`.
4. But `(k+1)^n` is not linear, and the reason is that `Lv α = Nat → List α` is a **function**. There are
   only `O(iters · n)` distinct `(iterate, level)` pairs in a doomed descent; the carrier recomputes each
   one. Measured at `k = 4, n = 6`: **15 625 demands over 22 distinct pairs**, a 710x redundancy that
   grows as `(k+1)^n / n^2`. Memoising levels — Feat's `[[a]]`, which `Basalt/Graded.lean`'s own docstring
   names as the executable form — would collapse it to the linear bound and nothing else would.

### Measured (interpreted; ratios transfer, absolute times do not)

`kAry k` is `k` rules each with one binary recursive constructor. `dead` has no base case at all.

| shape | k | level | terms | ms |
|---|---|---|---|---|
| dead | 4 | 8 | 0 | 896 |
| dead | 4 | 9 | 0 | 4 470 |
| dead | 4 | 10 | 0 | 22 020 |
| dead | 18 | 5 | **0** | **15 940** |
| live | 4 | 5 | 43 008 | 429 |
| live | 18 | 3 | 29 160 | 576 |

Per-level growth of the dead column is 5.0x then 4.9x, i.e. `k+1`. One doomed index at Cedar's parameters
(18 alternatives, level 5) burns 16 s for nothing — about what enumerating 800 k live terms costs.

`guard`, same enumeration and level, varying the predicate and the operand position:

| predicate | guard position | terms | ms |
|---|---|---|---|
| accept all | first | 59 136 | 310 |
| **reject all** | **first** | 0 | **0** |
| accept all | last | 59 136 | 171 |
| **reject all** | **last** | 0 | **72** |
| no guard | — | 59 136 | 223 |

Reject-all-in-first-position is free. The identical guard moved to last position costs 42% of the full
accept-all run and returns nothing.

### Two corroborating measurements from a separate run

**The iteration count cannot drive the cascade — only the level can.** Holding the level fixed at 3 and
sweeping the iteration count `l = 4, 6, 8, 10, 12` at `k = 3` gives 27/45/44/72/38 ms — flat. `pay` bounds
the recursive descent by the *level*: once it reaches 0, `pay x 0 = []` returns without recursing. So the
`(k+1)^n` above is in `n` and only `n`, which is why raising the fixpoint's unrolling budget is safe and
raising the level is not.

**`guard` earns its place despite charging per survivor.** With a varying value space (two leaves, so a
value-dependent predicate is not vacuous — with a single leaf every value collapses to `0` and `half`
measures the same as `accept all`), at `k = 3`:

| predicate | level | terms | ms | µs per survivor |
|---|---|---|---|---|
| accept all | 6 | 12 317 184 | 49 362 | 4 |
| half | 6 | 396 576 | 10 105 | 25 |
| 1-in-8 | 6 | 96 228 | 5 657 | 59 |

A selective check costs ~15x more *per surviving term*, but **total** cost falls with selectivity, because
rejected values do not seed the next level. The decision-relevant comparison: obtaining the 1-in-8
survivors by enumerating unfiltered and filtering afterwards costs the accept-all row, 49 362 ms; guarding
inside the enumeration costs 5 657 ms for the same 96 228 terms — **8.7x cheaper**. So the cost `guard`
imposes is real but is bought back several times over.

## What is still wasted, precisely

Even with a memoised carrier: one full doomed sub-build **per dead auxiliary value per split**, because
`bindC x k n` invokes the continuation once per `(i, a)` and nothing caches "index `a` is empty". Plus,
irreducibly, `guard`'s own level build and one predicate call per element. The two available savings are
scheduling the guarded/most-constrained premise first, and turning an output-`guard` into an input-`if`
(what `lookupEnum` and `TConst` already do in `GradedStlcTest.lean`).
-/

open Basalt

namespace GradedDeadEnd

/-- Force-and-time. The print has to sit **inside** the timed region: `let v := e` never demands `e`,
which is why `GradedArityStressTest.lean` times externally. With the force inside, `IO.monoMsNow` is
enough and one file holds the whole table. Note `#eval` only flushes at the end of the command, so an
oversized case yields no output at all rather than a partial table. -/
def timed (label : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.print s!"{label} -> "
  IO.print (f ())
  let t1 ← IO.monoMsNow
  IO.println s!"  [{t1 - t0} ms]"

/-! ## Part 1: the doomed index -/

/-- `k` alternatives, each one binary recursive constructor: the union width Cedar has and the arity file
did not test. -/
def kAry (k : Nat) (r : Lv Nat) : Lv Nat :=
  (List.range k).foldl (fun acc _ =>
    Choice.union acc (Graded.pay (Graded.gmap (fun p => p.1 + p.2) (Graded.pair r r)))) Choice.nothing

/-- **No base case**, so every level is empty — and every level has to be built to find that out. -/
def deadIter (k : Nat) : Nat → Lv Nat
  | 0 => fun _ => []
  | m + 1 => kAry k (deadIter k m)

/-- The control: identical shape plus a leaf. -/
def liveIter (k : Nat) : Nat → Lv Nat
  | 0 => fun _ => []
  | m + 1 => Choice.union (Graded.single 0) (kAry k (liveIter k m))

-- Every level of a doomed index is empty, as a count. The *cost* of learning that is the point; see the
-- docstring table.
/-- info: [0, 0, 0, 0, 0, 0] -/
#guard_msgs in
#eval (List.range 6).map fun n => (deadIter 4 14 n).length

/-- info: [1, 4, 32, 320, 3584, 43008] -/
#guard_msgs in
#eval (List.range 6).map fun n => (liveIter 4 14 n).length

/-- The demand law, pinned on an instance small enough to print: `(k+1)^n` demands on the recursive
occurrence. Run with `lake env lean` and count the `E` lines —
`lake env lean … 2>&1 | grep -c '^E$'` gives 27 for `k = 2, n = 3`, 3125 for `k = 4, n = 5`.
Total-vs-distinct is the number that matters: label the trace `s!"E {m} {n}"` and at `k = 4, n = 6` there
are 15 625 demands over 22 distinct pairs. -/
def deadIterTraced (k : Nat) : Nat → Lv Nat
  | 0 => fun _ => []
  | m + 1 => fun n => dbg_trace "E"; kAry k (deadIterTraced k m) n

/-! ## Part 2: arity independence of a dead end

The one place grading strictly beats `backtrack`. A doomed *first* premise stops the whole rule, so the
demand count does not move when arity does. `backtrack` instead re-selects premise `j-1` when premise `j`
fails, which is where its `k ^ arity` per level comes from. -/

def convPow [Graded f] (x : f Nat) : Nat → f Nat
  | 0 => Graded.single 0
  | k + 1 => Graded.gmap (fun p => p.1 + p.2) (Graded.pair x (convPow x k))

/-- A doomed premise. `deadLeafTraced` below is the same thing with a demand trace:
`lake env lean … 2>&1 | grep -c '^d'` is `n+1` for every arity, which is the claim. -/
def deadLeaf : Lv Nat := fun _ => []

def deadLeafTraced : Lv Nat := fun _ => dbg_trace "d"; []

-- Same (empty) answer at arity 2, 7 and 14; the demand count is also the same, which is the point.
/-- info: (0, 0, 0) -/
#guard_msgs in
#eval ((convPow deadLeaf 2 5).length, (convPow deadLeaf 7 5).length, (convPow deadLeaf 14 5).length)

/-! ## Part 3: `guard`, and why position is the whole story -/

/-- A populated level, `w` elements wide, whatever the predicate later does with them. -/
def pop (w : Nat) : Lv Nat := fun n => (List.range w).map (n * w + ·)

def rejectAll : Nat → V := fun _ => .no
def acceptAll : Nat → V := fun _ => .yes

/-- Drop the conclusiveness flag, so the guarded enumeration is a drop-in premise. -/
def guarded (p : Nat → V) (x : Lv Nat) : Lv Nat := Graded.gmap Prod.fst (GradedBind.guard p x)

/-- The same `k`-fold product with the guarded premise **last** instead of first. -/
def convLast [Graded f] (x last : f Nat) : Nat → f Nat
  | 0 => last
  | k + 1 => Graded.gmap (fun p => p.1 + p.2) (Graded.pair x (convLast x last k))

-- Identical counts, so the two positions are the same enumeration; the docstring table is the cost
-- difference.
/-- info: (59136, 59136, 0, 0) -/
#guard_msgs in
#eval ((convPow (guarded acceptAll (pop 2)) 7 5).length,
       (convLast (pop 2) (guarded acceptAll (pop 2)) 6 5).length,
       (convPow (guarded rejectAll (pop 2)) 7 5).length,
       (convLast (pop 2) (guarded rejectAll (pop 2)) 6 5).length)

/-! ## Part 4: `bindC` over a dead-end auxiliary output

The recorded generator pathology verbatim: `typeE` yields a type, the continuation enumerates at that
index, and some of those indices are doomed. `bindC` invokes the continuation once per `(split, value)`,
so the doomed sub-build is paid once per dead auxiliary value per split — and, `Lv` being a function,
with no sharing between splits. `deadFrac` controls how many auxiliary values are dead. -/

def auxE (w : Nat) : Lv Nat := fun n => (List.range w).map (n * w + ·)

/-- Index `a` is live iff `a % m == 0`. -/
def family (k m : Nat) (a : Nat) : Lv Nat :=
  if a % m == 0 then liveIter k 14 else deadIter k 14

-- All auxiliary values dead (`m = 1` is "live iff `a % 1 == 0`", so flip to `m = 0`-free form): with
-- every index doomed the result is empty at every level, and the cost is one doomed sub-build per
-- `(split, value)` pair.
/-- info: ([2, 10, 74, 714], [0, 0, 0, 0]) -/
#guard_msgs in
#eval ((List.range 4).map fun n => (GradedBind.bindC (auxE 2) (family 4 1) n).length,
       (List.range 4).map fun n => (GradedBind.bindC (auxE 2) (fun _ => deadIter 4 14) n).length)

/-! ## The table

Uncomment to regenerate. Keep the cases small: `#eval` buffers, so one oversized entry loses the whole
table rather than truncating it. -/

-- #eval do
--   timed "k=4  dead n=8 " fun _ => (deadIter 4 14 8).length
--   timed "k=4  dead n=9 " fun _ => (deadIter 4 14 9).length
--   timed "k=4  dead n=10" fun _ => (deadIter 4 14 10).length
--   timed "k=18 dead n=5 " fun _ => (deadIter 18 14 5).length
--   timed "k=4  live n=5 " fun _ => (liveIter 4 14 5).length
--   timed "k=18 live n=3 " fun _ => (liveIter 18 14 3).length
--   timed "accept, first " fun _ => (convPow (guarded acceptAll (pop 2)) 7 5).length
--   timed "reject, first " fun _ => (convPow (guarded rejectAll (pop 2)) 7 5).length
--   timed "accept, last  " fun _ => (convLast (pop 2) (guarded acceptAll (pop 2)) 6 5).length
--   timed "reject, last  " fun _ => (convLast (pop 2) (guarded rejectAll (pop 2)) 6 5).length

end GradedDeadEnd
