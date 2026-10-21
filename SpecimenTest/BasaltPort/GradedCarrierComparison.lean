import Basalt.Graded
import Specimen.LazyList

/-!
# The carrier decides everything: `Lv` vs `Array (List α)` vs `Array (LazyList α)`

`GradedDeadEndStressTest.lean` established that a doomed index costs `(k+1)^n` demands on the recursive
occurrence, that 100 % of that is redundancy (15 625 demands over 22 distinct `(iterate, level)` pairs),
and therefore that the fix is to memoise levels. This file tries the fixes and measures them.

## Result

| config | `Lv = Nat → List α` | `Array (List α)` | `Array (LazyList α)` |
|---|---|---|---|
| dead k=4, N=10 | 22 020 ms | 5 ms | **~0 ms** |
| dead k=18, N=5 | 15 940 ms | 6 ms | **~0 ms** |
| live k=4, N=5 | 429 ms | 2 343 ms | **44 ms** |
| live k=18, N=3 | 576 ms | 6 832 ms | **116 ms** |

Counts agree across all three carriers (43 008 and 29 160 for the live rows), so these are the same
enumeration, not three different ones.

**`Array (LazyList α)` wins on every axis** — it removes the dead-end exponential *and* is an order of
magnitude faster than the status quo on live enumeration.

## Why each of the other two loses

**`Lv` cannot be memoised in place.** Two attempts failed, and the reason is structural rather than
fixable: `Lv α = Nat → List α` is a *function*, so a partially-applied iterate never becomes a shared
value — the equation compiler treats the level as just another parameter and there is nothing for a cache
to attach to. (A `let`-bound table inside the returned lambda is worse than nothing: Lean may zeta-reduce
it into the body, rebuilding the table per call.) So "add memoisation to `Lv`" is not a small change; the
carrier has to become data.

**`Array (List α)` is eager**, so it computes every level of every iterate whether demanded or not. That
is why it fixes the dead rows and *regresses the live rows by 5–12×* — the common case.

**`Array (LazyList α)` gets both**, because the two properties are independent: the `Array` memoises
*across* levels (killing the `(k+1)^n` redundancy) and the `LazyList` stays lazy *within* a level (so an
undemanded level costs a thunk, and `Thunk` caches once forced).

## The `partial` objection does not apply here

`Basalt/Graded.lean` chose `Nat → List α` partly to avoid reasoning at `LazyList`, "whose round-robin bind
is `partial` and has no induction principle". That is true of `roundRobinConcat` and `bindLazyList`
(`Specimen/LazyList.lean:137,150`) — and `roundRobinConcat` does not merely lack a proof, it genuinely
diverges on infinitely many empty sub-lists.

But round-robin exists to buy *fairness across infinite alternatives*, and grading already supplies
fairness via the level structure. Within a single **finite** level plain concatenation is correct, and
`LazyList.append`, `LazyList.mapLazyList` and `LazyList.concat` (lines 65, 77, 129) are all **total
defs**. `flatMapL` below is built from `concat`, never from `bindLazyList`. So the lazy carrier costs
nothing in provability.

## Before this becomes Basalt's carrier

1. **Keep the proofs.** Every closure lemma in `Basalt/GradedSound.lean` is stated about `Lv`. Prove the
   new carrier *observationally equal* to `Lv` (`∀ n, (toLv c) n = ...`) and transport, rather than
   restating ~20 lemmas.
2. **`LazyList` lives in Specimen, not Basalt.** This file can import both; Basalt cannot import Specimen.
   Either Basalt gets its own lazy list or `Specimen/LazyList.lean` moves down.
3. **`N` is now explicit in the carrier.** `nothingL` needs a width, so the `Graded` instance cannot be
   width-polymorphic in the current class shape. Either thread `N` or use a growable representation.
4. Numbers are interpreted (`#eval`): ratios transfer, absolute times do not.
-/

open Basalt

namespace GradedCarrier

/-! ## Carrier C: an array of levels, each a lazy list -/

/-- Levels as an `Array` (memoised across levels), each level a `LazyList` (lazy within a level). -/
abbrev LvL (α : Type) := Array (LazyList α)

/-- `flatMap` by plain concatenation. **`LazyList.concat`, never `bindLazyList`** — the latter is
`partial` and routes through the diverging `roundRobinConcat`. Grading makes round-robin unnecessary
inside a finite level. -/
def flatMapL (f : α → LazyList β) (l : LazyList α) : LazyList β :=
  LazyList.concat (LazyList.mapLazyList f l)

def nothingL (N : Nat) : LvL α := (Array.range (N + 1)).map fun _ => LazyList.lnil

def singleL (N : Nat) (a : α) : LvL α :=
  (Array.range (N + 1)).map fun n =>
    if n = 0 then LazyList.lcons a ⟨fun _ => LazyList.lnil⟩ else LazyList.lnil

def unionL (x y : LvL α) : LvL α :=
  (Array.range x.size).map fun n => LazyList.append x[n]! y[n]!

def payL (x : LvL α) : LvL α :=
  (Array.range x.size).map fun n => if n = 0 then LazyList.lnil else x[n-1]!

def gmapL (g : α → β) (x : LvL α) : LvL β := x.map (LazyList.mapLazyList g)

/-- Convolution, level by level: `⨆_{i+j=n}`. -/
def pairL (x : LvL α) (y : LvL β) : LvL (α × β) :=
  (Array.range x.size).map fun n =>
    (List.range (n + 1)).foldr (fun i acc =>
      LazyList.append (flatMapL (fun a => LazyList.mapLazyList (fun b => (a, b)) y[n - i]!) x[i]!) acc)
      LazyList.lnil

/-! ## The same doomed/live pair as `GradedDeadEndStressTest`, at this carrier -/

def kAryL (N k : Nat) (r : LvL Nat) : LvL Nat :=
  (List.range k).foldl (fun acc _ =>
    unionL acc (payL (gmapL (fun p => p.1 + p.2) (pairL r r)))) (nothingL N)

/-- No base case, so empty at every level. -/
def deadIterL (N k : Nat) : Nat → LvL Nat
  | 0 => nothingL N
  | m + 1 => kAryL N k (deadIterL N k m)

/-- The control: identical shape plus a leaf. -/
def liveIterL (N k : Nat) : Nat → LvL Nat
  | 0 => nothingL N
  | m + 1 => unionL (singleL N 0) (kAryL N k (liveIterL N k m))

/-! ## Pinned: the counts match the `Lv` carrier

The timings are the point and live in the header; these guard the thing a carrier change could silently
break — that it is still the *same enumeration*. Both figures are the ones
`GradedDeadEndStressTest.lean` reports for plain `Lv`. -/

-- A doomed index is empty at every level here too.
/-- info: [0, 0, 0, 0, 0, 0] -/
#guard_msgs in
#eval ((deadIterL 5 4 14).toList.take 6).map fun l => l.toList.length

-- The live control reproduces the plain carrier's level counts exactly.
/-- info: [1, 4, 32, 320, 3584, 43008] -/
#guard_msgs in
#eval ((liveIterL 5 4 14).toList.take 6).map fun l => l.toList.length

-- And at Cedar's union width.
/-- info: 29160 -/
#guard_msgs in
#eval (liveIterL 3 18 14)[3]!.toList.length

end GradedCarrier
