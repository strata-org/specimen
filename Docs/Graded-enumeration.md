# Graded enumeration

Specimen's derived enumerators are budget-indexed: `enumSized s` returns everything that fits in budget
`s`, every call re-enumerates the smaller budgets, and a binary rule splits its budget evenly between its
recursive premises. Graded enumeration is the alternative from Duregård's Feat: an enumeration is a
sequence of **levels**, level `n` holding exactly the derivations of size `n`, each level finite. This
document describes the graded algebra in Basalt, the carriers that run it, what is proved about it, and
what it costs. Nothing in Specimen emits graded enumerators yet; this is the library and the evidence for
doing so.

## Contents

1. Levels
2. Carriers
3. What is proved, and where
4. From the deriver's schedules to rules
5. Measured costs
6. Using it
7. Not done

---

## 1. Levels

Basalt's `Basalt/Graded.lean` defines two classes.

- `Graded` has `nothing`, `union`, `single`, `pay` (shift up one level: one rule application), `gmap` and
  `pair`. `pair` is convolution: level `n` of `pair x y` is every `(a, b)` with `a` at level `i` and `b`
  at level `n - i`. That is Cantor's diagonal stated over finite levels, so it is fair without any
  interleaving.
- `GradedBind` adds the value-dependent operations: `bindC` (dependent convolution, for a premise whose
  output carries its own size), `bind` (level-preserving, for one that does not) and `guard` (a decidable
  premise, with a three-valued verdict).

The split is forced, not stylistic. Counting, `Cnt α := Nat → Nat`, is phantom in `α`, so it can implement
`Graded` but has no value to pass to a continuation. So a relation built from `Graded` operations alone
can be counted without being enumerated; one that needs `bindC` cannot. STLC's `TApp` is the example: its
argument type occurs in both premises, which `pair` cannot express (`SpecimenTest/BasaltPort/
GradedStlcTest.lean`).

Levels grade the **derivation**, `|D| = 1 + Σ|Dᵢ|`, not the output value, because a conclusion need not
be a constructor applied to premise outputs. A relation with ambiguous derivations therefore yields
duplicates.

Choosing between `bindC` and `bind` per premise is a correctness question, not a performance one: `bind`
for a premise whose output carries its own size makes the enumeration incomplete (a small derivation with
a large auxiliary output appears at no level). That bug shipped once, which is why the adequacy proofs in
§3 are stated against the inductive relation and not only between two readings of the same enumeration.

## 2. Carriers

The algebra has three interpretations: values `Lv α := Nat → List α`, counts `Cnt`, and specification
`SetE α := Nat → α → Prop`. `Lv` is the reference but cannot be run efficiently: it is a function, so
nothing memoises a level, and a value-dependent dead end recomputes the same levels exponentially often
(15 625 demands over 22 distinct levels in `GradedDeadEndStressTest.lean`). Three executable carriers
memoise levels in an `Array` of thunks:

| carrier | module | a level is | cost of the first `k` of a level |
|---|---|---|---|
| `LvT α = Array (Thunk (List α))` | `GradedRun` | a strict list | the whole level |
| `LvL α = Array (Thunk (LList α))` | `GradedLazy` | a lazy list | `k` |
| `LvC α = Array (Thunk (LList (List α)))` | `GradedChunked` | a lazy list of strict chunks of at least `C` | `k`, rounded up to a chunk |

Strict levels are fastest when everything is forced and ruinous when one level is huge and only its first
terms are wanted, which is what property testing does. Lazy levels fix that; chunked levels recover most of
the strict throughput (in measurements during development, about 1.3–1.4× strict when forcing everything)
while keeping the first `k` cheap. Each carrier has an agreement relation (`Agree`, `AgreeL`, `AgreeC`) with
`Lv` that every operation preserves, so a result proved about `Lv` transfers to the carrier that runs.

All of these, and the algebra, are Basalt modules (they import no Mathlib).

## 3. What is proved, and where

In Basalt:

- `GradedSound`: `Agrees` (values against specification) and `Counts` (values against counts), closed
  under every operation, iteration included.
- `GradedRun`, `GradedLazy`, `GradedChunked`: the carrier agreement relations, closed under every
  operation; `mem_take_sound` (lazy) and `takeC_eq` (chunked) for reading the first `k`.

In Specimen's test library, `SpecimenTest/BasaltPort/`:

- `GradedStlcAdequacy`: STLC `typing Γ e τ` holds exactly when the graded enumeration produces `e` at some
  level, against Lean's own inductive `typing`. Soundness is unconditional; completeness needs the leaf
  enumerations to cover their types. `GradedStlcLazyAdequacy` and `GradedStlcChunkedAdequacy` restate it
  on the lazy and chunked carriers (for every chunk size), and add that the first `k` terms read from any
  level are well typed (`stlc_take_sound`, `stlc_takeC_sound`).
- `GradedRuleAdequacy`: the same result proved once for rules given as data (`RuleShape.Body`: recursive
  call, auxiliary producer with its grading choice, check, side condition, pay, conclusion), and shown to
  be the hand-written STLC result: one unfolding of the rule data is the hand-written step function.
- `GradedCedarRuleAdequacy`: the generic theorem instantiated at relations transcribed from Cedar's typing
  spec, including the recursive `AllLub` and the mutual `Lub` family.

These use only `propext` and `Quot.sound`.

## 4. From the deriver's schedules to rules

`ScheduleTranslate` translates the deriver's `Schedules.ScheduleStep` into `RuleShape.Body`, at the
interpreter's value domain, and proves what can be proved: the translation agrees with a declarative
reading of the steps (`holdsR_translate`); for check-only schedules the graded denotation equals a
three-valued checker walk (`denoteL_checkOnly`); and a schedule plus a verified environment discharges the
generic theorem's obligations (`schedules_adequateL`). It also records six obstructions. The main one is
that the grading of each premise is not something the current schedules carry: the emitted enumerators
split budgets (`size' / k`) and bind at one budget, so the grading choice has to be made by whatever emits
graded code. These theorems also use `Classical.choice`.

## 5. Measured costs

Compiled, on the development machine; the benchmarks are in `bench/` (see `bench/README.md`).

**Derived enumerator against levels, same set.** For STLC at goal `Nat → Nat`, levels built to the derived
enumerator's own budget rule enumerate exactly its set. Forcing all 57 866 terms at budget 11 takes 693 ms
derived and 5 ms as levels; at budget 13 (190 049 terms), 2 666 ms and 24 ms. An ablation ladder attributes
the gap (budget 11):

| step | time |
|---|---|
| derived, as emitted | 693 ms |
| `bind` by in-order concatenation instead of round-robin | 490 ms |
| a hand copy of the emitted code | 414 ms |
| the derived `lookup` replaced by a scan | 353 ms |
| no `Except` (a failed match is an empty list) | 123 ms |
| strict lists | 16 ms |
| levels | 5 ms |

No single step dominates; the largest are dropping laziness (about 8×), `Except` (about 3×) and exact
levels instead of nested budgets (about 3×). Round-robin was about 100× before its queue was made two-list
(`LazyList.roundRobinConcat`); it is now about 1.4×. Strict lists win when everything is forced but not
for the first `k`: at budget 15 the first 1 000 terms cost 333 ms and 235 MB on strict lists, against about
35 ms and 65 MB lazily or as levels.

**One huge level.** STLC with 3 000 leaves at level 0, reading the first 5 000 terms: strict levels 2.7 s and
1.6 GB, lazy levels 3 ms and 67 MB, chunked levels 7 ms and 71 MB.

**Arity and dead ends.** Premise arity up to 14 costs about 2× throughput, not the split count, because
convolution skips empty sub-levels (`GradedArityStressTest`). A guard that rejects a whole level is free in
first premise position and costs the whole prefix product in last, so dead-end cost depends on premise
order (`GradedDeadEndStressTest`).

## 6. Using it

Graded enumerations are written by hand against Basalt's classes. A step function takes the recursive
occurrence as a parameter and is iterated with `gradedIter` (or `gradedIterIx` for an indexed family); see
`GradedStlcTest.stlcStep`. To run it, write the same step against a carrier (`LvL` for first-`k` use,
`LvC` for throughput) and read levels upward until enough values are in hand. The `Agree*` lemmas let a
soundness or completeness proof done at `SetE` or `Lv` carry over to the carrier.

## 7. Not done

- **No emitted graded code.** The deriver emits budget-split enumerators. Emitting graded ones needs a
  grading choice per premise (`bindC` or `bind`), which the schedules do not carry (§4).
- **No count-only fast path.** Relations whose rules are all applicative could be counted without
  enumeration, but nothing detects or uses this.
- **Benchmarks.** `bench/` holds the three benchmarks behind §5's numbers.
