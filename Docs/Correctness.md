# Soundness & Completeness of Derived Producers

Machine-checked soundness and completeness of specimen's derived generators, enumerators, and
checkers, following *Computing Correctly with Inductive Relations* (PLDI'22) and *Generating Good
Generators for Inductive Relations* (POPL'18).

All code lives under `Specimen/Correctness/`, aggregated by `Specimen/Correctness.lean` and built by
the test library (`import Specimen` does not load it). The proofs about *emitted* code live in
`SpecimenTest/Correctness/`, because each runs its own `derive_*`. The `SPMF` files read Basalt's
sub-probability semantics, which sits on Mathlib — Mathlib arrives with the `basalt` dependency as a
cached build (`lake exe cache get`; `lake update` runs it) and is loaded only by those files.

## What is proved

| Producer | Soundness | Completeness |
|---|---|---|
| Checker (`DecOpt`) | `decOpt fuel = .ok true → R`, and refutation-soundness: `.ok false → ¬R` | `R → ∃ fuel, decOpt fuel = .ok true` |
| Enumerator | every enumerated `x` satisfies `R x` | every `x` with `R x` is enumerated at some budget |
| Generator | every `x` in the support satisfies `R x` | every `x` with `R x` is in the support at some budget |

twice over, at two levels:

1. **Generically**, for any relation reflected as data (`RelSpec`), through a verified interpreter —
   correctness lives once, inherited by every relation.
2. **For the emitted code itself**, on concrete relations: the definitions `derive_checker` /
   `derive_mutual` actually emit, proved either by direct decomposition or by a *bridge* equating the
   emitted definition with the generic interpreter at a reconstructed step.

## How the proofs are built

The proofs are written by hand, but most of the work is done once. Generic results are proved a single
time over relations reflected as data (`RelSpec`), and each relation inherits them by instantiation.
What is written per relation is the connection to it: an adequacy lemma saying the reflected spec
means the same as the inductive, and a bridge showing the emitted code equals the interpreter at one
step (`lk_bridge`, `TypingBridge`). Some STLC results are proved instead by decomposing the emitted code
directly. A new relation proved this way needs its own adequacy lemma and bridge.

The deriver can also prove its own output, as *Computing Correctly* does: see
[Proofs `derive_mutual` emits](#proofs-derive_mutual-emits).

## The map

### Generic theory (`Specimen/Correctness/`)

- **`Semantics.lean`** — outcome-set semantics for the three producers and the target predicates
  (`CheckerSound`/`CheckerRefute`/`CheckerComplete`/`DecOptMonotone`, `EnumSound`/`EnumComplete`,
  `GenSound`/`GenComplete`/`SizedMonotone`). No `Set`, no Mathlib.
- **`Combinators.lean`** — relation-independent specs of the checker and enumerator combinators,
  including the K3 `andOpt` laws and `squashErrors` (values kept, at most one inconclusive error).
- **`LazyListLemmas.lean`** — the membership algebra for the lazy-list core the enumerators use.
- **`Reflect.lean`** — a relation as first-class data: `RelSpec` (constructors = premises +
  conclusion) with the inductive denotation `Provable`, whose `intro`/`rec` stand in for the shallow
  relation's constructors and recursor. Lean cannot quantify over "an arbitrary inductive relation
  and its constructors", so this is what makes a single generic proof possible; the residual
  per-relation duty is an adequacy bridge `Provable rSpec args ↔ R args`, designed to be routine
  (`EvSlice` has one).
- **`CheckerInterp.lean`** — checkers as fuel-iteration of a one-level step: soundness, refutation
  soundness, bounded refutation for structurally decreasing relations.
- **`ProducerInterp.lean`** — the same for enumerators, over `List`.
- **`GenInterp.lean`** — generic generator *soundness* at the real `Plausible.Gen`, axiom-free.
- **`GenSupport.lean`** — the support laws for `Plausible.Gen` in the soundness direction, proved:
  a value produced by `m >>= k` comes from one `m` produces (`genSupportAt_bind_sub`), and one produced
  by `backtrack` from one of its branches (`genSupportAt_backtrack_sub`). The reverse direction fails
  there, because `>>=` threads one `StdGen` through both halves rather than splitting it as QuickChick's
  bind does.
- **`GenInterpSPMF.lean`** — the generator interpreter again, at `SGen` (`SPMF` under the sampler's
  `OptionT` and `ExceptT Exhaustion`), where both support laws are *theorems*
  (`SPMF.mem_support_bind_iff`, Basalt's `mem_support_searchWith_ok`): the `Produces` and `Refutes`
  algebra, soundness **and** measure-pair completeness, fuel monotonicity, refutation from a failed
  search (`refutes_of_not_produces`), and the mutually-recursive family form (`genRelFam`).
- **`LeafSPMF.lean`** — an unconstrained draw at `SGen` reaches its `SPMF` support (`ReachesAll`, a
  `GenRel`, so `walk fixpoint` proves it per leaf), and the base `Nat` draw's completeness up to its
  size.
  A generator emitted under `specimen.emitBasalt` is polymorphic in Basalt's `Gen` class, so the same
  emitted definition is read at `SPMF` for reasoning and at `Plausible.Gen` for running.
- **`Specimen.Enum.Laws`** — the laws of the enumeration readings hosted in `Specimen.Enum`: at
  `Finite`, `WFinite` and `CostGraded Finite`, with and without failure and labels, a run is related to
  the generator's `SPMF` meaning by a `GenRel`, so `walk` proves it per generator.
  `SpecimenTest/Correctness/EnumLaws.lean` and `EnumBacktrackingTest.lean` are their regression tests;
  `DerivedEnumLaw.lean` walks one for a derived generator (`EnumeratesWith` for `Between`).
- **`EvSlice.lean`** — evenness end to end against the real relation: checker and enumerator sound and
  complete, generator sound at `Plausible.Gen`, plus `Ev` reflected as a `RelSpec` with its adequacy
  proof.
- **`EvGenSPMF.lean`** — the `Ev` generator proved sound and complete through `GenInterpSPMF`.

### Emitted code (`SpecimenTest/Correctness/`)

Each runs its own `derive_*` (inside a namespace, so flag-on builds cannot collide) and proves things
about the exact emitted definition — these are also regression guards on emission shape: change the
emitter, the scorer's schedule, the dispatch guards or the weights, and they stop compiling.

- **`DerivedCheckerSoundness.lean`** — the checker `derive_checker` emits for `Sorted`, proved sound
  through the generic two-counter theory.
- **`StlcMeasures.lean`** — the budget measures for the derived STLC generators (`budget`, `tdepth`,
  `varBound`, `leafBound`, and the type-draw budget `tyNeed` through `outTy`), plus completeness of the derived
  unconstrained `type` generator.
- **`StlcGeneratorSoundness.lean`** — the derived well-typed-term generator is sound at `SPMF`, by
  direct decomposition of the emitted pools; with non-vacuity witnesses.
- **`StlcCompleteness.lean`** — the converse by hand: every well-typed term is reachable given the
  budgets, with a closed-form corollary (`2 ^ hdepth e * (ldepth e + 2)`).
- **`DerivedGeneratorViaInterp.lean`** — the emitted `lookup` generator **is** `genRelB` at a
  reconstructed step (`lk_bridge`), so soundness, completeness, `NeverFails` and
  refutation-soundness all follow from the generic theorems.
- **`TypingBridge.lean`** — the same bridge for the emitted `typing` generator: dispatch guards, size
  halving, the unconstrained type draw and the delegated `lookup` instance, all in one step, with the
  external producer's correctness as a hypothesis. Its completeness side conditions coincide with
  `StlcCompleteness`'s hand-derived ones — the cross-check that the generic route computes the same
  budgets.
- **`VerdictFidelity.lean`** — the three-valued verdict discipline: a generator whose premise checker
  can only run out of budget can never report a definite refutation. The statement is false of any
  emission that collapses `error` into `refute`; `Fail` and `FailWith` separate them precisely so it
  holds.

## Proofs `derive_mutual` emits

Under `specimen.emitSound` and `specimen.emitComplete`, `derive_mutual` proves each worker it derives
sound and complete for its relation, against Basalt's `SPMF` reading of the code
(`specimen.emitBasalt`). Every law is a theorem the kernel checks; a step a heuristic cannot close fails
the derivation (or, with `specimen.admitFailedParts`, is admitted with `sorry` and a warning), so a
proof is never wrong, only missing.

| Law | Worker | States |
|---|---|---|
| `w.sound` | generator, enumerator | every value produced satisfies the relation |
| `w.checkSound` | checker | `.ok true` only when the relation holds |
| `w.searchSound`, `w.searchFinds` | enumerator's search, used by a checker | a value found satisfies the relation |
| `w.complete` | each | a value (or input) in the relation is produced (accepted) at some fuel and size |
| `w.instComplete` | its instance | `BacktrackGenForComplete` / `EnumForComplete` / `DecOptComplete` |
| `w.searchHits` | enumerator's search | a value in the relation is found |

`specimen.emitComplete` alone proves the generators; `specimen.completeAllSorts` adds the
enumerators and checkers. A worker's laws assume the laws of what it calls: the derived workers'
own, and for anything else an instance of the matching class (`ArbitrarySizedComplete α` for an
unconstrained draw, `BacktrackGenForComplete α P` for a hand-written generator, `ArbitrarySizedSearch`
and `ArbitrarySizedHits` for a checker's search over a type). A missing one is reported by name.
`Specimen.Correctness.LeafLaws` provides them for the instances `Specimen.BasaltBridge` supplies: a
`Nat` above or below a bound (`n ≤ x`, `x < n`, …) and a pair constrained equal. A recursive type
`deriving Basalt.ArbitrarySized` gets its laws by induction: `arbitrary_complete`,
`arbitrary_search_derived` and `arbitrary_hits_derived` (`LeafComplete.lean`).

**Across files.** For a large derivation, `specimen.deferSound` and `specimen.deferComplete` record
the components instead of proving them, and these commands, in files that import the derivation,
prove them, so that Lake checks the files in parallel:

- `#specimen_prove_sound`: the soundness proofs.
- `#specimen_prove_all_but [c, …]`: the enumerators' searches, and every component but those listed.
- `#specimen_prove_stmts c`, `#specimen_prove_slice c i of n`, `#specimen_prove_finish c`: a large
  component's parts stated once, proved in `n` slices, and assembled.
- `#specimen_audit "suffix"`: counts each law over the workers whose names end in `suffix`, fails if
  a worker lacks a law its sort's proved laws include (`laws missing`), and fails if a law depends on
  an axiom other than `propext`, `Classical.choice` and `Quot.sound`.

**Options.** `specimen.parallelProofs` proves a block's workers as parallel theorems.
`specimen.reachExtended` lets `reach_close`, the completeness search, use premises in context more
freely (a check's proposition or its negation, a `match` rewritten either way, a search over a type's
values); `specimen_complete_case` turns it on only for a case the plain search does not close, so a
derivation that does not need it pays nothing.

The tests are in `Specimen/Correctness/*Test.lean` (one feature each: `EmitSoundTest`, `CompleteOfTest*`,
`CheckSearchTest`, `SearchPolyTest`, `SizeSplitTest`, …) and `SpecimenTest/Correctness/Suite`
(relations derived in several modes with every law proved and audited: search trees, permutations,
STLC, regular expressions, a key-value store, polymorphic relations, …), all built by the test
library (`lake test`).

## Budgets, and why completeness is conditional

Unconditional completeness is false by design: the emitted `size = 0` pool withholds every recursive
constructor, and the schedule halves `size` at branching constructors — a balanced binary tree of
constructor depth `d` genuinely needs `size ≈ 2^d`. Completeness statements therefore carry a measure
pair `(φ, σ)` — fuel and size — plus, where the emitted code delegates at `initSize`, bounds like
`leafBound` (de Bruijn indices the `lookup` producer must reach, and literals the unconstrained `Nat`
draw reaches only up to its size) and `tyNeed` (depth of the types the `TApp` branch draws
unconstrained). The emitted `BacktrackGenFor` instance hard-wires the delegated
fuel to `10000`, which is a real (if remote) incompleteness ceiling, and it is visible in the
side conditions.

## Axioms

- Checker and enumerator results, and generator results at `SPMF`: `propext`, `Classical.choice`,
  `Quot.sound` only — Lean's standard three. `Classical.choice` enters through `SPMF` (classical
  measure-theoretic semantics) and through unfolding `partial_fixpoint` draws; checker/enumerator
  results that avoid `SPMF` use only `propext`/`Quot.sound`.
- Generator *soundness* at `Plausible.Gen`: the standard axioms only, through the proved support laws
  in `GenSupport.lean`.
- Generator *completeness* is proved at `SPMF` only. At `Plausible.Gen` it would need the reverse
  support laws, which fail there: `>>=` threads its seed rather than splitting it, so not every
  combination of outcomes is reachable. Nothing in the development is postulated.

Every headline theorem carries a `#guard_msgs`-pinned `#print axioms`, so an axiom regression fails the
build.
