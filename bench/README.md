# Benchmarks

Measurements behind the graded-enumeration work (see `Docs/Graded-enumeration.md`). They are not part of
the test suite: `lake build Bench` compiles them, which also runs their correctness checks (`#guard`s that
the things being timed enumerate the same set), and nothing runs the timings by default. Time the compiled
executables, not `#eval`: interpreted timings are dominated by the interpreter.

```
lake build Bench                       # compile, and check
lake build bench-same-discipline       # or any executable below
.lake/build/bin/bench-same-discipline fun 9 11
```

## `bench-same-discipline` — `Bench/GradedVsDerivedSameDiscipline.lean`

The enumerator `derive_mutual` emits for STLC `typing`, against levels built to follow the same budget
rule, so both enumerate exactly the same set at each budget (checked) and only the machinery differs.
Arguments: `[fun] BUDGET…` (`fun` for goal type `Nat → Nat`, otherwise `Nat`). For each budget it prints
the term count, the time to force everything, and the time for the first 1 000 terms.

## `bench-concat-ablation` — `Bench/GradedVsDerivedConcatAblation.lean`

Where the gap between the two goes. A ladder from the derived enumerator to levels, one change per rung,
every rung checked to enumerate the same set: L0 derived (with in-order concatenation for `bind`), L1 a
hand copy of the emitted code, L2 without the derived `lookup`, L3 without `Except`, L4 strict lists, L5
levels.

- `ladder [fun] BUDGET…` times every rung forcing all terms.
- `RUNG BUDGET K` (`RUNG` one of `L0`…`L5`, `all4`, `all5`) reads the first `K` terms at goal
  `Nat → Nat` and prints the peak resident memory.

## `bench-lazy-levels` — `Bench/GradedLazyLevelBenchmark.lean`

Strict, lazy and chunked levels when a single level is huge: STLC with a leaf pool of width `W` at level
0, read for its first `K` terms. Arguments: `CARRIER W K N [CHUNK]`, where `CARRIER` is `strict`, `lazy`,
`chunked` (chunk size `CHUNK`, default 256) or `check` (chunked levels flatten to the strict ones, in the
same order, at several chunk sizes). `N` is the number of levels built. The carriers are local copies rather than Basalt's proved
`GradedRun`/`GradedLazy`/`GradedChunked` because the benchmark measures variants the proved modules
do not export (the `pair2` convolution, and levels over Specimen's `LazyList`); its `check` mode
pins the copies against the strict carrier.

## Measured

On the development machine, compiled, goal `Nat → Nat`:

| | budget 11, all 57 866 terms |
|---|---|
| derived enumerator, as emitted | 693 ms |
| L0, concatenating `bind` | 490 ms |
| L1, hand copy | 414 ms |
| L2, without the derived `lookup` | 353 ms |
| L3, without `Except` | 123 ms |
| L4, strict lists | 16 ms |
| L5, levels | 5 ms |

| `W = 3000`, first 5 000 terms | time | peak memory |
|---|---|---|
| strict levels | 2 684 ms | 1.6 GB |
| lazy levels | 3 ms | 67 MB |
| chunked levels (256) | 7 ms | 71 MB |
