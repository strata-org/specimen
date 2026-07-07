# Error Classification: Inconclusive vs Impossible

When a Specimen-derived generator or enumerator fails, there are two fundamentally different reasons:

1. **Inconclusive** — the producer ran out of fuel, ran out of size, or exhausted its retry budget. It *might* succeed with a larger size. Example: a recursive generator hits its size limit before finding a valid construction path, but a larger size would allow trying recursive constructors that could succeed.

2. **Impossible** (or "disproved") — the constraint is unsatisfiable for this particular input. No amount of fuel or size will help. Example: generating `BST 5 3 t` where `lo=5 > hi=3` — every constructor tries a `Between 5 x 3` check which definitively fails because no `x` can satisfy `5 ≤ x ≤ 3`.

## Why the distinction matters

The primary consumer of this distinction is **checkers that invoke enumerators**. When a checker calls an enumerator to verify a hypothesis, it needs to know:

- **Disproved**: the enumerator proved this hypothesis is false → the checker can confidently return `false`.
- **Inconclusive**: the enumerator ran out of fuel → the checker should return "unknown" rather than a false negative.

Without this distinction, checkers either miss real counterexamples (treating all errors as unknown) or report false negatives (treating all errors as disproved).

### Concrete example

Suppose we're generating `BST lo hi t` (a binary search tree with keys in `[lo, hi]`). The derived generator uses `backtrack` to try each constructor:

- **Leaf**: always succeeds (base case).
- **Node k left right**: needs `lo ≤ k ≤ hi`, then recursively generates subtrees.

When `lo > hi`, the Node branch fails because no valid `k` exists. Previously, after exhausting all branches, `backtrackFuel` reported `"out of fuel"` which suggests "try with more fuel." But the real situation is that this input is *unsatisfiable* — no amount of fuel will help.

With error classification, `backtrackFuel` tracks whether any branch was inconclusive (fuel/size exhaustion) vs all branches definitively failed. If all branches threw non-fuel errors, the final error is `"all branches failed"` (impossible/disproved). If at least one was inconclusive, it still reports fuel exhaustion (because that branch *might* have succeeded with more fuel).

## How generators fail: size vs fuel vs definitive

Derived generators have three layers of resource bounds, each producing a different failure mode:

1. **Size** (`size` parameter, decremented on recursive calls): controls depth of generated terms. When `size = 0`, only base-case constructors are attempted. If all base cases fail for this input, that's a definitive failure at this size — but a larger size would have allowed recursive constructors that might succeed. This is the most common source of inconclusive failures.

2. **Fuel** (`fuel` parameter, set to a large constant like 10000): a safety bound to guarantee termination. Reaching fuel=0 is rare in practice and always inconclusive.

3. **Definitive failure** (DecOpt checks, pattern match wildcards): a constructor branch fails because the constraint genuinely can't be satisfied for this input. E.g., `WithinCapacity (v :: s) c` fails when the buffer is full. These throw `Plausible.Gen.genericFailure` (`"Generation failure."`).

When `backtrackFuel` exhausts all branches, it classifies the overall failure: if any branch's error was inconclusive (fuel/size), the overall error is inconclusive. If every branch failed definitively, the overall error is impossible.

## Where the classification lives

### Generators (`GeneratorCombinators.lean`)

`backtrackFuel` tracks an `anyInconclusive` flag as it tries branches:

- Each branch failure is checked against `GenError.isInconclusive`.
- If ANY branch was inconclusive → final error is "out of fuel" (might succeed with larger size).
- If ALL branches were definitively impossible → final error is "all branches failed".

This classification does NOT affect generator control flow or PRNG consumption — `backtrackFuel` retries unconditionally regardless of error type. The classification only determines the error message that propagates to callers.

### Enumerators (`EnumeratorCombinators.lean`)

`lazyListBacktrackOpt` uses `isInconclusiveError` to decide whether an enumerator error "poisons" the overall result:

- **Inconclusive error** (fuel/size exhaustion): sets `anyNone := true`, meaning the final result will be "unknown" rather than "false".
- **Disproved error** (not inconclusive): treated like `.ok false` — skip to the next candidate without poisoning.

This is where the classification has a real control-flow effect: a disproved branch does not prevent the checker from returning a definitive `false` if all other branches are also disproved.

## Public API

- `Gen.GenError.isInconclusive : GenError → Bool` — classifies an error.
- `Gen.GenResult α` — `ok`, `insufficientFuel`, or `impossible`.
- `Gen.runChecked : Gen α → Nat → IO (GenResult α)` — runs a generator and classifies the outcome.

## Error messages recognized as inconclusive

| Message | Source |
|---------|--------|
| `"Specimen: out of fuel (termination limit reached)"` | Derived producer fuel=0 or size=0 case |
| `"out of fuel"` | Plausible's `Gen.backtrackFuel` |
| `"Gen.runUntil: Out of attempts"` | `Gen.runUntil` retry limit |

All other `GenError` values are treated as definitive/impossible.

## Design note: generators throw `genericFailure`

All failure paths in derived generators (DecOpt check failures, pattern match wildcards) throw the same `Plausible.Gen.genericFailure` (`"Generation failure."`). This is NOT recognized as inconclusive — meaning individual branch failures are classified as definitive. This is correct: a `DecOpt` check failing (e.g., `WithinCapacity` on a full buffer) is a definitive fact about that branch with that input, not a resource limitation.

The inconclusive classification triggers from the *structural* resource mechanisms: the derived producer's `fuel` or `size` parameter reaching zero (which throws `Gen.outOfFuelError`), or `Gen.runUntil` exhausting its retry budget.
