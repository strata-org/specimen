# Specimen 
Specimen complements the Plausible property-based testing library by automatically deriving generators, enumerators, and checkers for inductive relations.

Specimen's design is heavily inspired by [Coq/Rocq's QuickChick](https://github.com/QuickChick/QuickChick) library and the following papers:
- *Testing Theorems, Fully Automatically* (OOPSLA 2026)
- [*Computing Correctly with Inductive Relations* (PLDI 2022)](https://dl.acm.org/doi/10.1145/3519939.3523707)
- [*Generating Good Generators for Inductive Relations* (POPL 2018)](https://dl.acm.org/doi/10.1145/3158133)

*Specimen is a testing and verification tool* - it is designed to help find bugs during development, not to serve as a security guarantee or correctness proof for production or enterprise workloads. Intended use is development-time property-based testing, rapid prototyping of invariants, and pre-proof exploration of conjectures.

## Overview
Like QuickChick, Specimen uses the following typeclasses:
- `Arbitrary`: unconstrained random generators for inhabitants of algebraic data types. This is imported from Plausible
- `ArbitrarySuchThat`: constrained generators which only produce random values that satisfy a user-supplied inductive relation
- `ArbitraryFueled`, `ArbitrarySizedSuchThat`: versions of the two typeclasses above where the generator's size parameter is made explicit (the former is imported from Plausible)
- `Enum, EnumSuchThat, EnumSized, EnumSizedSuchThat`: Like their `Arbitrary` counterparts but for deterministic enumerators instead
- `DecOpt`: Checkers (partial decision procedures that return `Except GenError Bool`) for inductive propositions

Specimen provides various top-level commands which automatically derive generators for Lean `inductive`s (the file [Specimen/README.md](Specimen/README.md) has more details):

**1. Deriving unconstrained generators/enumerators**              
An *unconstrained* generator produces random inhabitants of an algebraic data type, while an unconstrained enumerator *enumerates* (deterministically) these inhabitants. 
          
Users can write `deriving Arbitrary` and/or `deriving Enum` after an inductive type definition, e.g.
```lean 
inductive Foo where
  ...
  deriving Arbitrary, Enum
```
Alternatively, users can also write `deriving instance Arbitrary for T1, ..., Tn` (or `deriving instance Enum ...`) as a top-level command to derive `Arbitrary` / `Enum` instances for types `T1, ..., Tn` simultaneously. This also works for mutually recursive types:
```lean
mutual
  inductive MutEven where
    | zero : MutEven
    | succOdd : MutOdd → MutEven
  inductive MutOdd where
    | succEven : MutEven → MutOdd
end

deriving instance Enum for MutEven, MutOdd
```

To sample from a derived unconstrained generator, users can simply call `runArbitrary`, specify the type 
for the desired generated values and provide some `Nat` to act as the generator's size parameter (`10` in the example below):

```lean
#eval runArbitrary (α := Tree) 10
```

Similarly, to return the elements produced from a derived enumerator, users can call `runEnum` like so:
```lean
#eval runEnum (α := Tree) 10
```

**2. `derive_mutual` — the recommended command for constrained derivation**

`derive_mutual` is the primary command for deriving constrained generators, enumerators, and checkers. It supersedes the older `derive_generator`/`derive_enumerator`/`derive_checker` commands by providing:
- Automatic dependency discovery (derives instances for sub-relations)
- Multi-output generation (a single hypothesis step can produce multiple existential variables)
- True mutual recursion (multiple specs compiled into a shared `mutual` block)
- Quality scoring and schedule search with branch-and-bound optimization

**Syntax**:
```lean
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

-- Derive a constrained generator (default sort is `generator`)
derive_mutual
  (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Derive multiple specs at once (they can call each other)
derive_mutual
  (fun G t => ∃ (e : term), typing G e t)

-- Derive with explicit sort keywords
derive_mutual
  generator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t),
  checker (fun lo hi t => BST lo hi t)

-- Derive an enumerator
derive_mutual enumerator
  (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Multi-output: generate all existentials at once
derive_mutual
  (∃ (Γ : List type) (e : term) (τ : type), typing Γ e τ)
```

Each entry can be prefixed with `generator` (default), `enumerator`, or `checker`. When `specimen.autoDeriveDeps` is `true`, Specimen automatically discovers and derives instances for sub-relations referenced in the constructors. When `specimen.multiOutput` is `true`, the scheduler can produce multiple existential outputs in a single hypothesis step.

To sample from a generator derived via `derive_mutual`:
```lean
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balanced 5 t)) 10
```

**3. `derive_generator` / `derive_enumerator` — single-spec constrained derivation**

These commands derive a constrained generator or enumerator for a single specification. They are still supported and useful for quick one-off derivations:

```lean
derive_generator (fun n => ∃ t, balanced n t)
derive_enumerator (fun n => ∃ t, balanced n t)
```

In the command `derive_generator (fun x1 ... xn => ∃ x, P x1 ... x ... xn)`:
- `P` must be an inductively defined relation
- `x` is the value to be generated (bound by `∃`)
- `x1 ... xn` are input parameters (bound by `fun`)
- Multiple existential outputs are supported: `derive_generator (fun n => ∃ a b, Split n a b)`

To sample from the derived producer:
```lean
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balanced 5 t)) 10
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balanced 3 t)) 3
```

**4. `derive_checker` — partial decision procedures**

A checker for an inductively-defined `Prop` is a `Nat -> Except GenError Bool` function, which 
takes a `Nat` argument as fuel and returns an error if it can't decide whether the `Prop` holds (e.g. it runs out of fuel),
and otherwise returns `ok true` / `ok false` depending on whether the `Prop` holds.

```lean
derive_checker (fun n t => balanced n t)
```

**5. Options**

| Option | Default | Description |
|--------|---------|-------------|
| `specimen.autoDeriveDeps` | `false` | Automatically derive dependency instances for sub-relations in `derive_mutual` |
| `specimen.multiOutput` | `false` | Allow multi-output production steps (multiple `∃` vars generated per hypothesis) |
| `specimen.scoreType` | `"Scoring.DefaultScore"` | Scoring strategy for schedule quality evaluation (see below) |
| `specimen.weightFn` | `"Scoring.balancedCtorWeight"` | Weight function for constructor frequency in derived generators (see below) |
| `specimen.weightModifier` | `""` | Optional modifier layered on top of the weight function (see below) |
| `specimen.fuel` | `10000` | Fuel (termination budget) for derived generators/enumerators/checkers |
| `specimen.richOutput` | `true` | Emit rich HTML widget output in the Lean infoview |
| `specimen.textOutput` | `0` | Plain-text output verbosity (0=off, 1=summary, 2=problems, 3=full) |
| `specimen.silent` | `false` | Suppress all informational derivation output (`Try this:` suggestions and `derive_mutual` widgets/text). Instances are still installed |
| `specimen.searchLimit` | `200000` | Max hypothesis orderings to evaluate per constructor during schedule search |

**Scoring strategies** control how Specimen evaluates and selects among candidate schedules during derivation. The `specimen.scoreType` option selects the active strategy:

| Strategy | Option value | Description |
|----------|-------------|-------------|
| Default | `"Scoring.DefaultScore"` | Sum of (checks, length, unconstrained) — the original heuristic. Minimizes total checking work. |
| Worst-leaf | `"Scoring.WorstLeafScore"` | Takes the max (not sum) across coverage-trie leaves — penalizes worst-case input paths. |
| Density | `"Scoring.DensityScore"` | Categorical density classification (Total/Partial/Backtracking/Checking) from Section 4 of *Testing Theorems, Fully Automatically*. Prefers schedules that avoid backtracking. |

For example, to use the density scoring strategy from the *Testing Theorems* paper:
```lean
set_option specimen.scoreType "Scoring.DensityScore"
derive_mutual
  (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)
```

See [`ScheduleQualityRegressionTest.lean`](./SpecimenTest/ScheduleQualityRegressionTest.lean) for a comparison of all three strategies on the same relation.

**Weight functions** control how often each constructor is chosen at runtime by the backtracking combinator. The `specimen.weightFn` option selects the active weight function. A weight function has the signature:

```
CtorWeightFn := Name → List Nat → DeriveSort → Float → Bool → Nat → Nat → Nat → Nat
```

Arguments: `(ctorName, outputIndices, deriveSort, scoreBadness, isRec, size, numBase, numRec) → weight`
- `ctorName`: the fully qualified name of the constructor (e.g. `` `List.cons ``).
- `outputIndices`: the output position indices for this derivation.
- `deriveSort`: whether we are deriving a `Generator`, `Enumerator`, `Checker`, or `Theorem`.
- `scoreBadness`: a [0,1] float from the scorer indicating schedule quality for this constructor (0 = best, 1 = worst). Computed at elaboration time and baked in as a literal.
- `isRec`: whether this constructor is recursive.
- `size`: the current generation size parameter (decreases as the generator recurses deeper).
- `numBase` / `numRec`: counts of base vs recursive constructors for this inductive.

The return value is a `Nat` weight — the backtracking combinator picks constructors proportionally to their weights. The `ctorName`, `outputIndices`, and `deriveSort` arguments enable per-constructor and per-mode weight overrides without needing to write a separate weight function for each type.

| Weight function | Option value | Description |
|----------------|-------------|-------------|
| Balanced | `"Scoring.balancedCtorWeight"` | Controls aggregate P(recursive) with quality bias. Base ctors get a 4x boost. Good default for inductives with many recursive constructors. |
| Size-proportional | `"Scoring.sizeProportionalCtorWeight"` | `base=1, rec=size+1`. The strategy used by QuickChick. |
| Score-aware | `"Scoring.scoreAwareCtorWeight"` | Boosts good constructors (low badness 1–4) and applies size-based penalty to recursive ones. |
| Quality-only | `"Scoring.qualityCtorWeight"` | No structural bias — maps badness to 1–4, ignores size/recursion. Use with budget splitting for termination. |
| Flat | `"Scoring.flatCtorWeight"` | Every constructor gets weight 1. Ignores everything. |
| Default | `"Scoring.defaultCtorWeight"` | `base=1, rec=numBase*size/numRec`. Ignores score. |

For example, to use size-proportional weights (QuickChick-style):
```lean
set_option specimen.weightFn "Scoring.sizeProportionalCtorWeight"
derive_mutual
  (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)
```

**Defining a custom weight function.** You can define and register your own weight function in your own file — no need to modify Specimen. This is useful when you've derived generators and found the distribution poorly tuned for your application:

```lean
import Specimen

open Scoring Schedules in
-- Custom weight function: heavily favor base cases
def myCtorWeight (ctorName : Name) (outputIndices : List Nat) (deriveSort : DeriveSort)
    (scoreBadness : Float) (isRec : Bool) (size : Nat) (numBase numRec : Nat) : Nat :=
  if isRec then
    if size == 0 then 0
    else max 1 (size / (max 1 numRec * 4))
  else 10

-- Use it for a specific derivation
set_option specimen.weightFn "myCtorWeight" in
derive_mutual
  (fun n => ∃ (xs : List Nat), SortedList n xs)
```

**Targeting specific constructors.** The `ctorName`, `outputIndices`, and `deriveSort` arguments let you override weights for particular constructors or modes while falling back to a default for everything else:

```lean
open Scoring Schedules in
def myTargetedWeight (ctorName : Name) (outputIndices : List Nat) (deriveSort : DeriveSort)
    (scoreBadness : Float) (isRec : Bool) (size : Nat) (numBase numRec : Nat) : Nat :=
  -- Give a specific constructor a constant low weight
  if ctorName == ``MyType.ExpensiveCtor then 1
  -- Boost another constructor
  else if ctorName == ``MyType.PreferredCtor then 8
  -- Fall back to the default balanced strategy for everything else
  else balancedCtorWeight ctorName outputIndices deriveSort scoreBadness isRec size numBase numRec
```

The `set_option ... in` scoping means different derivations in the same file can use different weight functions. After changing the weight function, rederive and recompile your file to produce a generator reflecting the new weights.

**Weight modifiers.** Instead of replacing the entire weight function, you can layer a modifier on top. A `CtorWeightModifier` receives the base weight (already computed by the active weight function) as its first argument and can transform it — multiply, cap, override, or pass through:

```
CtorWeightModifier := Nat → Name → List Nat → DeriveSort → Float → Bool → Nat → Nat → Nat → Nat
                      (baseWeight, ctorName, outputIndices, deriveSort, scoreBadness, isRec, size, numBase, numRec) → finalWeight
```

Example — triple the weight for a preferred constructor, halve an expensive one, leave everything else alone:

```lean
open Scoring Schedules in
def myModifier (baseWeight : Nat) (ctorName : Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Float) (_isRec : Bool)
    (_size : Nat) (_numBase _numRec : Nat) : Nat :=
  if ctorName == ``MyType.PreferredCtor then baseWeight * 3
  else if ctorName == ``MyType.ExpensiveCtor then baseWeight / 2
  else baseWeight

set_option specimen.weightModifier "myModifier" in
derive_mutual
  (fun n => ∃ (xs : List Nat), SortedList n xs)
```

The modifier composes with whatever `specimen.weightFn` is active — you don't need to know or reimplement the base weight logic. This is the lightest-weight way to nudge the distribution for specific constructors.

## Repo overview

**Building & compiling**:
- To compile, run `lake build` from the top-level repository.
- To run snapshot tests, run `lake test`.
- To run linter checks, run `lake lint`. 
  + This invokes the linter provided via the [Batteries](https://github.com/leanprover-community/batteries/tree/main) library.

**Typeclass definitions**:
- [`ArbitrarySizedSuchThat.lean`](./Specimen/ArbitrarySizedSuchThat.lean): The `ArbitrarySuchThat` & `ArbitrarySizedSuchThat` typeclasses for constrained generators, adapted from QuickChick
- [`DecOpt.lean`](./Specimen/DecOpt.lean): The `DecOpt` typeclass for partially decidable propositions, adapted from QuickChick
- [`Enumerators.lean`](./Specimen/Enumerators.lean): The `Enum, EnumSized, EnumSuchThat, EnumSizedSuchThat` typeclasses for constrained & unconstrained enumeration

**Combinators for generators & enumerators**:
- [`GeneratorCombinators.lean`](./Specimen/GeneratorCombinators.lean): Extra combinators for Plausible generators (e.g. analogs of the `sized` and `frequency` combinators from Haskell QuickCheck)
- [`EnumeratorCombinators.lean`](./Specimen/EnumeratorCombinators.lean): Combinators over enumerators 

**Algorithm for deriving constrained producers & checkers** (adapted from the QuickChick papers):
- [`UnificationMonad.lean`](./Specimen/UnificationMonad.lean): The unification monad described in [*Generating Good Generators*](https://dl.acm.org/doi/10.1145/3158133)
- [`DeriveConstrainedProducer.lean`](./Specimen/DeriveConstrainedProducer.lean): Algorithm for deriving constrained generators, including the `derive_mutual` command for multi-spec mutual derivation
- [`MExp.lean`](./Specimen/MExp.lean): An intermediate representation for monadic expressions (`MExp`), used when compiling schedules to Lean code
- [`MakeConstrainedProducerInstance.lean`](./Specimen/MakeConstrainedProducerInstance.lean): Auxiliary functions for creating instances of typeclasses for constrained producers (`ArbitrarySuchThat`, `EnumSuchThat`)
- [`DeriveChecker.lean`](./Specimen/DeriveChecker.lean): Deriver for automatically deriving checkers (instances of the `DecOpt` typeclass)
- [`Schedules.lean`](./Specimen/Schedules.lean): Type definitions for generator schedules
- [`DeriveSchedules.lean`](./Specimen/DeriveSchedules.lean): Algorithm for deriving generator schedules
- [`SearchTree.lean`](./Specimen/SearchTree.lean): Dependency-aware hypothesis ordering via lazy search tree with branch-and-bound pruning

**Schedule scoring & quality analysis**:
- [`Score.lean`](./Specimen/Score.lean): Type-erased score values used by the modular scoring framework
- [`Scoring.lean`](./Specimen/Scoring.lean): Modular scoring framework with pluggable strategies (DefaultScore, WorstLeafScore, DensityScore) for evaluating schedule quality
- [`PatternCoverage.lean`](./Specimen/PatternCoverage.lean): Pattern coverage trie that partitions the input space of an inductive relation, identifies weak spots, and annotates leaves with constructor coverage

**Derivers for unconstrained producers**:
- [`DeriveArbitrary.lean`](./Specimen/DeriveArbitrary.lean): Deriver for unconstrained generators (instances of the `Arbitrary` / `ArbitrarySized` typeclasses), including support for mutually recursive and parameterized types
- [`DeriveEnum.lean`](./Specimen/DeriveEnum.lean): Deriver for unconstrained enumerators 
(instances of the `Enum` / `EnumSized` typeclasses), including nested and mutually recursive types

**Miscellany**:
- [`TSyntaxCombinators.lean`](./Specimen/TSyntaxCombinators.lean): Combinators over `TSyntax` for creating monadic `do`-blocks & other Lean expressions via metaprogramming
- [`LazyList.lean`](./Specimen/LazyList.lean): Implementation of lazy lists (used for enumerators)
- [`LazyRoseTree.lean`](./Specimen/LazyRoseTree.lean): Lazy rose tree data structure
- [`Idents.lean`](./Specimen/Idents.lean): Utilities for dealing with identifiers / producing fresh names 
- [`Utils.lean`](./Specimen/Utils.lean): Other miscellaneous utils
- [`Debug.lean`](./Specimen/Debug.lean): Debug tracing and option flags for Specimen

### Tests
**Overview of test corpus**:
- The [`SpecimenTest`](./SpecimenTest/) subdirectory contains [snapshot tests](https://www.cs.cornell.edu/~asampson/blog/turnt.html) (aka [expect tests](https://blog.janestreet.com/the-joy-of-expect-tests/)) for the derivation commands. 
- Run `lake test` to check that the derived generators in [`SpecimenTest`](./SpecimenTest/) typecheck, and that the code for the derived generators match the expected output.
- Key test directories:
  + [`DeriveArbitrarySuchThat/`](./SpecimenTest/DeriveArbitrarySuchThat/) — constrained generators (BST, balanced tree, STLC, regex, permutations, multi-output, mutual recursion)
  + [`DeriveEnumSuchThat/`](./SpecimenTest/DeriveEnumSuchThat/) — constrained enumerators
  + [`DeriveDecOpt/`](./SpecimenTest/DeriveDecOpt/) — checkers
  + [`DeriveArbitrary/`](./SpecimenTest/DeriveArbitrary/) — unconstrained generators (parameterized types, mutually recursive types, structures)
  + [`DeriveEnum/`](./SpecimenTest/DeriveEnum/) — unconstrained enumerators (nested recursion, mutual recursion)
  + [`CedarExample/`](./SpecimenTest/CedarExample/) — real-world application: well-typed Cedar policy expression generators
  + [`ArithCompiler/`](./SpecimenTest/ArithCompiler/) — end-to-end example: compiler correctness testing

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
