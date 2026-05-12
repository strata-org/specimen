# Specimen 
Specimen complements the Plausible property-based testing library by automatically deriving generators, enumerators, and checkers for inductive relations.

Specimen's design is heavily inspired by [Coq/Rocq's QuickChick](https://github.com/QuickChick/QuickChick) library and the following papers:
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
          
Users can write `deriving Arbitrary` and/or `deriving Enum` after an inductive type definition, e.g..
```lean 
inductive Foo where
  ...
  deriving Arbitrary, Enum
```
Alternatively, users can also write `deriving instance Arbitrary for T1, ..., Tn` (or `deriving instance Enum ...`) as a top-level command to derive `Arbitrary` / `Enum` instances for types `T1, ..., Tn` simultaneously.

Note that Plausible also provides support for deriving `Arbitrary` instances, but the version here supports some parametrized inductive relations; hopefully it will be upstreamed soon.

To sample from a derived unconstrained generator, users can simply call `runArbitrary`, specify the type 
for the desired generated values and provide some `Nat` to act as the generator's size parameter (`10` in the example below):

```lean
#eval runArbitrary (α := Tree) 10
```

Similarly, to return the elements produced form a derived enumerator, users can call `runEnum` like so:
```lean
#eval runEnum (α := Tree) 10
```

If you are defining your own type it needs instances of `Repr`, `Plausible.Shrinkable` and
`Plausible.SampleableExt` (or `Plausible.Arbitrary`):

**2. Deriving constrained generators** (for inductive relations)                
A *constrained* producer only produces values that satisfy a user-specified inductive relation. 

Specimen provides two commands for deriving constrained generators/enumerators. For example, 
suppose you want to derive constrained producers of `Tree`s satisfying some inductive relation `balanced n t` (height-`n` trees that are `balanced`. To do so, the user would write:

```lean
-- `derive_generator` & `derive_enumerator` derive constrained generators/enumerators 
-- for `Tree`s that are balanced at some height `n`,
-- where `balanced n t` is a user-defined inductive relation
derive_generator (fun n => ∃ t, balanced n t) 
derive_enumerator (fun n => ∃ t, balanced n t)
```
To sample from the derived producer, users invoke `runSizedGen` / `runSizedEnum` & specify the right 
instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass (along with some `Nat` to act as the generator size):

```lean
-- For generators:
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balanced 5 t)) 10

-- For enumerators:
-- (we recommend using a smaller `Nat` as the fuel for enumerators to avoid stack overflow)
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balanced 5 t)) 3
```

Some extra details about the grammar of the lambda-abstraction that is passed to `derive_generator` / `derive_enumerator`:

Specifically: in the command
```lean
derive_generator (fun x1 ... xn => ∃ x, P x1 ... x ... xn)
```
`P` must be an inductively defined relation, `x` is the value to be generated (bound by `∃`), and `x1 ... xn` are variable names bound by the `fun`. Following QuickChick, Specimen expects `x1, ..., xn` to be variable names (Specimen does not support literals in the position of the `xi` currently). 

**3. Deriving checkers (partial decision procedures)** (for inductive relations)                                 
A checker for an inductively-defined `Prop` is a `Nat -> Except GenError Bool` function, which 
takes a `Nat` argument as fuel and returns an error if it can't decide whether the `Prop` holds (e.g. it runs out of fuel),
and otherwise returns `ok true` / `ok false` depending on whether the `Prop` holds.

Specimen provides a command elaborator which elaborates the `derive_checker` command:

```lean
-- `derive_checker` derives a checker which determines whether `Tree`s `t` 
-- satisfy the `balanced` inductive relation mentioned above 
derive_checker (fun n t => balanced n t)
```

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
- [`DeriveConstrainedProducer.lean`](./Specimen/DeriveConstrainedProducer.lean): Algorithm for deriving constrained generators using the aforementioned unification algorithm & generator schedules
- [`MExp.lean`](./Specimen/MExp.lean): An intermediate representation for monadic expressions (`MExp`), used when compiling schedules to Lean code
- [`MakeConstrainedProducerInstance.lean`](./Specimen/MakeConstrainedProducerInstance.lean): Auxiliary functions for creating instances of typeclasses for constrained producers (`ArbitrarySuchThat`, `EnumSuchThat`)
- [`DeriveChecker.lean`](./Specimen/DeriveChecker.lean): Deriver for automatically deriving checkers (instances of the `DecOpt` typeclass)
- [`Schedules.lean`](./Specimen/Schedules.lean): Type definitions for generator schedules
- [`DeriveSchedules.lean`](./Specimen/DeriveSchedules.lean): Algorithm for deriving generator schedules
- [`SearchTree.lean`](./Specimen/SearchTree.lean): Search tree and dependency-aware ordering for schedule derivation

**Derivers for unconstrained producers**:
- [`DeriveArbitrary.lean`](./Specimen/DeriveArbitrary.lean): Deriver for unconstrained generators (instances of the `Arbitrary` / `ArbitrarySized` typeclasses)
- [`DeriveEnum.lean`](./Specimen/DeriveEnum.lean): Deriver for unconstrained enumerators 
(instances of the `Enum` / `EnumSized` typeclasses) 

**Miscellany**:
- [`TSyntaxCombinators.lean`](./Specimen/TSyntaxCombinators.lean): Combinators over `TSyntax` for creating monadic `do`-blocks & other Lean expressions via metaprogramming
- [`LazyList.lean`](./Specimen/LazyList.lean): Implementation of lazy lists (used for enumerators)
- [`LazyRoseTree.lean`](./Specimen/LazyRoseTree.lean): Lazy rose tree data structure
- [`Idents.lean`](./Specimen/Idents.lean): Utilities for dealing with identifiers / producing fresh names 
- [`Utils.lean`](./Specimen/Utils.lean): Other miscellaneous utils
- [`Debug.lean`](./Specimen/Debug.lean): Debug tracing and option flags for Specimen

### Tests
**Overview of snapshot test corpus**:
- The [`SpecimenTest`](./SpecimenTest/) subdirectory contains [snapshot tests](https://www.cs.cornell.edu/~asampson/blog/turnt.html) (aka [expect tests](https://blog.janestreet.com/the-joy-of-expect-tests/)) for the `derive_generator` & `derive_arbitrary` command elaborators. 
- Run `lake test` to check that the derived generators in [`SpecimenTest`](./SpecimenTest/) typecheck, and that the code for the derived generators match the expected output.
- See [`DeriveBSTGenerator.lean`](./SpecimenTest/DeriveArbitrarySuchThat/DeriveBSTGenerator.lean) & [`DeriveBalancedTreeGenerator.lean`](./SpecimenTest/DeriveArbitrarySuchThat/DeriveBalancedTreeGenerator.lean) for examples of snapshot tests. Follow the template in these two files to add new snapshot test file, and remember to import the new test file in [`SpecimenTest.lean`](./SpecimenTest.lean) afterwards.

For more documentation refer to the module docstrings in the individual source and test files.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
