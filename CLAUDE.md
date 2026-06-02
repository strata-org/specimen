# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Is

Specimen is a Lean 4 library for property-based testing that automatically derives constrained generators, enumerators, and checkers for inductive relations. It extends the [Plausible](https://github.com/leanprover-community/plausible) library and is heavily inspired by Coq's QuickChick.

## Build Commands

```bash
lake build          # Build the library
lake test           # Run snapshot tests (checks derived generators typecheck and match expected output)
lake lint           # Run Batteries linter
```

There is no single-test runner — `lake test` compiles and checks all files imported in `SpecimenTest.lean`.

## Toolchain

- Lean 4 (v4.30.0-rc1, specified in `lean-toolchain`)
- Build system: Lake (configured via `lakefile.toml`)
- Dependencies: `batteries` and `plausible` (both from leanprover-community, tracking `main`)

## Architecture

The library has three main derivation pipelines, all operating on inductively defined types/relations:

1. **Constrained producers** (`derive_generator`, `derive_enumerator`): Generate values satisfying an inductive relation. The pipeline is:
   - `DeriveSchedules.lean` — derives generator schedules (orderings of constructor arguments) using the search tree in `SearchTree.lean`
   - `DeriveConstrainedProducer.lean` — compiles schedules into monadic expressions using the unification algorithm from `UnificationMonad.lean`
   - `MExp.lean` — intermediate representation for monadic expressions
   - `MakeConstrainedProducerInstance.lean` — creates the final typeclass instance

2. **Unconstrained producers** (`deriving Arbitrary`, `deriving Enum`):
   - `DeriveArbitrary.lean` — derives `ArbitraryFueled` instances
   - `DeriveEnum.lean` — derives `EnumSized` instances

3. **Checkers** (`derive_checker`):
   - `DeriveChecker.lean` — derives `DecOpt` instances (partial decision procedures)

Key support modules:
- `GeneratorCombinators.lean` / `EnumeratorCombinators.lean` — monadic combinators (sized, frequency, etc.)
- `TSyntaxCombinators.lean` — helpers for constructing Lean syntax via metaprogramming
- `LazyList.lean` — lazy list implementation used by enumerators

## Testing

Tests are snapshot/expect tests in `SpecimenTest/`. They use `#guard_msgs` to assert that derived code matches expected output. The test structure mirrors the derivation commands:

- `DeriveArbitrarySuchThat/` — constrained generator tests
- `DeriveEnumSuchThat/` — constrained enumerator tests
- `DeriveDecOpt/` — checker tests
- `DeriveArbitrary/` — unconstrained generator tests
- `DeriveEnum/` — unconstrained enumerator tests
- `CommonDefinitions/` — shared inductive types used across tests

To add a new test: create a `.lean` file following the pattern in existing tests (e.g., `DeriveBSTGenerator.lean`), then import it in `SpecimenTest.lean`.

## Key Typeclasses

| Command | Typeclass Created |
|---------|------------------|
| `derive_generator` | `ArbitrarySizedSuchThat` |
| `derive_enumerator` | `EnumSizedSuchThat` |
| `derive_checker` | `DecOpt` |
| `deriving Arbitrary` | `ArbitraryFueled` (from Plausible) |
| `deriving Enum` | `EnumSized` |
