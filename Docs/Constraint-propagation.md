# Constraint Propagation for Polymorphic Dependencies

## Overview

When `derive_mutual` generates code for a spec involving polymorphic types, the generated definition needs typeclass constraints on its type parameters (e.g. `[Arbitrary α]`, `[DecidableEq α]`). Constraint propagation determines exactly which constraints each spec requires by walking the dependency graph bottom-up.

## Architecture

The system has four layers:

1. **`extractTypeParamRefs`** — structural: which type params does a `ConstructorExpr` reference?
2. **`synthExternalConstraints`** — semantic: for an external dep, what constraints does its instance need?
3. **`computeSpecConstraints`** — per-spec: walk all schedule steps and collect constraints
4. **`propagateConstraints`** — global: orchestrate across all components in topological order

### Why bottom-up?

Specs are organized into SCCs (strongly connected components) in topological order, leaves first. By the time we process a spec, all its non-mutual dependencies already have their constraints computed. This avoids re-derivation and gives us a single-pass algorithm for acyclic deps.

### Why fixed-point for mutual blocks?

In a mutual group, spec A may depend on spec B and vice versa. Neither can be computed first. We initialize all constraints to `∅` and iterate: recompute each spec's constraints using siblings' current sets, until no set changes. This converges because constraints can only grow (we never remove) and the universe of possible constraints is finite.

## Per-Step Constraint Rules

`computeSpecConstraints` matches on each schedule step:

### Unconstrained generation (`Unconstrained _ (NonRec (indName, args)) ps`)

Three cases:
- **Bare type param** (e.g. generating `α` directly): add the own-sort class (`Arbitrary` for generators, `Enum` for enumerators).
- **Compound type referencing type params** (e.g. `List α`): use `synthExternalConstraints` to discover transitive requirements. Generating `List α` requires `Arbitrary (List α)`, whose instance in turn requires `[Arbitrary α]`.
- **No type param involvement**: no constraint needed.

### Checks (`Check (NonRec (indName, args)) _`)

- **Eq/Ne**: special-cased to `DecidableEq`. These are the only relations where we know the constraint statically — equality on a type param always needs decidable equality.
- **Other relations**: three-tier lookup: internal dep map → sibling map (mutual) → synthesis of `DecOpt` on the relation (external). If synthesis fails entirely, conservatively fall back to `{Enum, DecidableEq}` — this only triggers for external deps where we can't determine the actual requirements.

### SuchThat deps (`SuchThat _ (NonRec (indName, args)) ps`)

Same three-tier lookup: internal map → sibling map → synthesis of `ArbitrarySizedSuchThat`/`EnumSizedSuchThat`.

### Recursive and mutual-recursive steps

- **Self-recursive** (`Rec`): no-op. Self-recursion doesn't introduce new constraints — whatever the spec needs is already captured by its non-recursive steps.
- **Mutual-recursive** (`MutRec sibName`): look up the sibling's current constraint set from the fixed-point iteration map.

### No blanket additions

Constraints are collected strictly from what the schedule steps demand. If a generator only generates `List α` unconstrainedly, it gets `[Arbitrary α]` — it does NOT get `DecidableEq` unless some step actually needs it (e.g. an Eq check, or a checker dep that transitively requires it). This avoids polluting generated signatures with unnecessary constraints.

## External Constraint Discovery (`synthExternalConstraints`)

For deps not in the current `derive_mutual` call (already in the environment), we can't inspect their schedules. Instead:

1. Build the fully-applied type expression (e.g. `List α`) with fresh metavariables for non-Sort params and local `Sort`-typed fvars with `[Enum], [Arbitrary], [DecidableEq]` instances available in context.
2. Ask Lean to synthesize the target class (e.g. `Arbitrary (List α)`).
3. On success, inspect the synthesized instance's **declaration type** — walk its forall binders and collect `instImplicit` domains. These are the constraints the instance needs (e.g. `[Arbitrary α]`).
4. Also inspect the **goal type** itself for additional instance-implicit requirements.

This two-pass inspection (declaration + goal) catches constraints from both the instance definition and from the typeclass itself.

### Why provide all three classes in the synthesis context?

When synthesizing `Arbitrary (List α)`, Lean needs `[Arbitrary α]` to be available in context. By providing `Enum`, `Arbitrary`, and `DecidableEq` instances on the fresh type fvars, we ensure synthesis succeeds for any instance that depends on standard classes. The constraints we *read back* from the synthesized instance tell us which subset is actually needed.

### Edge cases

- **Bare type param as indName** (e.g. step says "generate `α`"): short-circuit to returning the own-sort class directly without synthesis.
- **Predicate-form classes** (`ArbitrarySizedSuchThat`, `EnumSizedSuchThat`): the instance type requires building a lambda predicate over output variables, not just a bare application.
- **Synthesis failure**: return empty — the caller decides the fallback (checker defaults or nothing).

## Diagnostics

After propagation, two diagnostic passes run:

1. **Unprovided constraints**: if propagation discovers a class Specimen can't emit (anything other than `Arbitrary`, `Enum`, `DecidableEq`), a warning tells the user what's missing. This catches cases like a custom `[MyHashable α]` that Specimen doesn't know how to add to the generated signature.

2. **Missing concrete instances**: for each schedule step referencing a concrete type (no type params, not being derived in this call), verify the required instance actually exists. If not, warn — e.g. "needs `[Arbitrary MyColor]` but no such instance exists."

## Display

Computed constraints are shown in:
- **Spec labels** in both text output and HTML widget: e.g. `Generator Between{Arbitrary, DecidableEq}[0,2]`
- **Generated code dropdown** in the HTML widget: the actual emitted `def` with instance binders visible
- **logInfo suppression**: per-component log messages are suppressed when `richOutput` is active (the HTML widget shows everything more clearly)
