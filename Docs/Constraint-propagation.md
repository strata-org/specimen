# Constraint Propagation for Polymorphic Dependencies

## Problem

When Specimen generates code for a polymorphic type like `GenList (α : Type) [Arbitrary α]`, the generated definition needs the right typeclass constraints on its type parameters. Previously, constraints were hardcoded per derive-sort: generators always got `[Arbitrary α]`, checkers always got `[Enum α, DecidableEq α]`. This caused two issues:

1. **Unused constraints** — generators got `[Enum α]` they didn't need.
2. **Missing constraints** — when a generator depends on a checker that shares a type parameter, the generator's hardcoded constraints didn't include `[Enum α]`, so the checker call inside the generated code couldn't find its required instance.

## Solution: Bottom-Up Propagation

Replace hardcoded constraints with a bottom-up walk through the dependency graph that discovers what each spec *actually needs*.

### Algorithm

After SCC decomposition gives us components in topological order (leaves first):

```
for each component (in topo order):
  if singleton:
    compute constraints by walking schedule steps
  if mutual block:
    fixed-point iteration until stable
```

For each schedule step, we determine constraints by its kind:

| Step kind | Source of constraints |
|-----------|---------------------|
| `Unconstrained (NonRec)` on a bare type param | Own-sort class directly (`Arbitrary`/`Enum`) |
| `Unconstrained (NonRec)` on a compound type | Synthesis: try `synth [TC (Foo α)]`, read back what the instance needs |
| `Check (NonRec)` for Eq/Ne | `DecidableEq` (special case) |
| `Check (NonRec)` for other relations | Look up internal dep map, else synthesize `DecOpt` |
| `SuchThat (NonRec)` | Look up internal dep map, else synthesize `ArbitrarySizedSuchThat`/`EnumSizedSuchThat` |
| `Rec` / self-recursive | No-op (constraints come from non-recursive steps) |
| `MutRec` sibling | Look up sibling's current constraints (fixed-point) |

### Key design decisions

**Why synthesis for external deps?** When a spec depends on something already in the environment (e.g. `Arbitrary (List α)`), we can't inspect its schedule—it doesn't have one. Instead we ask Lean's instance synthesis to find it, then read the instance's type signature to discover what constraints it required (e.g. `[Arbitrary α]`).

**Why fixed-point for mutual blocks?** In a mutual group, spec A might depend on spec B and vice versa. We iterate: compute A's constraints assuming B's current set, then B's assuming A's, repeat until neither changes.

**Why always add `DecidableEq`?** If a spec has *any* constraints, it almost certainly needs `DecidableEq` too (for equality checks in the generated code). Rather than track this precisely, we add it unconditionally when the constraint set is non-empty.

### Implementation

Core functions in `Specimen/DeriveConstrainedProducer.lean`:

- `extractTypeParamRefs` — walks a `ConstructorExpr` tree to find which type params it references
- `synthExternalConstraints` — synthesizes an instance for a compound type and reads back the constraints from the instance's type signature
- `computeSpecConstraints` — computes constraints for a single spec given the already-computed dep map
- `propagateConstraints` — orchestrates the full bottom-up walk across all components

The computed constraints are passed to `compileInductiveSchedule` which emits them as instance binders in the generated definition.

## Diagnostics

The propagation system also enables two kinds of warnings:

1. **Unprovided constraints** — when propagation discovers a requirement Specimen can't emit (e.g. `[MyHashable α]`), it warns the user. Specimen can only provide `Arbitrary`, `Enum`, and `DecidableEq`.

2. **Missing concrete instances** — when a schedule step references a concrete type (no type params) but the required instance doesn't exist (e.g. `[Arbitrary MyColor]` with no such instance defined), Specimen warns rather than silently generating broken code.

## Display

Computed constraints appear in two places:
- **Spec labels** in the HTML widget and text output: `Generator Between{Arbitrary, DecidableEq}[0,2]`
- **Generated code dropdown** in the HTML widget: shows the actual emitted definition with its instance binders
