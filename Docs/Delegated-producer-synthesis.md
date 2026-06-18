# Delegated Producer Synthesis for Constrained Generators

## Motivation

Specimen derives constrained producers (`ArbitrarySizedSuchThat` /
`EnumSizedSuchThat`) for inductive relations by *scheduling* the hypotheses of
each constructor: deciding, for each hypothesis, which arguments are inputs and
which are outputs, and in what order to satisfy them. When a hypothesis can be
run in a producer mode — generate the outputs given the inputs — Specimen emits
a call to a sub-producer. When it cannot, Specimen falls back to
**generate-and-check**: generate the value blindly with `Arbitrary.arbitrary`
and discharge the hypothesis with a `DecOpt` check, backtracking on failure.

Generate-and-check is the source of almost all the quality problems with derived
generators. The experiments under `SpecimenTest/Experiments/` show this
concretely:

- `FuncEqExp.lean` — `isSmall n = true`, `lookupNat l k = some v`: derive, but
  by generating the unknown and checking. Random values rarely satisfy a sparse
  constraint.
- `FreshExp.lean` — `x ∉ l`: compiles to `DecOpt.negOpt (DecOpt.decOpt (x ∈ l))`;
  the caller must *guess* an `x` and test it.
- `TransformedRecExp.lean` — a recursive call on a transformed output
  (`Good (wrap inner)`, the shape of `varOpen 0 x e` in a binder rule): derives,
  but produced only the trivial value because random bodies almost never pass the
  check.

For a relation like Strata's `HasType` (Hindley–Milner typing over a
locally-nameless term language), a generate-and-check generator would almost
never produce a non-trivial well-typed term within a reasonable size/fuel
budget. See `SpecimenTest/LExprGen.lean` for the full case study.

The key observation: **for many of these constraints, an efficient
mode-directed producer exists — Specimen just has no way to obtain it.** A
freshness constraint `x ∉ freeVars e` does not want to be *checked*; it wants a
producer that takes `e`, computes its free variables, and *returns* a variable
not among them. The scheduler is already willing to ask for such a producer
(see below); the gap is supplying one.

## What already works today

Two facts from the experiments anchor the design.

### The scheduler already emits mode-directed producer steps

In `DefWrappedExp.lean`, the hypothesis `freshDef x l` (with `l` an input and
`x` an existential output) compiles to:

```lean
@ArbitrarySizedSuchThat.arbitrarySizedST _ (fun (x_1 : Nat) => @freshDef x_1 l_1) _ initSize
```

That is exactly a mode-directed call: "produce `x` such that `freshDef x l`,
given `l`." It fails only because no instance of that class exists, and the
failure surfaces late — during Lean's typeclass synthesis after code generation.

### Supplying the producer makes it work end-to-end

In `ModeDirectedExp.lean`, providing

```lean
instance (l : List Nat) : ArbitrarySizedSuchThat Nat (fun x => freshDef x l) where
  arbitrarySizedST _ := return (l.foldr Nat.max 0) + 1
```

makes the *same* derivation compile and produce a fresh variable directly
(`max + 1`), every time, with zero backtracking. The code generator needs no
changes — only the instance needs to exist.

So the codegen path is already correct. The missing piece is an **oracle**, used
during scheduling, that answers "can this constraint be produced in this mode?"
and, when the answer is yes, makes a producer available.

## Design

### 1. A layered availability oracle

When the scheduler considers a hypothesis `P a₁ … aₙ` with a given input/output
mode, it classifies the constraint into one of three states:

- **known** — a producer is already available. Sources, in order:
  1. **Typeclass synthesis**: an `ArbitrarySizedSuchThat`/`EnumSizedSuchThat`
     instance for the mode resolves. (This formalizes, at schedule time, what
     codegen does implicitly today.)
  2. **Self-derivation**: if `P` is itself an inductive relation of the right
     shape, attempt to derive a producer on the fly (extends the existing
     `autoDeriveDeps` machinery to the scheduling decision).
  Known constraints carry a *real* cost estimate.

- **plausibly-producible** — no producer exists yet, but a static feasibility
  heuristic judges that one *could* be built. Examples of cheap static filters:
  - the output is a computable function of the inputs (e.g. `x ∉ f(inputs)`,
    `x = g(inputs)`);
  - `P` is an inductive relation whose constructor conclusions admit the
    requested mode.
  Plausibly-producible constraints carry an *assumed* cost, **penalized** so
  they never out-rank a known-cheap alternative (see §3).

- **infeasible** — fails the static filter. Only generate-and-check is
  available (today's behaviour), with its corresponding (high) cost.

### 2. Optimistic scheduling with an obligation list

The scheduler proceeds *as if* every plausibly-producible constraint will be
satisfied by some future producer. As it commits to a schedule, it records an
**obligation**: the predicate, the mode (which args are in/out), the argument
types, and the definition body. Each schedule therefore depends on a set of
obligations.

This keeps the symbolic core **deterministic and reproducible**: no external
call happens during elaboration. The nondeterministic step is deferred and
isolated.

### 3. Cost model and bounded optimism

Unbounded optimism is unsound for the *scorer*: a hypothetical "free" producer
would always beat a real instance plus a check. So:

- plausibly-producible modes are scored with a penalty relative to known modes;
- the static feasibility heuristic is the knob trading LLM load against
  coverage. Too strict defeats delegation; too loose floods the backend with
  impossible asks and causes thrashing (see §5).

Freshness (`x ∉ freeVars e`) passes the "output computable from inputs" filter
cleanly. A constraint like Strata's `AnnotCompat` (`∃ σ, AliasEquiv … (subst σ ann) xty`)
is exactly the uncertain case where the static filter cannot decide and the
judgment should be **delegated**.

### 4. Batch construction as a persisted cache

After synthesis, the accumulated obligation list is handed to an external
backend (e.g. an LLM agent) that **constructs or declines** each producer. The
crucial framing:

> The backend does not generate producers *on the fly* during elaboration, nor
> merely *at the end of one run*. It **populates a cache that typeclass
> resolution reads.**

Concretely, the backend emits the producers as ordinary checked-in Lean
instances (a generated file). Consequences:

- **Normal builds never call the backend.** They resolve the committed instances
  via typeclass synthesis — step 1.1 of the oracle. The backend is only on the
  *cache-miss* path: when the obligation set changes.
- **Reproducible builds.** The nondeterministic step is out of the elaboration
  loop entirely.
- **Reviewable.** Generated producers appear in a PR and can be read, tested, and
  edited by hand. Hand-written and LLM-written producers live in the same
  namespace and are indistinguishable to the scheduler.
- **Parallelizable.** Independent obligations are constructed concurrently.
- **Latency is off the build's critical path.**

This reframing makes the "on-the-fly vs. batch" question largely dissolve: step 1.1
(resolution) is identical either way; the only question is *when the cache is
filled*, and the answer is "lazily, on cache miss, out of band."

### 5. Monotone re-search on failure

If the backend declines obligation *N* (judges it infeasible, or fails to
construct it), the schedules that depended on *N* are no longer valid. Rather
than a fine-grained truth-maintenance system, exploit the fact that Specimen's
scheduler already enumerates schedules lazily with branch-and-bound:

- maintain a monotonically growing **infeasible set** of `(predicate, mode)`
  pairs;
- on a decline, add the failed pair to the set and **re-run the lazy search**
  with those modes demoted to infeasible;
- repeat until a schedule's obligations are all satisfiable (or all are
  infeasible).

Two guarantees fall out:

- **Termination.** The infeasible set only grows and the schedule space is
  finite.
- **Fallback floor = today's Specimen.** If every delegated mode is ultimately
  declined, the search lands on a generate-and-check schedule using existing
  instances. *The feature can never do worse than the status quo.* This is worth
  stating as an explicit contract.

### 6. Soundness gate

A producer is only sound if every value it emits satisfies `P`. The backend
cannot be trusted blindly. The contract is **construct-or-decline** (constructing
the instance *is* the feasibility claim — there is no separate "could you?"
query), plus a verification step before Specimen emits code that relies on it.
Options, in increasing strength:

- **Runtime `DecOpt` guard** (when `P` is decidable): wrap produced values in a
  `DecOpt` check of `P`; backtrack if it ever fails. The producer still
  generates good values directly — the check is a *safety net* that catches an
  unsound producer at test time, not the generation strategy, so it does not
  reintroduce generate-and-check blowup.
- **Property test at derivation time**: sample N values, assert `P` holds.
- **Proof obligation**: require the producer to ship a proof that all outputs
  satisfy `P` (a verified `ArbitrarySuchThat`). Strongest, highest authoring
  cost.

The choice can be per-backend or per-obligation.

## End-to-end shape

```
static feasibility heuristic + cost model
        │
        ▼
typeclass resolution / self-derivation   ──(known)──┐
        │ (no instance)                              │
        ▼                                            │
optimistic obligation for plausibly-producible mode  │
        │                                            │
        ▼                                            │
batch backend: construct-or-decline ─decline─► add to infeasible set ─► re-search (§5)
        │ construct                                  │
        ▼                                            │
persist as checked-in instance (cache) ──────────────┘
        │
        ▼
runtime soundness guard
```

## Recommended first prototype

**Freshness** (`freshDef(+e, −x)`): compute the free variables of the input and
return one not among them. It exercises the entire loop — a mode-directed need,
a producer that is a computable function of the inputs, and an easy soundness
check — while staying self-contained. And because `ModeDirectedExp.lean` already
shows the codegen end works once the instance exists, a prototype only has to
fill in the "produce the instance" box; it need not touch code generation.

The next target would be **context-lookup** (`tvar`-style `find? Γ x = some ty`,
mode `(+Γ, −x, −ty)`): enumerate bindings from the context instead of guessing
keys. This is the single biggest quality win for typing-relation generators, but
it requires the oracle to reason about container membership, so it is best
attempted after the freshness loop is solid.

## Evidence

All claims above are reproducible from the files under
`SpecimenTest/Experiments/`:

| File | Demonstrates |
|---|---|
| `FuncEqExp.lean` | function-call / container equalities derive via generate-and-check |
| `FreshExp.lean` | `∉` and Bool side-conditions are the same mechanism (`negOpt`/`decOpt`) |
| `TransformedRecExp.lean` | transformed recursive args derive but generate poorly |
| `HardCasesExp.lean` | non-syntax-directed rules terminate (size/fuel); disjunctions become one check |
| `ExistsHypExp.lean` | a `def`-wrapped existential predicate is opaque → missing instance |
| `DefWrappedExp.lean` | `def`-wrapped predicate is opaque, but the scheduler still emits a mode-directed call |
| `ModeDirectedExp.lean` | supplying that producer makes the same derivation compile and generate well |
