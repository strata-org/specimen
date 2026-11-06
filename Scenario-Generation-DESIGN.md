# Scenario Generation: From Random Traces to Systematic Validation

## Problem Statement

Specimen can derive constrained generators from inductive relation specifications.
For trace-based testing (e.g., `SafeBBTrace`), the forward generator produces random
sequences of operations starting from an initial state — but the resulting traces
cluster around easy-to-satisfy paths (lots of `SizeOp`, few interesting interleavings
of `PutOp`/`GetOp`). The backward generator is worse: it degenerates to all-`SizeOp`
traces because it guesses predecessor states rather than computing them.

The fundamental issue: **random generation explores stochastically, when what we need
is systematic coverage of all behaviorally-distinct scenarios.**

## Inspiration: HiFi (High Fidelity Models for Large Scale Stateful Services)

The HiFi paper (Jaber et al., OSDI '26) describes a manual MBT pipeline for S3 that:

1. **Abstracts** API parameters and state into features/categories (equivalence classes
   that trigger the same SuT behavior)
2. **Enumerates** all non-spurious input scenarios (truth assignments over feature
   predicates, filtered by a state invariant inv_Ω)
3. **Plans** a path from the current state to each scenario's required state via an
   API-planner that issues preparatory requests
4. **Concretizes** abstract scenarios into concrete requests
5. **Validates** the SuT's response against the model, organized by error count
   (0-error, 1-error, 2-error campaigns)

Key results: systematic scenario enumeration deterministically covers in 8 requests
what PBT covers stochastically in ~3200. The tool prevents 300+ regressions in S3's
CI/CD pipeline.

## The Opportunity

For an inductive relation like `BBSafeStep`, the entire HiFi pipeline structure is
**already implicit in the specification**:

| HiFi Concept | Lean Inductive Analog |
|---|---|
| Features/categories | Premises of each constructor |
| Scenarios | Distinct premise configurations |
| inv_Ω | Implications derivable from constructor structure |
| API-planner | Goal-directed trace generator |
| Model execution | Relation evaluation via `DecOpt`/enumerator |
| Response validator | Differential testing (relation vs. implementation) |
| Error scenarios | `¬CanStep` / negative constructors |

The vision: **derive the entire systematic testing pipeline from the inductive spec.**

## Architecture (4 Phases)

### Phase 1: Feature & Scenario Extraction

From the constructors of a step relation, identify:
- **Features**: abstract predicates over state (buffer_empty, buffer_full, etc.)
- **State invariant (inv_Ω)**: implications between features that rule out spurious
  combinations (can't be both empty and full; non-empty implies within-capacity)
- **Scenarios**: all satisfying truth assignments to features, partitioned by whether
  the operation succeeds (safe) or fails (error)

For `BBSafeStep`, the features are derived from premise shapes:
- `WithinCapacity (v :: s) c` → "buffer not full" (length < capacity)
- Pattern `v :: s` in GetOp → "buffer non-empty"
- `WithinCapacity s c` in SizeOp → "buffer within capacity" (always true for reachable states)

### Phase 2: Goal-Directed Planning (API-Planner)

Given a target scenario (a set of state predicates that must hold), produce a
trace from the initial state to a state satisfying those predicates.

For BoundedBuffer:
- Target "buffer non-empty": generate one or more PutOps
- Target "buffer full": generate exactly `capacity` PutOps
- Target "buffer empty": either start (already empty) or generate Gets to drain

This is **generation-by-execution**: iteratively pick an action that moves toward
the goal, execute it against the model, repeat until the goal holds.

For simple systems like BB, the planner is deterministic. For complex systems
(many features, indirect dependencies), planning becomes a search problem —
potentially reducible to proof search over the constructors.

### Phase 3: Campaign Organization

Organize scenarios by error count (following HiFi's first-error hypothesis):

- **0-error campaigns**: For each safe constructor, plan to a state where its
  premises hold, then execute the operation and validate.
- **1-error campaigns**: For each error constructor, plan to a state where the
  error's precondition holds (e.g., buffer full → PutOp errors), execute, and
  validate that the error is produced correctly.
- **2-error campaigns**: Validate error precedence when multiple errors are possible.

### Phase 4: Validation Execution

For each scenario in a campaign:
1. Run the planner to reach the target state (executing each step against both
   model and SuT to detect deviations during setup)
2. Concretize the scenario request (pick concrete values from the relevant category)
3. Execute against both model and SuT
4. Compare responses

## Implementation Plan

### Step 1: Manual Prototype (this PR)

Hand-write the complete HiFi pipeline for BoundedBuffer:
- Explicitly define features, scenarios, and inv_Ω
- Implement a goal-directed planner that reaches each scenario's target state
- Organize tests into 0-error and 1-error campaigns
- Demonstrate deterministic coverage vs. the existing random approach

This validates the architecture works in Lean and identifies which parts are
mechanical/automatable.

### Step 2: Scheduler Enhancement — Invertible Functions

Teach Specimen's scheduler that when generating backward, equalities involving
invertible functions (e.g., `s' = List.concat s v` with `s'` known) can be
solved by inversion rather than guess-and-check. This directly fixes the
backward generator quality issue.

### Step 3: Derive Planner

Implement a `derive_planner` metaprogram that, given a trace relation and a
goal predicate, synthesizes a goal-directed generator. The planner analyzes
each constructor's "effect" (how it changes state) and selects constructors
whose effects move toward the goal.

### Step 4: Derive Campaign

Implement `derive_campaign` that:
1. Extracts features from the step relation's premises
2. Derives inv_Ω from constructor structure
3. Enumerates non-spurious scenarios (via all-SAT or enumeration)
4. Synthesizes a planner for each scenario
5. Produces a complete test harness

## Comparison: Random PBT vs. Systematic Scenario Generation

For the BoundedBuffer with capacity 3:

**Random PBT** (current forward generator, 1000 traces of size ≤10):
- Covers PutOp, GetOp, SizeOp in various combinations
- May never hit "buffer exactly full then Put" (error scenario)
- May never hit "buffer exactly full then Get" (interesting safe scenario)
- Coverage depends on luck and trace length

**Systematic** (HiFi-style):
- 0-error scenarios: PutOp-on-non-full, GetOp-on-non-empty, SizeOp (3 scenarios)
- 1-error scenarios: PutOp-on-full, GetOp-on-empty (2 scenarios)
- Total: 5 scenarios, each hit exactly once with a planned trace
- 100% behavioral coverage, deterministic

## Open Questions

1. **Feature granularity**: How fine-grained should extracted features be? HiFi
   uses domain expertise to identify meaningful categories. Can we derive
   "meaningful" automatically from the relation structure?

2. **Planner complexity**: For BB, planning is trivial. For systems with
   non-reversible operations or complex state dependencies, planning may require
   backtracking search. How does this compose with Specimen's existing search
   infrastructure (enumerators, bounded search)?

3. **Generation-by-execution vs. upfront generation**: Specimen currently generates
   entire values upfront. The planner model requires interleaving generation with
   model execution. Can this be expressed as a monadic generator that threads
   state, or does it require a fundamentally different execution model?

4. **Scaling**: HiFi handles 10^25 scenarios for GetObject via campaign budgeting
   and the first-error hypothesis. For Specimen, what's the analog of "time budget"
   when tests run at elaboration time vs. runtime?

5. **Non-determinism**: HiFi's model allows multiple valid responses (set of
   acceptable errors). Specimen's inductive relations are inherently deterministic
   in their logical content. How to express "the SuT may return any of these errors"?
