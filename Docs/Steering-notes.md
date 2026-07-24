# Notes: Steering Command-Sequence Generation Toward a Target

*Speculative. Separate from [Lookahead-experiment.md](./Lookahead-experiment.md),
which is about generating valid command sequences at all — including commands
with hard-to-satisfy preconditions. These notes assume that problem is solved and
ask a further question.*

## The problem

Given an *adequate* forward generator for a state-transition specification (one
that can produce valid sequences exercising every command, including
precondition-heavy ones), it still produces only *random* valid sequences. A
distinct goal is **steering**: bias generation to reach a *specific, rare target*
— e.g. "a state where the `GetOp` branch is enabled", so we can test that branch,
or a designated destination state.

This is orthogonal to the forward-generation-adequacy problem. Step inlining (the
subject of the companion doc) makes a generator *capable* of hard steps; it does
nothing to *aim* it. A fused generator still walks forward and still produces
random valid sequences.

## Planning vs. generation

A natural decomposition:

- **Planning (control):** decide *which* constructors fire, and in what order —
  the command skeleton from the start to the target.
- **Generation (data):** decide *what values* instantiate the states and command
  arguments along that skeleton.

The tempting design is to treat the specification as an explicit **state machine**
and plan by pathfinding, then solve constraints along the path. Two observations
complicate that:

1. **The states are symbolic.** A "node" like `([], n)` is a *family* of states
   (a pattern with a free variable), and edges carry *constraints*
   (`WithinCapacity`, the equality `s' = concat s v`). "Reaching the target" is
   unification + constraint solving over the relation's constructors — a form of
   narrowing. No separate graph is required; the state machine is a *lens* on that
   search, not an input to it.

2. **Pure control planning is unsound**, because data dependencies determine which
   control paths are feasible. In the KV store, a versioned `Get` (version 1)
   requires two prior `Set`s **of the same key** (`LookupKV.LFoundS` bumps the
   version only when a newer entry for the same key is prepended). A control-only
   planner would propose `Create; Set; Get@v1` — a skeleton with no concrete
   realization. The skeleton cannot be chosen without partly accounting for the
   data.

So planning and solving must be **interleaved, not staged.** What survives as a
clean distinction is *reachability-relevant data* (what guards branch on — must be
tracked during planning) vs. *inert data* (appears in commands but never gates a
transition — can be deferred to cheap unconstrained generation).

## Directions

- **Target-mode / backward derivation.** Combine an adequate forward generator
  with backward/target-mode derivation (`fun s => ∃ t i, Trace i t s`) so a target
  biases which edges are explored. The abstract state machine acts as a heuristic
  that prunes and orders constructor choices, while the actual work is narrowing
  over the constructors.

- **Backtracking over plans (CEGAR).** Any finite state abstraction can propose a
  skeleton with no concrete realization. Treat a skeleton as a *bias with a
  fallback* and backtrack when its accumulated constraints go unsat, refining the
  abstraction on failure.

- **The proven state machine (optional).** A Lean-*defined* transition system with
  a proof of equivalence to the source relation would be a nice artifact for trust
  and visualization, but it is not on the critical path: the generator needs only
  the internal, heuristic version, whose soundness comes from checking the
  relation's guards during generation.

## Relationship to the inlining work

The static analyses proposed for taming the inlining blow-up (culling
unsatisfiable step-combinations, classifying forward-functional vs. inversion
links) are effectively a *local, bounded* form of the planning search described
here. Steering generalizes them: instead of pruning fixed-length step windows, it
searches for a path of arbitrary length toward a chosen target. A good next step
is to see whether the same reachability pruning that culls dead `b^k`
combinations extends naturally into goal-directed path search.
