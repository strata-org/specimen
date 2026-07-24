# Step-Inlining: Implementation Results

*Results for the implemented pieces of the step-inlining design
([Lookahead-experiment.md](./Lookahead-experiment.md)). The design doc argues
what to build and why; this doc records what was built and how it behaves. It
grows one section per landed piece.*

## 1. Culling provably-dead constructors (`specimen.cullDeadCtors`)

Design reference: "Pass B — cull provably-dead combinations" and the "Cull
unsatisfiable combinations" bullet of §6 in the design doc.

### The disproofs are dischargeable

Before wiring anything into the deriver, `VaultCullProof.lean` establishes the
premise: that "this constructor can never fire" is a goal Lean's own automation
closes. For the all-combinations vault relation it states each constructor's
premise block verbatim and proves `premises → False`:

- `II` and `RR` — closed by `simp_all` (contradictory `some _ = none`
  equalities); dead regardless of the input state.
- `RI` — closed by `simp_all` *once a `none` start is assumed*; dead only from
  that start.

It also exhibits **satisfying witnesses** for `IR` and for `RI` from a `some (sq _)`
start — evidence that a sound pass must *keep* those. This is the guardrail: cull
only on a proof of `False`, never on a failure to find a model.

### The implemented pass

`constructorPremisesUnsat` (`Specimen/DeriveConstrainedProducer.lean`) telescopes
a constructor, opens its premises into the local context, and tries
`simp_all` / `omega` / `decide` on a `False` goal under a bounded heartbeat
budget. `compileInductiveSchedule` skips any constructor it proves dead. The pass
is behind `set_option specimen.cullDeadCtors true` (default off).

Key semantics — **cull only if never satisfiable, under *any* input state**: the
goal is assembled from the constructor's own premises, with no assumption about
the start state. So a constructor that is merely unreachable from a particular
start (like `RI`) is *not* culled. Sound by construction, and a pure optimization:
the runtime backtracking that prunes these already exists, so a timeout or
undecidable goal is harmless (keep the constructor).

### Results

- On the hand-written `VaultUnrolledAll` relation, the derivation trace shows
  `[cull] dropping recursive constructor …VT.II` and `…VT.RR` — exactly the two
  internally-contradictory constructors — while `IR` and `RI` are kept. Generation
  still produces valid traces (`VaultCullTest.lean`: ~220 / 1000 Redeem-bearing,
  and the stable invariant *non-empty ⟹ contains-Redeem* holds — 0 non-empty
  traces without a Redeem).
- On the guarded-dereference relation with a deliberately-dead `DeadHead`
  constructor (premises force `0 = 1`), only `DeadHead` is dropped; every
  satisfiable rule is kept (`AttrGuardCullTest.lean`: ~566 / 1000 `drf`-bearing).
- Flag-off is a no-op: BST / STLC / multi-output / Cedar derivations are
  unchanged.

Counts fluctuate a few percent run to run (`Gen.run` uses real `IO` randomness);
the invariants (which constructors are dropped, and non-empty ⟹ target-hit) are
what's stable.

### Files

- `SpecimenTest/VaultExperiment/VaultCullProof.lean` — the by-hand disproofs and
  the keep-these witnesses.
- `SpecimenTest/VaultExperiment/VaultCullTest.lean` — culling on the vault
  all-combinations relation.
- `SpecimenTest/AttrGuardExperiment/AttrGuardCullTest.lean` — culling on the
  guarded-dereference relation (drops a planted dead constructor, keeps the rest).
