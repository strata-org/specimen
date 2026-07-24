# Generating Command Sequences with Hard-to-Satisfy Preconditions

*Why Specimen's forward generator can fail to exercise some commands, a fix by
step inlining, and a minimal experiment (the "perfect-square ticket vault").*

## 1. The problem

Specimen derives generators from inductive relations. A very common shape is a
**state-transition specification** — a step relation whose constructors are the
labeled edges of a state machine, plus a trace relation that chains steps:

```
Step  : State → Cmd → Result → State → Prop
Trace : State → List (Cmd × Result) → State → Prop
```

`SpecimenTest/BoundedBuffer/BoundedBufferSpec.lean` (`BBSafeStep` / `SafeBBTrace`)
and `SpecimenTest/KeyValueStoreExample/KeyValueStore.lean` (`EvalApiCall` /
`EvalApiCalls`) are both exactly this shape.

For such a relation, Specimen derives a **forward generator**: from a start state
it walks the machine, at each step picking an enabled edge. The natural
assumption is that this produces valid command sequences covering the whole
machine. **It does not** — when a command has a precondition that isn't cheaply
satisfiable, the forward generator fails to exercise that command *at all*, from
any start. This document is about that failure and how to fix it.

## 2. Why forward generation can fail: un-invertible preconditions

The derived forward generator is a **0-step lookahead** walk: it picks a branch,
solves that branch's premises *locally*, moves to the next state, and repeats. It
never reasons across the step boundary. So if firing a command requires data that
had to be set up by an *earlier* step, and that data cannot be recovered from the
current state, the generator has no way to produce the command — the earlier step
already committed the wrong value.

The trouble arises when a command's precondition is not satisfiable by *reading
the current state*. Contrast two cases:

- **Easy:** KV `Set k v; Get k`. `Get`'s precondition is that `k` is present in
  the store — the generator reads a key that's already there. Mere equality
  against the state; the derived generator handles it.
- **Hard:** a precondition that must be *synthesized*, not read — e.g. "present a
  value `k` whose square equals the stored ticket". The state holds the square;
  the root cannot be read off it, and Specimen (a solver-*synthesizer*, worst
  case generate-and-check) can only guess `k` and test — which for an arbitrary
  committed value ~never hits.

## 3. The fix: inline adjacent steps

Specimen is a **solver-synthesizer**, not a solver, but *within a single
constructor* its scheduler already reorders premises and reuses bound variables
(bind-once, use-many). It just never reasons *across* the recursive step
boundary, where two steps communicate only through the intermediate state value.

That gives a machinery-free fix: **inline `k+1` adjacent steps into a single
constructor.** Inlining moves the step boundary *inside* the scheduler's existing
joint-scheduling window, so the data constraint of a later step and the choices
of an earlier step share one scope. No solver is added.

The mechanism, and its limit: the recursive relation can link two steps only by
routing a value through the intermediate state and reading it back out — which,
backward, requires **inverting the state**, exactly what Specimen cannot do.
Inlining instead lets a value be a **shared variable** across both steps and lets
a linking equation be **computed forward** from a fresh variable. So inlining
helps precisely when the cross-step link is *forward-functional in a fresh
variable*; when it requires inverting a non-injective function, inlining only
relocates the guess-and-check into a bigger constructor.

## 4. The experiment: the perfect-square ticket vault

The *smallest* example that (a) is as simple as BoundedBuffer, (b) has a command
whose precondition is set up by an earlier step, and (c) **cannot** be satisfied
by reading the state.

### The machine (`VaultBaseline.lean`)

A vault is `Option Nat` (empty, or holding one ticket). `sq k := k * k`.

```lean
inductive VStep : Vault → VCmd → VResult → Vault → Prop where
| DoIssue  : ∀ t,   VStep none     (VCmd.Issue t)  VResult.IssueOk  (some t)
| DoRedeem : ∀ t k, t = sq k →
             VStep (some t) (VCmd.Redeem k) VResult.RedeemOk none
```

`Issue t` puts any ticket into an empty vault; `Redeem k` empties a held vault
**only** if the ticket `t = sq k` — you must present the square root `k`.
Nothing at `Issue` forces `t` to be a square; the requirement is imposed later,
by `Redeem`, and the root `k = √t` must be synthesized, not read off the state.

We supply the generator Specimen cannot derive (expected to be picked up wherever
a perfect-square value is needed):

```lean
instance : ArbitrarySizedSuchThat Nat (fun t => ∃ k, t = sq k) where
  arbitrarySizedST size := do
    let k ← Gen.choose Nat 0 size (by omega)
    return sq k
```

### Variants

1. **Baseline** (`VaultBaseline.lean`): forward generator for `VTrace` (0-step
   lookahead) — the generator Specimen derives today.
2. **Fused** (`VaultFused.lean`): `VTrace2` has an `IssueRedeem` constructor that
   inlines `Issue t; Redeem k` with `t = sq k` in one scope (1-step lookahead).
3. **All-combinations** (`VaultUnrolledAll.lean`): the *mechanical* k=2 inlining a
   tool would emit — one constructor **per combination** of `VStep`'s two rules
   (II, IR, RI, RR = 2² = 4), with state constraints inlined as explicit
   premises. The command sequence is not hardcoded; which combination is viable
   is left for the generator to work out.

### Results (1000 sampled traces each)

| Variant          | Structure                              | Traces w/ ≥1 Redeem  |
|------------------|----------------------------------------|----------------------|
| Baseline         | 0-step lookahead (Specimen today)      | **0 / 1000**         |
| Fused            | `Issue; Redeem` inlined, `t = sq k`    | **~320 / 1000**      |
| All-combinations | all 4 step-pairs inlined               | **~200 / 1000**      |

`Gen.run` uses real `IO` randomness, so exact counts fluctuate a few percent
run-to-run; the *invariants* below are what's stable.

Baseline behaves as predicted: 372/1000 traces are non-empty and **every** one
has length exactly 1 (372 `Issue`s, max length 1). It reaches a held vault but
can never take a second step, because the only outgoing edge (`DoRedeem`) needs a
root it cannot produce. The zero is a genuine "never exercises Redeem".

Fused sample traces (each redeem presents the true root): `Issue 9, Redeem 3`;
`Issue 16, Redeem 4`; `Issue 81, Redeem 9`; `Issue 361, Redeem 19`.

### What the experiment establishes

- **Baseline → Fused (0 → ~320):** inlining one step turns a command the forward
  generator *could never fire* into one it fires reliably, **with no solver
  added** — the scheduler binds a fresh `k` and *computes* `t = sq k` forward
  instead of committing `t` early and failing to invert it. The state bookkeeping
  (`Issue` needs empty, `Redeem` resets to empty) is solved by the scheduler from
  ordinary premises; nothing needs pre-solving by hand.
- **All-combinations (~200):** the fully mechanical `b^k` expansion works too,
  and the generator finds the viable step-pair **without being told which**. No
  static pruning happens — `derive_mutual` emits code for all four constructors,
  and the infeasible ones fail *at generation time* and backtrack: II and RR by
  internal unification inconsistency (`sa = some _` ∧ `sa = none`), RI because its
  `s = some (sq k)` contradicts the `none` start (every recursion point is `none`,
  since IR resets to it), leaving only IR. The shortfall from 1000 is just the
  generator choosing the valid empty (`Nil`) trace, not failure.

The mechanism is **variable sharing + premise reordering across the widened
window**, which Specimen already does within a constructor. Two requirements:
(a) inlining must reach *through* the callee relation's premises — inline the
step *rules*, not merely unroll the recursion; a constructor that keeps the two
steps as `VStep` premises reproduces the baseline's 0, because each premise is a
black box; (b) the cross-step link must be forward-functional (§3). The costs are
the `b^k` constructor blow-up and the fact that infeasible combinations are
eliminated only by **runtime** backtracking, not static analysis.

## 5. Generality: a different structure (guarded dereference)

The vault is a *flat command trace* — a `Step`/`Trace` pair. Does inlining help
on a genuinely different structure? `SpecimenTest/AttrGuardExperiment/` is a
second experiment shaped like Cedar's `HasType`: a **single self-recursive typing
relation over an expression tree**, threading a "guard set" state from a
subexpression's output into its parent (Cedar threads a `PathSet` this way in
`TCondTrue`, `THasAttr`, …).

```lean
inductive Expr | lit (n : Nat) | chk (c : Nat) (e : Expr) | drf (k : Nat) (e : Expr)

inductive WT : Guards → Expr → Guards → Prop where   -- Guards := List Nat
| TLit : ∀ g n,        WT g (Expr.lit n) g
| TChk : ∀ g c e g',   WT g e g' → WT g (Expr.chk c e) (c :: g')
| TDrf : ∀ g k e g',   WT g e g' → sq k ∈ g' → WT g (Expr.drf k e) g'
```

`chk c e` records guard code `c`; `drf k e` (a "dereference") is well-typed only
if `sq k` is already among `e`'s output guards. As in the vault, the guard set
stores *squares*, so the root `k` cannot be read back — a forward generator can
only guess `k` and check `sq k ∈ g'`. Two differences from the vault: the state
is threaded through a *tree* (subexpression outputs), not a linear trace, and the
relation is *self-recursive* (one relation, not a pair).

Same three variants, same outcome (1000 samples each):

| Variant          | Structure                                  | Exprs w/ ≥1 `drf`  |
|------------------|--------------------------------------------|--------------------|
| Baseline         | 0-step lookahead (Specimen today)          | **0 / 1000**\*     |
| Fused            | `drf k (chk (sq k) e)` inlined             | **~580 / 1000**    |
| All-combinations | `drf` inlined over each inner rule         | **~480 / 1000**    |

\* Baseline builds real guarded trees — 607/1000 non-trivial, 1344 `chk` nodes,
max size 10 — but essentially never a valid `drf` (one lucky `drf 0`, since
`sq 0 = 0`). A genuine "never derefs", not "never generates".

Fused samples are all well-guarded: `drf 4 (chk 16 …)`, `drf 9 (chk 81 …)`,
`drf 13 (chk 169 …)`. So the mechanism transfers intact to the tree-structured,
self-recursive case.

**One new lesson this example exposes that the vault could not: inlining must
compose *across relations*.** The vault's cross-step link was an *equality*
(`t = sq k`), which the scheduler resolves by unification. Here `drf`'s link is a
*membership* (`sq k ∈ g'`). Inlining `drf` over the inner expression's `WT` rule
alone leaves a residual `sq k ∈ c :: g0` — still a guess-and-check — and the
mechanical all-combinations generator produces **0** derefs, exactly like the
baseline. It only works once we *also* inline the membership via its two
`List.Mem` constructors: the **head** case unifies `sq k = c` (substitute
`c := sq k` — forward-functional, and it recovers precisely the `AttrGuardFused`
pairing), while the **tail** case leaves the harder residual `sq k ∈ g0`. So the
general transformation is not "inline the step relation" but "inline the
constructors of whatever derivable relation a stuck premise calls, recursively" —
a step relation, a typing relation, or an auxiliary like `∈`.

## 6. Paths forward: avoiding the combinatorial blow-up

The all-combinations approach is the mechanical form of the fix, but it emits
`b^k` constructors (KVStore: ~16 commands → ~256 at k=2) and eliminates dead ones
only at **runtime**, after their generator code is synthesized and executed to
failure. Making this scale means moving that elimination to **derivation time**,
via two complementary static analyses over the inlined premises:

- **Cull unsatisfiable combinations.** Detect at derivation time that a
  combination's inlined state premises are contradictory (e.g. `sa = some _` ∧
  `sa = none`) and never emit its generator. This directly removes the
  start-independent dead constructors (II, RR in the experiment), and, given a
  known start state, the start-dependent ones (RI). This is where a state-machine
  view earns its keep: it is exactly the reachability pruning that tells us which
  step sequences are worth generating at all.

  Crucially, this culling is a **theorem-proving** goal we can hand to **Lean
  itself**: a combination is dead iff its premise conjunction entails `False`. A
  pruning pass would, per candidate constructor, assemble the premise conjunction
  and try an escalating tactic (`simp_all` / `omega` / `decide`): proof found →
  drop it; no proof or a countermodel → keep it. This is sound by construction
  (drop only what Lean *proves* can never fire) and degrades gracefully — a
  timed-out or undecidable goal just means "keep it", falling back to runtime
  backtracking. (The disproofs that show these goals are dischargeable, and the
  results of the implemented pass, are reported separately — see `Results.md`.)

- **Classify the surviving cross-step links.** For each combination that is not
  culled, decide whether its linking equation is *forward-functional in a fresh
  variable* (emit an efficient forward generator, as for `t = sq k`) or requires
  *inverting a non-injective function* (as for `sq t = sq k`). In the latter
  case, either skip the combination or consult a user-supplied inverse generator
  — like the `ArbitrarySizedSuchThat Nat (fun t => ∃ k, t = sq k)` instance in
  this experiment, which the forward derivations never needed but an
  inversion-based one would. This avoids emitting generators that could only ever
  fall back to fruitless guess-and-check.

Together these turn the naive `b^k` enumeration into a pruned set of viable,
efficiently-generable step sequences, computed before code generation rather than
discovered by runtime backtracking.

## 7. A design for Specimen

Both experiments are hand-written. The manual constructions suggest a concrete
extension to `derive_mutual`, two composable passes behind option flags.

### Pass A — premise-call inlining (`specimen.inlineDepth`)

Generalize beyond the `Step`/`Trace` shape to the condition both experiments
actually rely on:

> a constructor has a premise that **calls a derivable relation** and **shares a
> variable** with another premise or the conclusion, such that binding it in one
> scope would resolve a link the local scheduler currently defers.

`Trace.Cons` (shares intermediate state `s'`) and `WT.TDrf` (shares guard set
`g'`, and — a level deeper — the membership `sq k ∈ g'`) are both instances.
Inlining substitutes each constructor of the called relation into the caller,
threading the shared variable, and emits one specialized constructor per
combination. Crucially it must **recurse across relations**: after inlining
`WT`'s rules into `drf`, the residual `sq k ∈ c :: g0` is itself a call to a
derivable relation (`List.Mem`) and must be inlined in turn (head → `sq k = c`;
tail → `sq k ∈ g0`). Depth `k` bounds how many levels are unrolled; `k = 1` is
today's behavior.

Specimen already has the raw material: `getScheduleForInductiveRelationConstructor`
(`DeriveConstrainedProducer.lean:443`) telescopes each constructor into
`forAllVars`, `hypotheses`, and `conclusion` as `Expr`s. Inlining is a
transformation of that spec into a list of specs. The main refactor is to make
the per-constructor pipeline consume a *spec* rather than a name it looks up via
`getConstInfoCtor` (line 437), since inlined constructors are synthetic and have
no `ConstInfo`.

### Pass B — cull provably-dead combinations (`specimen.cullDeadCtors`)

Inlining's `b^k` blow-up (Cedar's `HasType`: ~40 rules, some with 3 recursive
premises) makes pruning a prerequisite, not a polish. A combination is dead iff
its inlined premise conjunction entails `False`, which is a **theorem-proving
goal we hand to Lean**: assemble `h₁ → … → hₙ → False` from the spec's
hypotheses and try an escalating tactic (`simp_all` → `omega` → `decide`) under a
heartbeat budget. Proof found → emit no generator for that combination; no proof
or timeout → keep it.

Two properties make this safe:

- **Cull only if never satisfiable, under *any* input state.** We assemble the
  goal from the constructor's own premises and **never** inject the start state.
  So we drop `some _ = none`-style internal contradictions (vault II/RR), but a
  constructor that is merely unreachable *from a particular start* (vault RI,
  which is satisfiable from some `some (sq _)` state) is provably not `False` and
  is kept. This is the intended semantics: never assume anything about the input
  state that might not always hold.
- **Sound by construction, and a pure optimization.** We drop only what Lean
  *proves* dead, so no reachable behavior is lost; and the runtime backtracking
  that prunes these today still exists, so a timeout or undecidable goal is
  harmless — it just falls back to current behavior.

### Composition

The two passes are generate-then-filter over one constructor list: Pass A expands
the original constructors into `b^k` synthetic specs (building the merged premise
lists that culling needs), then Pass B filters that list before scheduling and
codegen. They are independently switchable — culling alone still removes
genuinely-vacuous hand-written constructors; inlining alone reproduces the
runtime-backtracking all-combinations behavior — and they touch disjoint stages,
so neither perturbs the scheduler, MExp, or codegen.

### Suggested next step

Scale the study toward the KV store's genuine multi-step precondition (a
versioned `Get` at version ≥ 1 needs ≥ 2 same-key `Set`s) to (a) confirm a
`k`-window with `k ≥ 2` exercises it where `k = 1` cannot, and (b) stress the
`b^k` blow-up at a realistic command count, where the static pruning above
becomes necessary rather than optional.

## Files

- `SpecimenTest/VaultExperiment/VaultBaseline.lean` — flat trace, 0-lookahead baseline.
- `SpecimenTest/VaultExperiment/VaultFused.lean` — one inlined `Issue; Redeem` step-pair.
- `SpecimenTest/VaultExperiment/VaultUnrolledAll.lean` — mechanical all-combinations `b^k` inlining.
- `SpecimenTest/AttrGuardExperiment/AttrGuardBaseline.lean` — tree-structured self-recursive analog, baseline.
- `SpecimenTest/AttrGuardExperiment/AttrGuardFused.lean` — inlined `drf`/`chk` pair.
- `SpecimenTest/AttrGuardExperiment/AttrGuardUnrolledAll.lean` — all-combinations, inlining across `WT` *and* `∈`.

## Appendix: why not "generate by walking a state machine"?

The natural first instinct for this problem is to read the step relation as a
**state machine** and *plan a path* through it: pick a sequence of edges from the
start state to one where the target command is enabled, then generate along that
path. This appendix records why that framing is the wrong one to build on — the
reasoning that led to the premise-inlining design above.

**The states are symbolic, and the edges carry constraints.** A "node" like the
empty vault or `([], n)` in BoundedBuffer is not one state but a *family* — a
pattern with free variables — and an edge is guarded by a constraint
(`t = sq k`, `WithinCapacity`, `sq k ∈ g'`). So "the state machine" is not a
finite graph you can pathfind over; reaching a target is already
unification-plus-constraint-solving over the relation's constructors. There is no
separate graph object to build: the constructors *are* the transition structure.

**Control and data cannot be separated.** The appealing part of the state-machine
picture is that it looks like *planning* (which edges, in what order — control)
that you could do first, then *solve* the data along the chosen path. But which
control paths are even feasible is determined by the data:

- In the vault, "reach a state where `Redeem` fires" is not a control fact — it
  depends on having *issued a perfect square*, a data constraint on an earlier
  edge.
- In a KV store, a versioned `Get` at version 1 is reachable only after **two
  `Set`s of the same key**; a controller that reasoned over edge labels alone
  would happily propose `Create; Set; Get@v1`, a path with no data realization.

So a control-only planner is unsound: it proposes paths that cannot be
instantiated. Planning and solving have to be **interleaved**, which means the
"plan a path, then fill in data" decomposition buys nothing — the path search and
the constraint solving are the same search.

**Inlining is that interleaved search, in the one place Specimen already does
it.** Rather than build an external planner over a graph that does not really
exist, the design above pulls adjacent edges into a *single constructor*, where
the scheduler already solves control (premise ordering) and data (variable
binding) together. The cross-step data constraint (`t = sq k`) and the earlier
edge's choice (`Issue t`) end up in one scope, so the constraint steers the
choice — exactly the control/data interleaving the state-machine framing wanted,
without inventing a graph or a separate planning phase.

The residue of the state-machine idea that *does* survive is narrow and useful:
the *reachability pruning* of §6 (a dead edge-combination is one whose merged
guards are contradictory) is precisely the "which transitions are worth taking"
question — but computed as a theorem-proving check on inlined premises, not as
graph search. The broader "aim generation at a target" goal is real but separate;
it is discussed in `Steering-notes.md`.
