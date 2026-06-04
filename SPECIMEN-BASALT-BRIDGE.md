# Bridging Specimen and Basalt via `BacktrackGen`

This document describes a plan to make [Specimen](https://github.com/strata-org/specimen)-derived generators compatible with [Basalt](https://code.amazon.com/packages/Basalt)'s correctness proof infrastructure.

A glossary of terms appears at the end, for quick reference.

## 1. Status Quo and Goal

### The three frameworks

**Plausible** is a property-based testing library for Lean. Its `Gen` monad is a stack of monad transformers:
```
abbrev Gen (α : Type u) := RandT (ReaderT (ULift Nat) (Except GenError)) α
```
It provides randomness, a size parameter, and exception-based failure. The `plausible` tactic finds `Testable` instances (which bottom out at `Arbitrary` instances) via typeclass synthesis and executes them.

**Specimen** derives generators for values satisfying inductive relations, built on top of Plausible. It emits `Plausible.Gen α` terms that use `throw`/`tryCatch` for backtracking: when a branch can't satisfy constraints, it throws a `GenError`, and the `backtrack` combinator catches it and retries another branch. Key typeclasses:
- `ArbitrarySizedSuchThat α P` — a sized generator (`Nat → Gen α`) for values satisfying `P`
- `ArbitrarySuchThat α P` — the unsized wrapper (via `Gen.sized`)

**Basalt** defines a `Gen` typeclass abstracting the capabilities needed by a generator:
```lean
class Gen (g : Type u → Type v) where
  instInhabited : ∀ α, Inhabited (g α)
  instMonad : Monad g
  instRandomChoice : RandomChoice g
  instCCPO : ∀ α, CCPO (g α)
  instMonoBind : MonoBind g
```
Basalt provides multiple instances: `SetGen.Set` (for soundness/completeness proofs), `SPMF` (for termination/distribution proofs), `SPMF.Cost` (for cost bounds), and `Plausible.Gen` (for execution, via `Basalt/PlausibleGen.lean`). A generator written polymorphically as `[Gen G] → G α` can be proved correct at `SetGen`/`SPMF` and executed at `Plausible.Gen`.

Basalt also defines correctness classes for individual generator terms:
- `IsSoundAndComplete (g : SPMF α) (P : α → Prop)` — the generator's support equals `{a | P a}`
- `IsAlmostSurelyTerminating (g : SPMF α)` — the generator's mass sums to 1
- `IsCostBounded (g : SPMF.Cost α) (c : α → Nat)` — the generator makes at most `c a` choices to produce `a`
- `LawfulGenerator (g : ∀ {G} [Gen G], G α) (P) (c)` — combines all three

### Current dependency structure

```
┌──────────┐         ┌──────────┐
│ Plausible│◄────────│ Specimen │
└────┬─────┘         └──────────┘
     │
     ▼
┌──────────┐
│  Basalt  │
└──────────┘
```

Specimen and Basalt are currently unrelated — Specimen-derived generators cannot be reasoned about using Basalt's correctness classes.

### Target dependency structure

```
┌──────────┐
│ Plausible│
└────┬─────┘
     │
     ▼
┌──────────┐         ┌──────────┐
│  Basalt  │◄────────│ Specimen │
└──────────┘         └──────────┘
```

Specimen will depend on Basalt for `Gen`, `BacktrackGen`, and `backtrack`. The `plausible` tactic will still work: Specimen emits `ArbitrarySizedSuchThat` instances (as it does today) whose body calls `BacktrackGen.toPlausibleGen` to produce the `Plausible.Gen α` that Plausible's machinery expects.

### The goal

We want Specimen-derived generators to be **polymorphic over Basalt's `Gen` class** so they can be:
- **Executed** via `Plausible.Gen` (as today)
- **Proved sound/complete** at `SetGen.Set`

### Non-goals

The following are explicitly **not** addressed by this plan:

- **Changing user-facing syntax.** The `derive_generator (fun τ => ∃ e, HasType e τ)` command syntax remains unchanged. The difference is purely in what code gets emitted.
- **Enumerators.** Specimen's deterministic enumerators (`EnumSizedSuchThat`) are a separate concern from random generators and are not addressed here. (But we should address them similarly.)
- **Almost-sure termination proofs for derived generators.** Phase 2 proves soundness/completeness only. Termination and cost bounds for Specimen-derived generators are future work (they would require `partial_fixpoint`-based emission).

### Example

We will use the following small typed language throughout this document to illustrate the changes. This example is designed to exercise all three mechanisms: backtracking (multiple constructors per type, some of which fail), checkers (the `isPos` constructor has a decidable guard `n ≠ 0`), and cross-generator composition (`WellFormed` calls `HasType`).

```lean
inductive Ty | nat | bool

inductive Expr
  | lit (n : Nat)
  | isPos (n : Nat)
  | add (l r : Expr)

inductive HasType : Expr → Ty → Prop
  | lit (n) : HasType (.lit n) .nat
  | isPos (n) : n ≠ 0 → HasType (.isPos n) .bool
  | add (l r) : HasType l .nat → HasType r .nat → HasType (.add l r) .nat

inductive Prog
  | expr (e : Expr)
  | both (e1 e2 : Expr)

inductive WellFormed : Prog → Prop
  | expr (e τ) : HasType e τ → WellFormed (.expr e)
  | both (e1 e2 τ) : HasType e1 τ → HasType e2 τ → WellFormed (.both e1 e2)
```

To get generators, a user invokes Specimen (this syntax will not change):

```lean
derive_generator (fun τ => ∃ e, HasType e τ)
derive_generator (fun _ => ∃ p, WellFormed p)
```

### What Specimen emits today

For the `HasType` relation, Specimen produces:

```lean
instance : ArbitrarySizedSuchThat Expr (fun e => HasType e τ) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (τ : Ty) : Plausible.Gen Expr :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, match τ with
            | Ty.nat => do
              let n ← Arbitrary.arbitrary
              return Expr.lit n
            | _ => MonadExcept.throw Gen.genericFailure),
           (1, match τ with
            | Ty.bool => do
              let n ← Arbitrary.arbitrary
              match @DecOpt.decOpt (¬(n = 0)) _ initSize with
              | Except.ok true => return Expr.isPos n
              | _ => MonadExcept.throw Gen.genericFailure
            | _ => MonadExcept.throw Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1, match τ with
            | Ty.nat => do
              let n ← Arbitrary.arbitrary
              return Expr.lit n
            | _ => MonadExcept.throw Gen.genericFailure),
           (1, match τ with
            | Ty.bool => do
              let n ← Arbitrary.arbitrary
              match @DecOpt.decOpt (¬(n = 0)) _ initSize with
              | Except.ok true => return Expr.isPos n
              | _ => MonadExcept.throw Gen.genericFailure
            | _ => MonadExcept.throw Gen.genericFailure),
           (Nat.succ size', match τ with
            | Ty.nat => do
              let l ← aux_arb initSize size' Ty.nat
              let r ← aux_arb initSize size' Ty.nat
              return Expr.add l r
            | _ => MonadExcept.throw Gen.genericFailure)]
    fun size => aux_arb size size τ
```

For `WellFormed`, Specimen produces a generator that calls the `HasType` generator **via typeclass resolution** (`ArbitrarySizedSuchThat.arbitrarySizedST`):

```lean
instance : ArbitrarySizedSuchThat Prog (fun p => WellFormed p) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : Plausible.Gen Prog :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, do let τ ← Arbitrary.arbitrary
                  let e ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
                  return Prog.expr e),
           (1, do let τ ← Arbitrary.arbitrary
                  let e1 ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
                  let e2 ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
                  return Prog.both e1 e2)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1, do let τ ← Arbitrary.arbitrary
                  let e ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
                  return Prog.expr e),
           (1, do let τ ← Arbitrary.arbitrary
                  let e1 ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
                  let e2 ← @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun e => HasType e τ) _ initSize
                  return Prog.both e1 e2)]
    fun size => aux_arb size size
```

These generators work for execution but cannot be proved correct. To bridge them to Basalt, we need to solve four problems:

**Problem 1: Backtracking.** The generators use Plausible's `throw`/`tryCatch` for backtracking. Basalt's `Gen` class has no exception mechanism — only `choose`, `bind`, `pure`, and ⊥ (`default`). We need a backtracking mechanism that works across all Basalt interpretations. (Addressed in Section 2.)

**Problem 2: Sub-generator resolution.** The generators call sub-generators via Plausible-specific typeclasses (`Arbitrary`, `ArbitrarySizedSuchThat`). These typeclasses wrap `Plausible.Gen` and cannot be used polymorphically over `G`. We need a Basalt-compatible typeclass for sub-generator lookup. (Addressed in Section 3.)

**Problem 3: Checkers.** In more complex examples, Specimen invokes `DecOpt.decOpt` within generators to check hypotheses that involve only fixed (input) variables. `DecOpt.decOpt` returns `Except GenError Bool` — a Plausible-specific type. Checkers must also be made polymorphic over `G`. (Addressed in Section 4. In our running example, the `isPos` constructor triggers this: after generating `n`, Specimen checks `n ≠ 0` via `DecOpt`.)

**Problem 4: Unconstrained generators.** Specimen's `derive Arbitrary` emits generators using Plausible-specific `Gen.frequency` / `Gen.oneOfWithDefault` and `Arbitrary.arbitrary`. These must also become Basalt-polymorphic so they can serve as provably-correct `GenFor` instances for sub-generator resolution in constrained generators. (Addressed in Section 6.)

## 2. Solving Problem 1: `BacktrackGen`

We introduce a newtype that wraps `G (Option α)` to represent generators that may fail locally:

```lean
/-- A backtracking generator: wraps G (Option α) where none = local failure, some = success.
    Defined as a structure (not a type alias) so it can have its own Monad instance,
    enabling do-notation within backtracking generators. -/
structure BacktrackGen (G : Type → Type) (α : Type) where
  run : G (Option α)
```

The `Option` layer is *inside* the generator monad `G`, meaning failure is a **value** that the generator successfully produces (as opposed to ⊥/`default`, which represents divergence). This lets other generators observe and react to failure — enabling retry.

`BacktrackGen` is a `structure` (newtype) rather than a type alias so that it can have its own `Monad` instance. This allows `do`-notation within backtracking generators to bind `BacktrackGen G` values directly, threading `Option` automatically:

```lean
instance [Gen G] : Monad (BacktrackGen G) where
  pure a := ⟨pure (some a)⟩
  bind x f := ⟨do
    match ← x.run with
    | some a => (f a).run
    | none => pure none⟩
```

### The `backtrack` combinator

```lean
/-- Weighted backtracking: randomly pick a branch, try it, retry remaining on failure.
    Uses fuel (initially gs.length) for structural termination. -/
def backtrack [Gen G] (gs : List (Nat × (Unit → BacktrackGen G α))) : BacktrackGen G α :=
  ⟨go gs.length gs⟩
where
  go : Nat → List (Nat × (Unit → BacktrackGen G α)) → G (Option α)
  | _, [] => pure none
  | 0, _ => pure none
  | fuel + 1, gs@(_ :: _) => do
    let idx ← RandomChoice.choose 0 (gs.length - 1) (by omega)
    let i := idx.down
    if hi : i < gs.length then
      let (_, g) := gs[i]
      match ← (g ()).run with
      | some a => pure (some a)
      | none => go fuel (gs.eraseIdx i)
    else
      pure none
```

This has identical operational semantics to Specimen's current `backtrack`: pick a branch randomly, run it, and if it returns `none` (failure), remove it from the pool and retry with decremented fuel. Termination is structural on the `fuel : Nat` parameter (which starts at `gs.length`, bounding retries to at most one attempt per branch).

The key proof lemma for this combinator is `backtrack_mem_iff`, which states that `some a ∈ support ((backtrack gs).run)` iff there exists some branch `i` such that `some a ∈ support ((gs[i].2 ()).run)`. This reduces reasoning about backtracking to reasoning about individual branches, hiding the retry logic entirely.

### The `frequency` combinator

For **non-backtracking** generators (like unconstrained `Arbitrary` derivations that use `Gen.frequency`), we provide a simpler combinator that picks by weight but does *not* retry on failure:

```lean
/-- Weighted random selection without retry. For non-backtracking generators. -/
def frequency [Gen G] (default : G α) (gs : List (Nat × (Unit → G α))) : G α :=
  match gs with
  | [] => default
  | [(_, g)] => g ()
  | gs => do
    let idx ← RandomChoice.choose 0 (gs.length - 1) (by omega)
    let (_, g) := gs[idx.down]!
    g ()
```

This is the Basalt-polymorphic replacement for `Plausible.Gen.frequency` / `Gen.oneOfWithDefault`.

### The `liftGen` and `fail` helpers

```lean
/-- Lift a non-failing G α into BacktrackGen G α. -/
def BacktrackGen.liftGen [Gen G] (g : G α) : BacktrackGen G α :=
  ⟨do let a ← g; pure (some a)⟩

/-- Signal local failure (backtrack). -/
def BacktrackGen.fail [Gen G] : BacktrackGen G α :=
  ⟨pure none⟩
```

### Boundary: unwrapping `BacktrackGen` to `Gen`

At the outermost level — where a generator must produce a value for Plausible's testing machinery — we collapse the `Option`:

```lean
def BacktrackGen.toGen [Gen G] [Inhabited α] (g : BacktrackGen G α) : G α := do
  match ← g.run with
  | some a => pure a
  | none => pure default  -- ⊥ (divergence)

def BacktrackGen.toPlausibleGen (g : BacktrackGen Plausible.Gen α) : Plausible.Gen α := do
  match ← g.run with
  | some a => pure a
  | none => throw (.genError "backtracking exhausted")
```

### Why a structure (newtype)?

`BacktrackGen` is defined as a `structure` wrapping `G (Option α)` rather than a type alias for two reasons:

1. **Disambiguation.** Without the newtype, `G (Option α)` is ambiguous — it could be a generator that legitimately produces `Option` values (where `none` is a valid output) or a backtracking generator where `none` signals failure. `BacktrackGen` makes the intent explicit at the type level.

2. **Own Monad instance.** As a `structure`, `BacktrackGen G` gets its own `Monad` instance that threads `Option` automatically. This means `pure x` wraps in `some`, and `bind` short-circuits on `none`. Without this, code inside backtracking branches would need to manually construct `pure (some x)` and pattern-match on `Option` at every bind — making the generated code verbose and error-prone.

### Interpretations across Basalt instances

| Instance | `BacktrackGen G α` is... | `none` means... | `some a` means... |
|---|---|---|---|
| `SetGen.Set` | `Set (Option α)` | failure is reachable | `a` is reachable |
| `SPMF` | `SPMF (Option α)` | mass on failure | mass on producing `a` |
| `SPMF.Cost` | `SPMF (Option α × Nat)` | failure with cost `n` | producing `a` with cost `n` |
| `Plausible.Gen` | `Plausible.Gen (Option α)` | generation failed | generation succeeded |

Note: `SPMF.Cost` tracks the number of `choose` calls. In `backtrack`, each retry costs one `choose` (to select the next branch) plus whatever choices that branch made. The cost of backtracking falls out automatically from existing `IsBounded_bind` and `IsBounded_choose` theorems — no new cost infrastructure is needed.

## 3. Solving Problem 2: Sub-generator Resolution

Today, Specimen resolves sub-generators via Plausible's `Arbitrary` typeclass (for unconstrained types like `Nat`) and `ArbitrarySizedSuchThat` (for constrained types like well-typed expressions). But `Arbitrary` wraps `Plausible.Gen α` specifically — it cannot be used inside a polymorphic `G`.

We need a Basalt-compatible typeclass mechanism that:

1. Works at all Basalt interpretations (`SetGen.Set`, `SPMF`, `Plausible.Gen`)
2. Scales to large developments with many types
3. Supports modular correctness proofs about composite generators

### Design: `GenFor` and `BacktrackGenFor`

The key distinction we want to express in the typeclass setup is **backtracking vs non-backtracking** behavior — whether the generator can fail locally. Both kinds target a property `P` characterizing their output.

```lean
/-- A non-backtracking generator for type α whose outputs satisfy P.
    Always succeeds (returns G α, not BacktrackGen G α).
    For a truly unconstrained generator, P = fun _ => True.
    Analogous to Plausible's Arbitrary, but polymorphic over Gen G. -/
class GenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], G α

/-- A backtracking generator for type α whose successful outputs satisfy P.
    May fail (returns BacktrackGen G α = G (Option α)).
    Takes a Nat fuel parameter for structural termination.
    Analogous to Specimen's ArbitrarySizedSuchThat, but polymorphic over Gen G. -/
class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G α
```

The naming reflects the role: "find me a generator **for** `α` satisfying `P`." The calling convention:
- `GenFor` → always succeeds, caller uses `BacktrackGen.liftGen` to enter `BacktrackGen`
- `BacktrackGenFor` → may fail, caller binds directly in `BacktrackGen` (failure propagates via `bind`)

The `P` parameter characterizes what the generator produces:

| Class | Example | Property `P` |
|---|---|---|
| `GenFor Nat (fun _ => True)` | Generates any `Nat`, always succeeds | `True` |
| `GenFor (Tree Nat) (Tree.isBST 0 10)` | `Tree.genBST 0 10`, always succeeds | `isBST 0 10` |
| `BacktrackGenFor Expr (HasType · τ)` | Specimen-derived, may fail on some branches | `HasType · τ` |

### Lawful versions: `LawfulGenFor` and `LawfulBacktrackGenFor`

The issue with instances of these typeclasses is that we do not know if they are correct, i.e., whether they are _lawful_. This complicates proving lawfulness of a generator that happens to use a sub generator. For our example, the generator for well-formed statements invokes the generator for well-formed expressions via typeclass resolution. To prove that the well-formed statements generator is correct, we need to know/assume that the one for well-formed expressions is correct, too.

To this end, we introduce two additional typeclasses:

```lean
/-- A lawful non-backtracking generator: proves that outputs satisfy P.
    Provides only soundness & completeness — weaker than Basalt's LawfulGenerator
    which also requires almost-sure termination and cost bounds. -/
class LawfulGenFor (α : Type) (P : α → Prop) extends GenFor α P where
  sound_and_complete : SetGen.IsSoundAndComplete (gen (G := SetGen.Set)) P

/-- A lawful backtracking generator: proves that successful outputs satisfy a size-indexed
    bounded predicate at SetGen.Set. The Bounded predicate refines P with size/range
    constraints imposed by the implementation (e.g., bounded leaf values, bounded depth). -/
class LawfulBacktrackGenFor (α : Type) (P : α → Prop) (Bounded : Nat → α → Prop)
    extends BacktrackGenFor α P where
  sound : ∀ size a,
    some a ∈ SetGen.support ((gen (G := SetGen.Set) size).run) → Bounded size a
  complete : ∀ size a,
    Bounded size a → some a ∈ SetGen.support ((gen (G := SetGen.Set) size).run)
```

Instances of these typeclasses are sure to be sound and complete, i.e., lawful (to a minimal degree). Thus users of them can rely on that lawfulness when proving lawfulness locally.

**Why `Bounded` is separate from `P`.** The property `P` (e.g., `HasType e τ`) is the *semantic* specification the user cares about — it's what appears in `derive_generator (fun τ => ∃ e, HasType e τ)`. But a fuel-based generator cannot produce *all* values satisfying `P` at every size — it only produces values within its size budget and sub-generator ranges. The `Bounded` predicate (e.g., `HasTypeBounded τ`) captures these implementation constraints: `Bounded size a` implies `P a` but additionally requires bounded depth and bounded leaf values.

This two-parameter design is a direct consequence of using explicit fuel for termination (see "Fuel vs size vs `partial_fixpoint`" in Section 7). If generators were defined via `partial_fixpoint` instead — where the generator's support at the fixpoint covers all values satisfying `P` — then `Bounded` would be unnecessary and the class could use a simple `iff` with `P`. The `Bounded` parameter is essentially the price of fuel-based termination; eliminating it is a benefit of moving to `partial_fixpoint` in the future.

**Relationship to Basalt's `LawfulGenerator`:** Basalt defines `LawfulGenerator` as a property of a *specific generator term* — it says "this particular generator `g` is sound, complete, terminating, and cost-bounded." Our `LawfulGenFor` and `LawfulBacktrackGenFor` serve a different purpose: they are *typeclasses for resolution* — they say "there exists a generator for this type/property findable by typeclass synthesis, and it is sound and complete." They intentionally omit cost and termination requirements for simplicity; in the future, these could be strengthened to require `LawfulGenerator` of the underlying term, at which point the system would provide full lawfulness guarantees.

### Standard `GenFor` instances

For standard types (`Nat`, `Bool`, `List`, etc.), we provide `GenFor` instances using existing Basalt-polymorphic generators:

```lean
instance : GenFor Nat (fun _ => True) where
  gen := Nat.arbitrary  -- Basalt's polymorphic Nat generator

instance : GenFor Bool (fun _ => True) where
  gen := Bool.arbitrary
```

These are the generators that Specimen-derived code will resolve via typeclass synthesis. They must be Basalt-polymorphic (not Plausible-specific) so they work at all interpretations. If needed, a `GenFor` instance can bridge *down* to Plausible's `Arbitrary` for compatibility with the `plausible` tactic:

```lean
instance [GenFor α (fun _ => True)] : Arbitrary α where
  arbitrary := GenFor.gen  -- specializes at G := Plausible.Gen
```

## 4. Solving Problem 3: Checkers (`DecOpt`)

### The problem

Today's `DecOpt` typeclass returns a Plausible-specific type:

```lean
class DecOpt (P : Prop) where
  decOpt : Nat → Except GenError Bool
```

It returns `ok true` (P holds), `ok false` (P doesn't hold), or `error` (can't decide — out of fuel). Inside a generator, the result is pattern-matched: `ok true` continues, anything else causes backtracking via `throw`.

Since the emitted generator following our proposal is polymorphic over `G`, it cannot call a function like `DecOpt.decOpt` that returns `Except GenError Bool`. The checker must also be polymorphic over `G`.

### Design: `DecOpt` as `BacktrackGen G Bool`

We redefine `DecOpt` to return `BacktrackGen G Bool`:

```lean
class DecOpt (P : Prop) where
  decOpt : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G Bool
```

The three-valued semantics map cleanly to `G (Option Bool)`:
- `some true` → P holds
- `some false` → P doesn't hold
- `none` → can't decide (out of fuel) → causes backtracking

This fits naturally into the `BacktrackGen` framework: when the checker returns `none`, the calling generator treats it as local failure and backtracks to another branch — exactly today's behavior. The running example demonstrates this: in the `isPos` branch, `DecOpt.decOpt (P := ¬(n = 0))` is called after `n` is generated; if it returns `false`, the branch fails and `backtrack` retries another branch.

### Interpretations

| Instance | `DecOpt.decOpt P fuel` is... | `none` means... | `some true/false` means... |
|---|---|---|---|
| `SetGen.Set` | `Set (Option Bool)` | checking may fail | P is/isn't decidable as true |
| `SPMF` | `SPMF (Option Bool)` | mass on undecided | mass on decided |
| `Plausible.Gen` | `Plausible.Gen (Option Bool)` | checker ran out of fuel | checker decided |

### Bridge from `Decidable`

Any `Decidable` instance gives a `DecOpt` trivially (it never fails):

```lean
instance [Decidable P] : DecOpt P where
  decOpt _ := pure (decide P)
```

## 5. The Generated Code (Running Example)

Applying `BacktrackGen` (Section 2), `GenFor` / `BacktrackGenFor` (Section 3), and `DecOpt` (Section 4) to the example, the generated code becomes:

```lean
def genHasType [Gen G] [GenFor Nat (fun _ => True)]
    (initSize : Nat) (τ : Ty) : (size : Nat) → BacktrackGen G Expr
  | 0 => backtrack [
      (1, fun () => match τ with
        | .nat => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            pure (Expr.lit n)
        | _ => BacktrackGen.fail),
      (1, fun () => match τ with
        | .bool => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            match ← DecOpt.decOpt (P := ¬(n = 0)) initSize with
            | true => pure (Expr.isPos n)
            | false => BacktrackGen.fail
        | _ => BacktrackGen.fail)]
  | size + 1 => backtrack [
      (1, fun () => match τ with
        | .nat => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            pure (Expr.lit n)
        | _ => BacktrackGen.fail),
      (1, fun () => match τ with
        | .bool => do
            let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
            match ← DecOpt.decOpt (P := ¬(n = 0)) initSize with
            | true => pure (Expr.isPos n)
            | false => BacktrackGen.fail
        | _ => BacktrackGen.fail),
      (size + 1, fun () => match τ with
        | .nat => do
            let l ← genHasType initSize .nat size
            let r ← genHasType initSize .nat size
            pure (Expr.add l r)
        | _ => BacktrackGen.fail)]

instance [GenFor Nat (fun _ => True)]
    : ∀ τ, BacktrackGenFor Expr (fun e => HasType e τ) :=
  fun τ => ⟨fun {_} [_] size => genHasType size τ size⟩
```

And `genWellFormed` calls the `HasType` generator via `BacktrackGenFor` typeclass resolution — the runtime value `τ` is captured in the predicate lambda, just as today's code captures it in `(fun e => HasType e τ)`:

```lean
def genWellFormed [Gen G] [GenFor Nat (fun _ => True)] [GenFor Ty (fun _ => True)]
    [∀ τ, BacktrackGenFor Expr (fun e => HasType e τ)]
    (initSize : Nat) : (size : Nat) → BacktrackGen G Prog
  | 0 => backtrack [
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.expr e)),
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e1 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        let e2 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.both e1 e2))]
  | size + 1 => backtrack [
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.expr e)),
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e1 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        let e2 ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
        pure (Prog.both e1 e2))]
```

### Key transformations from the code Specimen generates today

- `MonadExcept.throw Gen.genericFailure` → `BacktrackGen.fail`
- `return value` → `pure value` (the `BacktrackGen` Monad wraps in `some` automatically)
- `Arbitrary.arbitrary` → `BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G α)`
- `ArbitrarySizedSuchThat.arbitrarySizedST (fun e => P e) initSize` → `BacktrackGenFor.gen (P := fun e => P e) initSize`
- `match @DecOpt.decOpt P _ fuel with | Except.ok true => ... | _ => throw` → `match ← DecOpt.decOpt (P := P) fuel with | true => ... | false => BacktrackGen.fail`
- Return type: `Plausible.Gen α` → `BacktrackGen G α`
- Function is now polymorphic over `[Gen G]`
- Recursive calls compose directly in the `BacktrackGen` monad (failure propagates via `bind`)

The `let rec aux_arb` inner function is eliminated — `initSize` and `τ` are explicit parameters with structural recursion on `size`. However, the double-initialization pattern remains: at the Plausible call site, the same value is used for both `initSize` and `size` (matching today's `fun size => aux_arb size size τ`). The `initSize` variable (passed when calling sub-generators like `BacktrackGenFor.gen ... initSize`) gives sub-generators their full budget without decrementing.

### Executing via Plausible

```lean
instance : ArbitrarySizedSuchThat Expr (HasType · τ) where
  arbitrarySizedST size := BacktrackGen.toPlausibleGen (genHasType size τ size)

instance : ArbitrarySuchThat Expr (HasType · τ) where
  arbitraryST := Gen.sized (fun n => BacktrackGen.toPlausibleGen (genHasType n τ n))

instance : ArbitrarySizedSuchThat Prog WellFormed where
  arbitrarySizedST size := BacktrackGen.toPlausibleGen (genWellFormed size size)
```

The `plausible` tactic finds these instances via the existing `ArbitrarySizedSuchThat → ArbitrarySuchThat → Arbitrary` chain and executes them normally.

## 6. Solving Problem 4: Unconstrained Generators (`derive Arbitrary`)

### The problem

Specimen derives unconstrained generators for algebraic data types via `derive Arbitrary`. These generators use `Gen.frequency` / `Gen.oneOfWithDefault` and `Arbitrary.arbitrary` — all Plausible-specific combinators. Like the constrained generators, they cannot be used polymorphically over Basalt's `Gen` class and cannot be proved correct at `SetGen.Set`.

Unlike constrained generators, unconstrained generators never backtrack — they always succeed. This makes the migration simpler: no `BacktrackGen` wrapper is needed, just the `frequency` combinator and `GenFor` for sub-field resolution.

### What Specimen emits today

For a type like:

```lean
inductive Tree (α : Type) where
  | leaf
  | node (left : Tree α) (val : α) (right : Tree α)
  deriving Arbitrary
```

Specimen currently emits:

```lean
instance [Arbitrary α] : ArbitraryFueled (Tree α) where
  arbitraryFueled :=
    let rec aux_arb (fuel : Nat) : Plausible.Gen (Tree α) :=
      match fuel with
      | Nat.zero => Gen.oneOfWithDefault (pure Tree.leaf) [pure Tree.leaf]
      | fuel' + 1 => Gen.frequency (pure Tree.leaf)
          [(1, pure Tree.leaf),
           (fuel' + 1, do
              let left ← aux_arb fuel'
              let val ← Arbitrary.arbitrary
              let right ← aux_arb fuel'
              return Tree.node left val right)]
    fun fuel => aux_arb fuel
```

### Design: Basalt-polymorphic unconstrained generators

The migrated version emits a Basalt-polymorphic generator and a `GenFor` instance:

```lean
def Tree.gen [Gen G] [GenFor α (fun _ => True)] : (fuel : Nat) → G (Tree α)
  | 0 => frequency (pure Tree.leaf) [
      (1, fun () => pure Tree.leaf)]
  | fuel + 1 => frequency (pure Tree.leaf) [
      (1, fun () => pure Tree.leaf),
      (fuel + 1, fun () => do
        let left ← Tree.gen fuel
        let val ← GenFor.gen (P := fun _ => True)
        let right ← Tree.gen fuel
        pure (Tree.node left val right))]

instance [GenFor α (fun _ => True)] : GenFor (Tree α) (fun _ => True) where
  gen := Gen.sized Tree.gen  -- or a fixed default fuel
```

### Key transformations

| Today | After migration |
|---|---|
| `Gen.oneOfWithDefault default [gs]` / `Gen.frequency default [(w, g), ...]` | `frequency default [(w, fun () => g), ...]` |
| `Arbitrary.arbitrary` | `GenFor.gen (P := fun _ => True)` |
| Recursive calls: `aux_arb fuel'` | `Tree.gen fuel` |
| Return type: `Plausible.Gen α` | `G α` (polymorphic over `[Gen G]`) |
| Instance: `ArbitraryFueled` | `GenFor α (fun _ => True)` |

No `BacktrackGen` wrapper is needed — unconstrained generators always succeed.

### Executing via Plausible

The bridge instance from Section 3 provides backward compatibility:

```lean
instance [GenFor α (fun _ => True)] : Arbitrary α where
  arbitrary := GenFor.gen  -- specializes at G := Plausible.Gen
```

This ensures `deriving Arbitrary` continues to work with the `plausible` tactic.

## 7. Design Notes

### Calling patterns summary

The emitted code uses different calling conventions depending on the sub-generator kind:

- **Non-backtracking leaf types** (via `GenFor`): Always succeeds, lifted into `BacktrackGen`:
  ```lean
  let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
  ```

- **Backtracking constrained sub-generator** (via `BacktrackGenFor`): May fail, resolved by typeclass. Runtime parameters are captured in the predicate lambda. Because we are inside a `BacktrackGen` `do`-block, failure propagates automatically via `bind`:
  ```lean
  let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
  ```

- **Self-recursive call**: Direct, with decremented size:
  ```lean
  let l ← genHasType initSize .nat size
  ```

- **Hand-written non-backtracking constrained generator** (e.g., Basalt's `Tree.genBST`): Returns `G α`, registered as a `GenFor`:
  ```lean
  instance : GenFor (Tree Nat) (Tree.isBST 0 10) where
    gen := Tree.genBST 0 10
  ```

### Why typeclass resolution is safe here

A natural concern: typeclass resolution is opaque, so how can a proof about `genHasType` know which `GenFor Nat (fun _ => True)` instance was resolved?

The answer is that we maintain the invariant: **every `GenFor` instance in the system is eventually upgraded to a `LawfulGenFor` instance** (and likewise for `BacktrackGenFor` / `LawfulBacktrackGenFor`). Once this invariant holds, it doesn't matter which instance resolution picks — any instance it finds is provably sound and complete. The opacity of resolution is harmless because all candidates satisfy the same contract.

This invariant is enforced by the two-step roadmap (see Section 8):
1. First, Specimen emits generators with `GenFor` / `BacktrackGenFor` constraints (for execution only).
2. Then, Specimen is upgraded to also emit `LawfulGenFor` / `LawfulBacktrackGenFor` instances with synthesized proofs, ensuring every derived generator is lawful.

### Instance diamond with `LawfulBacktrackGenFor`

A practical issue arises from `LawfulBacktrackGenFor` extending `BacktrackGenFor`: when both a standalone `BacktrackGenFor` instance and a `LawfulBacktrackGenFor` instance exist for the same type/predicate, typeclass synthesis may resolve `BacktrackGenFor.gen` to the standalone instance inside a generator body, while `LawfulBacktrackGenFor.sound`/`.complete` expect the inherited instance. Even though both produce the same generator, Lean treats them as distinct terms, causing type mismatches in proofs.

**Solution:** Generators that need lawfulness proofs must explicitly route through the lawful instance:

```lean
def genWellFormed' [Gen G] [GenFor Nat (fun _ => True)] [GenFor Ty (fun _ => True)]
    [inst : ∀ τ, LawfulBacktrackGenFor Expr (fun e => HasType e τ) (HasTypeBounded τ)]
    (initSize : Nat) : (size : Nat) → BacktrackGen G Prog
  | 0 => backtrack [
      (1, fun () => do
        let τ ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Ty)
        let e ← @BacktrackGenFor.gen _ _ ((inst τ).toBacktrackGenFor) _ _ initSize
        pure (Prog.expr e)),
      ...]
```

**Implication for Specimen's code emission:** When emitting generators that will carry proofs (Phase 2), Specimen must either:
- Emit `@BacktrackGenFor.gen` with explicit instance selection via the lawful instance's `.toBacktrackGenFor` field, or
- Ensure that the `LawfulBacktrackGenFor` instance is the *only* `BacktrackGenFor` instance registered for that type/predicate (i.e., don't register a separate standalone instance once the lawful one exists), or
- Use instance priority to ensure the lawful instance wins synthesis

### Mutual recursion

Specimen supports mutually recursive inductive relations. For mutually recursive generators, the emitted code uses Lean's `mutual ... end` block with direct name calls between the co-defined generators (not typeclass resolution). After the mutual block, each generator is registered as a `BacktrackGenFor` instance. This is the same pattern Specimen uses today — mutual generators call each other by name, and only *external* callers go through typeclass resolution.

### The `initSize` parameter

The generated code takes both `initSize` and `size` as parameters:
- `size` is structurally decremented at each recursive call, ensuring termination.
- `initSize` is the original fuel value, passed unchanged to sub-generators via `BacktrackGenFor.gen ... initSize`.

This means sub-generators always get a full budget. When `genWellFormed` at `size=3` calls `BacktrackGenFor.gen (P := fun e => HasType e τ) initSize`, the `HasType` generator receives the original budget (e.g., 5) rather than the remaining budget (3). This matches today's behavior where `aux_arb initSize size' Ty.nat` passes `initSize` to nested `ArbitrarySizedSuchThat.arbitrarySizedST` calls.

### Fuel vs size vs `partial_fixpoint`

The `size`/`fuel` parameter in generated code currently serves two distinct purposes that are worth disentangling:

1. **Termination witness.** Lean requires structural recursion (or `partial_fixpoint`) for every recursive definition to be accepted. The `size : Nat` parameter with pattern-matching on `0` vs `size + 1` provides a structural termination argument.

2. **Size control.** In property-based testing, generators need a knob that controls the size of generated values — smaller sizes for initial exploration, larger sizes to stress-test. Plausible's `Gen.sized` provides this via a `ReaderT (ULift Nat)` layer.

These two roles happen to coincide in today's Specimen output (the fuel *is* the size), but they are conceptually independent:

- **For constrained generators (`BacktrackGenFor`):** Both roles are essential. The fuel ensures termination, and it also bounds the depth of generated derivation trees, providing natural size control. The `initSize`/`size` split already separates them partially: `size` is the termination witness (structurally decremented), while `initSize` controls sub-generator budgets.

- **For unconstrained generators (`GenFor`):** The fuel is used *only* for termination and size control — there is no backtracking, no failure. In Basalt, `partial_fixpoint` could eliminate the need for an explicit termination witness entirely, since it provides a well-founded recursion principle for generators with `⊥` as the default. However, the fuel still serves a useful role as a **size parameter**: without it, a recursive generator like `Tree.gen` has no way to bias toward smaller trees at lower sizes.

The practical upshot for this plan:

- **Phase 1 preserves explicit fuel for both constrained and unconstrained generators.** This is the simplest path — it matches today's behavior, requires no `partial_fixpoint` infrastructure, and gives users familiar size control.

- **A future optimization** (noted in Section 9) could emit `partial_fixpoint`-based generators that take an optional size hint rather than mandatory fuel. For unconstrained generators, this would look like:
  ```lean
  def Tree.gen [Gen G] [GenFor α (fun _ => True)] : G (Tree α) :=
    partial_fixpoint fun self => frequency (pure Tree.leaf) [
      (1, fun () => pure Tree.leaf),
      (???, fun () => do  -- weight would need to come from somewhere
        let left ← self
        let val ← GenFor.gen (P := fun _ => True)
        let right ← self
        pure (Tree.node left val right))]
  ```
  The open question here is how to express size-dependent weights (today's `(fuel + 1, ...)` pattern) without an explicit fuel parameter. One option is a separate size monad layer; another is to use Basalt's cost infrastructure to bound expected depth. This is deferred as a research question.

### Performance considerations

`BacktrackGen` adds an `Option` wrapper at every bind within backtracking branches. For deeply nested generators this means more allocations and pattern-matches compared to today's exception-based approach. Benchmarking (see `SpecimenTest/BridgeBenchmark.lean`) shows:

**Benchmark results** (bridge/legacy ratio, lower = bridge is faster):

| Scenario | Ratio | Notes |
|---|---|---|
| Recursive generator (5-ary `nary` constructor, sizes 2–4) | 97–101% | Dominant cost is recursion; `Option` overhead invisible |
| Backtracking on guards (`isPos`, DecOpt check) | 100–105% | Within noise |
| Stress test: 5 branches × 5 `liftGen`s, 4 always fail | **118%** | Worst case: cheap branches that fail frequently |
| Same stress test with batched `liftGen`s | **106%** | Batching cuts overhead by ~2/3 |

The 18% worst-case overhead arises when branches consist almost entirely of `liftGen` calls (no recursive sub-generator calls) and multiple branches are tried per iteration (due to frequent failure and retry), amplifying the per-`liftGen` `Option` wrap/unwrap cost across many executed branches. In realistic generators (like Cedar's `HasType` with 23 constructors and recursive sub-generators), branch bodies are dominated by recursive calls — the `Option` overhead is amortized to < 3%.

**IR verification:** The Lean 4 compiler erases the `BacktrackGen` newtype (no `.mk`/`.run` in compiled IR), and `@[specialize]` eliminates the `[Gen G]` dictionary when instantiated at `Plausible.Gen` (producing `spec_0._redArg` variants).

#### Optimization: batching consecutive `liftGen` calls

When Specimen emits code where multiple unconstrained field generations appear consecutively (before any backtracking operation), they can be batched into a single `liftGen`:

```lean
-- Before (3 Option wraps + 3 Option checks):
let a ← BacktrackGen.liftGen (GenFor.gen : G Nat)
let b ← BacktrackGen.liftGen (GenFor.gen : G Nat)
let c ← BacktrackGen.liftGen (GenFor.gen : G Nat)

-- After (1 Option wrap + 1 Option check):
let (a, b, c) ← BacktrackGen.liftGen (do
  let a ← (GenFor.gen : G Nat)
  let b ← (GenFor.gen : G Nat)
  let c ← (GenFor.gen : G Nat)
  pure (a, b, c))
```

The inner `do` block runs in `G` directly (no `Option` overhead). This is purely a code-emission optimization in Specimen — the generated code's semantics are unchanged. The batching boundary is any operation that can fail: a `BacktrackGenFor.gen` call, a `DecOpt` check, or `BacktrackGen.fail`.

#### Optimization: `liftBind` for interleaved non-backtracking operations

When a `liftGen` is followed by a backtracking continuation (not another `liftGen`), batching doesn't apply. For this case, a fused combinator eliminates the intermediate `Option`:

```lean
/-- Fused liftGen + bind: runs a non-failing G α and passes the result directly
    to a backtracking continuation, without wrapping in some and immediately unwrapping. -/
@[inline] def BacktrackGen.liftBind [Gen G] (g : G α) (f : α → BacktrackGen G β) : BacktrackGen G β :=
  ⟨do let a ← g; (f a).run⟩
```

This handles patterns like:
```lean
-- Without liftBind: wraps n in some, then bind unwraps it
let n ← BacktrackGen.liftGen (GenFor.gen : G Nat)
let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize  -- may fail

-- With liftBind: no intermediate Option
BacktrackGen.liftBind (GenFor.gen : G Nat) (fun n => do
  let e ← BacktrackGenFor.gen (P := fun e => HasType e τ) initSize
  ...)
```

In practice, Specimen's emission order places all unconstrained generations before constrained sub-generator calls, so **batching handles the common case**. `liftBind` covers the remaining interleaved cases (e.g., generating a type `τ`, calling a sub-generator parameterized by `τ`, then generating another unconstrained field). Both optimizations are purely in Specimen's code emission — they require no changes to the `BacktrackGen` API or Basalt infrastructure.

Neither optimization affects provability: `liftBind g f` has the same denotation as `bind (liftGen g) f` at all Basalt interpretations (the `some` wrap/unwrap is semantically invisible). The proof lemma is trivial:
```lean
theorem liftBind_eq_bind_liftGen [Gen G] (g : G α) (f : α → BacktrackGen G β) :
    liftBind g f = bind (liftGen g) f
```

### Proving correctness (at `SetGen.Set`)

Soundness and completeness proofs for the running example have been carried out manually as a POC. The proof structure is as follows.

**The key lemma** is `backtrack_mem_iff`, which characterizes membership in `backtrack`'s support:

```lean
theorem backtrack_mem_iff (gs : List (Nat × (Unit → BacktrackGen SetGen.Set α))) (a : α) :
    some a ∈ SetGen.support ((backtrack gs).run) ↔
    ∃ i : Fin gs.length, some a ∈ SetGen.support ((gs[i].2 ()).run) := ...
```

This reduces reasoning about `backtrack` to reasoning about individual branches — the random selection and retry logic is abstracted away.

**The predicate.** Because `GenFor Nat (fun _ => True)` generates naturals in a bounded range (0–100 in the example), the generator's support does not cover *all* well-typed expressions — only those whose leaf values fall within range and whose depth fits the size budget. The proven predicate is:

```lean
def HasTypeBounded (τ : Ty) (size : Nat) (e : Expr) : Prop :=
  HasType e τ ∧ exprBounded size e
```

where `exprBounded size e` requires leaf naturals ≤ 100 and `add`-nesting ≤ `size`.

**Soundness** proceeds by induction on `size`, applying `backtrack_mem_iff` to decompose into branches, then case-splitting on `τ` within each branch. For the `isPos` branch, the `DecOpt` check (`decide (n ≠ 0)`) produces a `Bool` that is matched — only the `true` case reaches `pure (Expr.isPos n)`, directly yielding the `HasType.isPos` constructor with proof `n ≠ 0`.

**Completeness** also proceeds by induction on `size`, constructing the appropriate branch index (`Fin gs.length`) for each `HasType` constructor. For example, `HasType.add` maps to branch index 2 in the `size + 1` case, with recursive appeals to the induction hypothesis for both subexpressions.

**Compositionality.** In the full system with `LawfulGenFor` / `LawfulBacktrackGenFor` instances, these proofs compose modularly: the `genWellFormed` proof discharges its `HasType` sub-generator obligations by appealing to the `LawfulBacktrackGenFor Expr (HasType · τ) (HasTypeBounded τ)` instance's `.sound` and `.complete` fields rather than inlining the `genHasType` proof. This has been validated: soundness and completeness of `genWellFormed` are proved using `backtrack_mem_iff` to decompose into branches, then `backtrackGen_bind_mem` / `backtrackGen_pure_mem` to decompose the sequential `BacktrackGen` bind chain within each branch, and finally `(inst τ).sound` / `(inst τ).complete` to discharge sub-generator obligations. The generator must explicitly route through the lawful instance to avoid the instance diamond described in "Instance diamond with `LawfulBacktrackGenFor`" above.

## 8. Plan of Work

The work proceeds in two major phases. Phase 1 makes Specimen emit Basalt-compatible generators that can be executed via Plausible. Phase 2 upgrades the system so that every derived generator is provably lawful.

### Phase 1: Basalt-compatible generation (execution only)

The goal of this phase is to make Specimen-derived generators polymorphic over Basalt's `Gen` class, using `BacktrackGen` for backtracking and `GenFor` / `BacktrackGenFor` for sub-generator resolution. Generators can be executed via Plausible but do not yet carry correctness proofs.

**Success criteria:** All existing Specimen snapshot tests pass (with updated expected output reflecting the new code shape). The `plausible` tactic works end-to-end for both `derive Arbitrary` and `derive_generator`. At least one manual soundness proof is completed for the running example.

#### Step 1.1: Define `BacktrackGen` and generator typeclasses in Basalt

- Define `BacktrackGen G α := G (Option α)` as a newtype
- Implement helper functions: `pure`/`fail`/`bind`/`liftGen` for `BacktrackGen`
- Implement `BacktrackGen.run` and `BacktrackGen.toPlausibleGen`
- Implement the `backtrack` combinator (weighted random selection with retry)
- Implement the `frequency` combinator (weighted random selection, no retry — for non-backtracking generators)
- Define the `GenFor α P` and `BacktrackGenFor α P` typeclasses
- Redefine `DecOpt P` to return `BacktrackGen G Bool` (polymorphic over `G`)
- Provide `GenFor` instances for standard types (`Nat`, `Bool`, `List`, etc.) using existing Basalt-polymorphic generators (e.g., `Nat.arbitrary`)
- Provide bridge instance: `instance [Decidable P] : DecOpt P`
- Optionally provide bridge: `instance [GenFor α (fun _ => True)] : Arbitrary α` for Plausible compatibility

#### Step 1.2: Prove SetGen support lemmas

- `backtrack_mem_iff`: `some a ∈ support ((backtrack gs).run)` iff `some a ∈ support ((gs[i].2 ()).run)` for some `i : Fin gs.length`. This is the key lemma for proving correctness of derived generators — it reduces backtracking to a disjunction over branches. (Proven now in a separate scratchfile.)
- `frequency_mem_iff`: analogous for `frequency`
- `backtrackGen_bind_mem`: `some b ∈ support ((x >>= f).run)` iff `∃ a, some a ∈ support x.run ∧ some b ∈ support ((f a).run)`. This is essential for decomposing sequential composition inside `BacktrackGen` branches — without it, proofs about composite generators (like `genWellFormed`) are extremely difficult because `BacktrackGen`'s bind introduces nested `match` on `Option` that doesn't reduce with `simp`.
- `backtrackGen_pure_mem`: `some b ∈ support ((pure a : BacktrackGen SetGen.Set α).run)` iff `b = a`. The base case for branch decomposition.
- Basic `liftGen` support lemma (follows from the above and Basalt's existing `SetGen.support_bind`, `SetGen.support_pure`)

#### Step 1.3: Modify Specimen's constrained code emission (`derive_generator`)

- Replace `GeneratorCombinators.backtrack` with Basalt's `backtrack` over `BacktrackGen G`
- Replace `Gen.frequency` / `oneOfWithDefault` with Basalt's `frequency`
- Replace `throw` with `BacktrackGen.fail` (equivalently, `pure none` at the `G` level)
- Replace fuel-based recursion with structural recursion on an explicit `size : Nat`
- Emit generators polymorphic over `[Gen G]` with `[GenFor α P]` / `[BacktrackGenFor α P]` constraints for sub-generators
- Replace `Arbitrary.arbitrary` calls with `GenFor.gen` wrapped in `BacktrackGen.liftGen`
- Replace `ArbitrarySizedSuchThat.arbitrarySizedST` calls with `BacktrackGenFor.gen` (or direct name calls for co-derived / mutually-recursive generators)
- Replace `DecOpt.decOpt` calls (pattern-matching on `Except`) with the new polymorphic `DecOpt.decOpt` (pattern-matching on `Bool` within `BacktrackGen`)
- Emit `ArbitrarySizedSuchThat` instances that call `BacktrackGen.toPlausibleGen`

#### Step 1.4: Modify Specimen's unconstrained code emission (`derive Arbitrary`)

- Replace `Gen.oneOfWithDefault` / `Gen.frequency` with Basalt's `frequency` combinator
- Replace `Arbitrary.arbitrary` calls (for sub-fields) with `GenFor.gen (P := fun _ => True)`
- Emit generators polymorphic over `[Gen G]` with `[GenFor α (fun _ => True)]` constraints for type parameters
- Emit `GenFor α (fun _ => True)` instances (with a `Gen.sized` wrapper or fixed fuel) for each derived type
- Emit bridge `Arbitrary` instance: `instance [GenFor α (fun _ => True)] : Arbitrary α where arbitrary := GenFor.gen`
- Ensure mutually recursive types use Lean's `mutual ... end` block with direct name calls, then register `GenFor` instances after

This step can proceed in parallel with Step 1.3 since the unconstrained deriver (`DeriveArbitrary.lean`) is independent of the constrained deriver (`DeriveConstrainedProducer.lean`).

#### Step 1.5: Validate the pipeline

- Verify existing Specimen test cases still pass (expected output will change shape; update snapshots)
- Verify `derive Arbitrary` produces working `GenFor` instances for standard test types (e.g., `Tree`, `Expr`)
- Verify the `plausible` tactic works end-to-end with both constrained and unconstrained generators
- Write a manual soundness proof for the `HasType` example, demonstrating that a Specimen-derived generator can be proved sound at `SetGen.Set` given `LawfulGenFor` / `LawfulBacktrackGenFor` instances for sub-generators. (Complete soundness and completeness proofs of `genHasType` in a scratchfile.)

### Phase 2: Lawful generation (with proof synthesis)

The goal of this phase is to make Specimen emit `LawfulGenFor` / `LawfulBacktrackGenFor` instances alongside the generators, so that every derived generator carries a machine-checked proof of soundness and completeness. Once this phase is complete, the system invariant holds: all `GenFor` / `BacktrackGenFor` instances are lawful, and proofs about composite generators compose modularly.

#### Step 2.1: Define `LawfulGenFor` and `LawfulBacktrackGenFor` in Basalt

- Define `LawfulGenFor` extending `GenFor` with soundness/completeness at `SetGen.Set`
- Define `LawfulBacktrackGenFor` extending `BacktrackGenFor` with a `Bounded : Nat → α → Prop` parameter and sound/complete fields at `SetGen.Set`
- Provide `LawfulGenFor` instances for standard types (using existing Basalt proofs like `Nat.arbitrary_support`)

#### Step 2.2: Synthesize soundness/completeness proofs in Specimen

For each derived **constrained** generator, Specimen emits a proof that the generator's support at `SetGen.Set` matches the target inductive relation. The proof structure mirrors the generator structure:

1. **Top-level**: The proof proceeds by `cases` on the `size` parameter, matching the generator's pattern match.
2. **Per-branch**: Each branch in `backtrack [...]` contributes one direction of the `↔`. The `backtrack_mem_iff` lemma decomposes `some a ∈ support (backtrack gs)` into a disjunction over branches.
3. **Soundness** (forward): For each branch that produces `some a`, show `P a` holds. This follows the `do`-block structure — each `liftGen` or `BacktrackGenFor.gen` call contributes a hypothesis (from the sub-generator's `LawfulGenFor` / `LawfulBacktrackGenFor` instance).
4. **Completeness** (backward): For each constructor of the inductive relation, exhibit a `size` and branch that produces the corresponding value. Typically, the recursive constructor needs `size = depth_of_derivation`.

Sub-generator proof obligations are discharged by the `LawfulGenFor` / `LawfulBacktrackGenFor` instances of sub-generators (available via typeclass resolution).

This structure has been validated by hand-proving soundness and completeness for the running example's `genHasType`. The proofs use `induction size`, `backtrack_mem_iff`, `fin_cases` on branch indices, and `simp` over `SetGen.support` lemmas — a pattern amenable to automation.

Emit `LawfulBacktrackGenFor` instances bundling generator + proof.

For each derived **unconstrained** generator (`derive Arbitrary`), Specimen emits a `LawfulGenFor α (fun _ => True)` instance. The property is trivially `True`, so the proof obligation reduces to:
- **Soundness**: trivial (every value satisfies `fun _ => True`)
- **Completeness**: show that every inhabitant of `α` is in the support of the generator. This amounts to showing that `frequency` with all constructors covered produces every value at some fuel — each constructor's branch reaches the corresponding value when sub-generators (with their own `LawfulGenFor` instances) are complete.

The proof follows the inductive structure of the type: base-case constructors are reachable at fuel 0, recursive constructors at fuel ≥ depth. This is simpler than the constrained case because there is no `Option` wrapping and no backtracking — `frequency_mem_iff` directly gives the membership condition.

#### Step 2.3: End-to-end validation

- Verify that Specimen-derived generators (both constrained and unconstrained) carry correct proofs (they typecheck with no `sorry`)
- Verify that proofs compose: a generator for type `A` that calls a generator for type `B` can use `B`'s `LawfulGenFor` / `LawfulBacktrackGenFor` proof without manual intervention
- Benchmark elaboration time to ensure proof synthesis does not unacceptably slow down `derive_generator` or `derive Arbitrary`

### Rollback strategy

If Phase 1 reveals fundamental design issues (e.g., universe polymorphism problems, instance diamonds at scale, or unacceptable elaboration performance), the changes are confined to:
- New definitions in Basalt (additive, do not break existing Basalt code)
- Modified code emission in Specimen (can be feature-flagged or reverted)

The existing `GeneratorCombinators.backtrack` path remains functional throughout development. A feature flag (`set_option specimen.basaltBridge true`) can gate the new emission path, allowing incremental rollout and easy revert.

## 9. Known Limitations and Future Work

The following issues are related to the migration but are not addressed by the plan above:

**`partial_fixpoint` vs explicit fuel.** Basalt's hand-written generators use `partial_fixpoint` for termination (no explicit fuel parameter), enabling proofs of almost-sure termination. Specimen-derived generators use explicit `size : Nat` with structural recursion. The plan preserves this pattern. A future optimization could emit `partial_fixpoint` generators where almost-sure termination can be proved, eliminating the fuel parameter and enabling tighter cost bounds. This is a research question deferred beyond Phase 2.

## Glossary

| Term | Meaning |
|---|---|
| **Constrained producer** | A generator that only produces values satisfying a user-specified inductive relation (e.g., well-typed expressions) |
| **Support** | The set of values a generator can produce (with nonzero probability) |
| **Fuel / size** | A `Nat` parameter that bounds recursion depth, ensuring termination |
| **`initSize`** | The *original* fuel value passed at the top level; sub-generators receive the full budget, not the decremented counter |
| **Schedule** | Specimen's internal representation of how to order constructor attempts when deriving a generator |
| **Backtracking** | The ability for a generator branch to signal failure, causing the combinator to retry another branch |
| **`BacktrackGen`** | A newtype wrapping `G (Option α)` — the backtracking layer used in this plan |
| **`GenFor` / `BacktrackGenFor`** | Typeclasses for finding generators by typeclass resolution (analogous to `Arbitrary` / `ArbitrarySizedSuchThat`) |
