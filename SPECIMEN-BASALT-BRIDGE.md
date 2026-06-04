# Bridging Specimen and Basalt via `BacktrackGen`

## Executive Summary

**Goal.** Make Specimen-derived generators polymorphic over Basalt's `Gen` class so they can be both *executed* (via `Plausible.Gen`) and *proved correct* (at `SetGen.Set`).

**Dependency change.** Today Specimen depends only on Plausible; after this work it will also depend on Basalt, using Basalt's `Gen` abstraction as the target monad for emitted generators.

**Four problems to solve:**

1. **Backtracking.** Basalt's `Gen` has no exceptions. We introduce `BacktrackGen G α` (a newtype over `G (Option α)`) and a `backtrack` combinator with retry semantics.
2. **Sub-generator resolution.** Plausible's `Arbitrary`/`ArbitrarySizedSuchThat` wrap `Plausible.Gen` specifically. We introduce `GenFor α P` and `BacktrackGenFor α P` — Basalt-polymorphic typeclasses for sub-generator lookup.
3. **Checkers.** `DecOpt` currently returns `Except GenError Bool`. We redefine it to return `BacktrackGen G Bool`, making it polymorphic over `G`.
4. **Unconstrained generators.** `derive Arbitrary` uses Plausible-specific combinators. We emit Basalt-polymorphic generators using a `frequency` combinator and `GenFor` instances.

**Plan of work:**

- *Phase 1* — Emit Basalt-compatible generators that execute via Plausible. All existing tests pass; the `plausible` tactic works end-to-end.
- *Phase 2* — Emit `BacktrackGenCorrect` certificates (soundness + completeness proofs at `SetGen.Set`) alongside every derived generator.

**What does NOT change:** User-facing syntax (`derive_generator`, `derive Arbitrary`), enumerators (future work), and almost-sure termination proofs (future work).

A glossary of terms appears at the end, for quick reference.

---

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

### The goal

We want Specimen-derived generators to be **polymorphic over Basalt's `Gen` class** so they can be:
- **Specified as today.** The `derive_generator (fun τ => ∃ e, HasType e τ)` command syntax remains unchanged. The difference is purely in what code gets emitted.
- **Executed** via `Plausible.Gen` (as today)
- **Proved sound/complete** at `SetGen.Set`

### Example

We use the following small typed language throughout to illustrate changes. It exercises all three mechanisms: backtracking (multiple constructors per type), checkers (`isPos` has a decidable guard `n ≠ 0`), and cross-generator composition (`WellFormed` calls `HasType`).

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

These generators work for execution but cannot be proved correct. To bridge them to Basalt, we need to solve the four problems listed in the executive summary.

## 2. Solving Problem 1: `BacktrackGen`

We introduce a newtype that wraps `G (Option α)` to represent generators that may fail locally:

```lean
/-- A backtracking generator: wraps G (Option α) where none = local failure, some = success. -/
structure BacktrackGen (G : Type u → Type v) (α : Type u) where
  run : G (Option α)
```

The `Option` layer is *inside* the generator monad `G`, meaning failure is a **value** that the generator successfully produces (as opposed to ⊥/`default`, which represents divergence). This lets other generators observe and react to failure — enabling retry.

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
def backtrack [Gen G] (gs : List (Nat × (Unit → BacktrackGen G α))) : BacktrackGen G α :=
  ⟨go gs.length (sumWeights gs) gs⟩
where
  go : Nat → Nat → List (Nat × (Unit → BacktrackGen G α)) → G (Option α)
  | _, _, [] => pure none
  | 0, _, _ => pure none
  | fuel + 1, total, gs@(_ :: _) => do
    let n ← RandomChoice.choose 0 (total - 1) (by omega)
    let (k, g, gs') := pickDrop gs n.down
    match ← (g ()).run with
    | some a => pure (some a)
    | none => go fuel (total - k) gs'
```

Operational semantics: pick a branch randomly (weighted), try it; if it returns `none`, remove it from the pool and retry with decremented fuel. Termination is structural on fuel (starts at `gs.length`).

### Helpers

```lean
/-- Lift a non-failing G α into BacktrackGen G α. -/
def BacktrackGen.liftGen [Gen G] (g : G α) : BacktrackGen G α :=
  ⟨do let a ← g; pure (some a)⟩

/-- Signal local failure (backtrack). -/
def BacktrackGen.fail [Gen G] : BacktrackGen G α :=
  ⟨pure none⟩
```

### Boundary: unwrapping `BacktrackGen`

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

> **Design rationale** (why a newtype, interpretations across Basalt instances): see Appendix A.

## 3. Solving Problem 2: Sub-generator Resolution

Today, Specimen resolves sub-generators via Plausible's `Arbitrary` (for unconstrained types) and `ArbitrarySizedSuchThat` (for constrained types). These wrap `Plausible.Gen` specifically — they cannot be used inside a polymorphic `G`.

### Design: `GenFor` and `BacktrackGenFor`

```lean
/-- A non-backtracking generator for type α whose outputs satisfy P.
    Always succeeds. Analogous to Plausible's Arbitrary, but polymorphic over Gen G. -/
class GenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], G α

/-- A backtracking generator for type α whose successful outputs satisfy P.
    May fail. Takes a Nat fuel parameter for structural termination.
    Analogous to Specimen's ArbitrarySizedSuchThat, but polymorphic over Gen G. -/
class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G α
```

The calling convention:
- `GenFor` → always succeeds, caller uses `BacktrackGen.liftGen` to enter `BacktrackGen`
- `BacktrackGenFor` → may fail, caller binds directly in `BacktrackGen` (failure propagates via `bind`)

### Standard `GenFor` instances

```lean
instance : GenFor Nat (fun _ => True) where
  gen := Nat.arbitrary  -- Basalt's polymorphic Nat generator

instance : GenFor Bool (fun _ => True) where
  gen := Bool.arbitrary
```

Bridge to Plausible:

```lean
instance [GenFor α (fun _ => True)] : Arbitrary α where
  arbitrary := GenFor.gen  -- specializes at G := Plausible.Gen
```

## 4. Solving Problem 3: Checkers (`DecOpt`)

Today's `DecOpt` returns `Except GenError Bool` — a Plausible-specific type. We redefine it to return `BacktrackGen G Bool`:

```lean
class DecOpt (P : Prop) where
  decOpt : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G Bool
```

The three-valued semantics map to `G (Option Bool)`:
- `some true` → P holds
- `some false` → P doesn't hold
- `none` → can't decide (out of fuel) → causes backtracking

### Bridge from `Decidable`

```lean
instance [Decidable P] : DecOpt P where
  decOpt _ := pure (decide P)
```

> **Interpretations** (how `DecOpt` behaves at each Basalt instance): see Appendix D.

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

And `genWellFormed` calls the `HasType` generator via `BacktrackGenFor` typeclass resolution:

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

### Key transformations from Specimen's output today 

| Today | After migration |
|---|---|
| `MonadExcept.throw Gen.genericFailure` | `BacktrackGen.fail` |
| `return value` | `pure value` (BacktrackGen Monad wraps in `some`) |
| `Arbitrary.arbitrary` | `BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G α)` |
| `ArbitrarySizedSuchThat.arbitrarySizedST (fun e => P e) initSize` | `BacktrackGenFor.gen (P := fun e => P e) initSize` |
| `match @DecOpt.decOpt P _ fuel with \| Except.ok true => ... \| _ => throw` | `match ← DecOpt.decOpt (P := P) fuel with \| true => ... \| false => BacktrackGen.fail` |
| Return type: `Plausible.Gen α` | `BacktrackGen G α` |
| Recursive calls via `let rec aux_arb` | Direct structural recursion on `size : Nat` |

The `initSize`/`size` split remains: `size` is structurally decremented for termination; `initSize` is passed unchanged to sub-generators via `BacktrackGenFor.gen ... initSize`.

### Executing via Plausible

```lean
instance : ArbitrarySizedSuchThat Expr (HasType · τ) where
  arbitrarySizedST size := BacktrackGen.toPlausibleGen (genHasType size τ size)

instance : ArbitrarySizedSuchThat Prog WellFormed where
  arbitrarySizedST size := BacktrackGen.toPlausibleGen (genWellFormed size size)
```

The `plausible` tactic finds these instances via the existing `ArbitrarySizedSuchThat → ArbitrarySuchThat → Arbitrary` chain and executes them normally.

## 6. Solving Problem 4: Unconstrained Generators (`derive Arbitrary`)

### The problem

Specimen's `derive Arbitrary` emits generators using `Gen.frequency` / `Gen.oneOfWithDefault` and `Arbitrary.arbitrary` — all Plausible-specific. Unlike constrained generators, unconstrained generators never backtrack (always succeed), so no `BacktrackGen` is needed — just the `frequency` combinator and `GenFor`.

### The `frequency` combinator

```lean
/-- Weighted random selection without retry. For non-backtracking generators.
    Picks a generator from `gs` by weight interval (matching GeneratorCombinators.frequency).
    If `gs` is empty, the `default` generator is returned. -/
def frequency [Gen G] (default : G α) (gs : List (Nat × (Unit → G α))) : G α :=
  match gs with
  | [] => default
  | _ => do
    let total := sumWeights gs
    let n ← RandomChoice.choose 0 (total - 1) (by omega)
    (pick (fun () => default) gs n.down).snd ()
```

### Example: what changes

For a type like `Tree α`, today's output vs the migrated version:

**Today:**
```lean
instance [Arbitrary α] : ArbitraryFueled (Tree α) where
  arbitraryFueled :=
    let rec aux_arb (fuel : Nat) : Plausible.Gen (Tree α) := ...
    fun fuel => aux_arb fuel
```

**After migration:**
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
  gen := Gen.sized Tree.gen
```

### Key transformations

| Today | After migration |
|---|---|
| `Gen.oneOfWithDefault default [gs]` / `Gen.frequency default [(w, g), ...]` | `frequency default [(w, fun () => g), ...]` |
| `Arbitrary.arbitrary` | `GenFor.gen (P := fun _ => True)` |
| Recursive calls: `aux_arb fuel'` | `Tree.gen fuel` |
| Return type: `Plausible.Gen α` | `G α` (polymorphic over `[Gen G]`) |
| Instance: `ArbitraryFueled` | `GenFor α (fun _ => True)` |

### Executing via Plausible

The bridge instance from Section 3 provides backward compatibility:

```lean
instance [GenFor α (fun _ => True)] : Arbitrary α where
  arbitrary := GenFor.gen  -- specializes at G := Plausible.Gen
```

## 7. Design Notes

### Calling patterns summary

The emitted code uses different calling conventions depending on the sub-generator kind:

- **Non-backtracking leaf types** (via `GenFor`): Always succeeds, lifted into `BacktrackGen`:
  ```lean
  let n ← BacktrackGen.liftGen (GenFor.gen (P := fun _ => True) : G Nat)
  ```

- **Backtracking constrained sub-generator** (via `BacktrackGenFor`): May fail, resolved by typeclass. Failure propagates automatically via `bind`:
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

### Mutual recursion

For mutually recursive inductive relations, the emitted code uses Lean's `mutual ... end` block with direct name calls between co-defined generators (not typeclass resolution). After the mutual block, each generator is registered as a `BacktrackGenFor` instance. This is the same pattern Specimen uses today.

### The `initSize` parameter

- `size` is structurally decremented at each recursive call, ensuring termination.
- `initSize` is the original fuel value, passed unchanged to sub-generators via `BacktrackGenFor.gen ... initSize`.

Sub-generators always get a full budget. This matches today's behavior where `aux_arb initSize size' Ty.nat` passes `initSize` to nested calls.

### Known limitations

**`partial_fixpoint` vs explicit fuel.** Basalt's hand-written generators use `partial_fixpoint` for termination (no explicit fuel parameter), enabling proofs of almost-sure termination. Specimen-derived generators use explicit `size : Nat` with structural recursion. The plan preserves this pattern. A future optimization could emit `partial_fixpoint` generators, eliminating the fuel parameter and enabling tighter cost bounds. This is deferred beyond Phase 2.

> **Further design discussion** (typeclass resolution safety, fuel vs `partial_fixpoint`, performance benchmarks): see Appendices A and B.

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
- Provide `GenFor` instances for standard types (`Nat`, `Bool`, `List`, etc.) using existing Basalt-polymorphic generators
- Provide bridge instance: `instance [Decidable P] : DecOpt P`
- Optionally provide bridge: `instance [GenFor α (fun _ => True)] : Arbitrary α`

#### Step 1.2: Prove SetGen support lemmas

- `backtrack_mem_iff`: `some a ∈ support ((backtrack gs).run)` iff `some a ∈ support ((gs[i].2 ()).run)` for some `i`
- `frequency_mem_iff`: analogous for `frequency`
- `backtrackGen_bind_mem`: decomposition of sequential composition inside `BacktrackGen` branches
- `backtrackGen_pure_mem`: base case for branch decomposition
- Basic `liftGen` support lemma

#### Step 1.3: Modify Specimen's constrained code emission (`derive_generator`)

- Replace `GeneratorCombinators.backtrack` with Basalt's `backtrack` over `BacktrackGen G`
- Replace `Gen.frequency` / `oneOfWithDefault` with Basalt's `frequency`
- Replace `throw` with `BacktrackGen.fail`
- Replace fuel-based recursion with structural recursion on an explicit `size : Nat`
- Emit generators polymorphic over `[Gen G]` with `[GenFor α P]` / `[BacktrackGenFor α P]` constraints
- Replace `Arbitrary.arbitrary` calls with `GenFor.gen` wrapped in `BacktrackGen.liftGen`
- Replace `ArbitrarySizedSuchThat.arbitrarySizedST` calls with `BacktrackGenFor.gen`
- Replace `DecOpt.decOpt` calls (pattern-matching on `Except`) with the new polymorphic `DecOpt.decOpt`
- Emit `ArbitrarySizedSuchThat` instances that call `BacktrackGen.toPlausibleGen`

#### Step 1.4: Modify Specimen's unconstrained code emission (`derive Arbitrary`)

- Replace `Gen.oneOfWithDefault` / `Gen.frequency` with Basalt's `frequency` combinator
- Replace `Arbitrary.arbitrary` calls with `GenFor.gen (P := fun _ => True)`
- Emit generators polymorphic over `[Gen G]` with `[GenFor α (fun _ => True)]` constraints
- Emit `GenFor α (fun _ => True)` instances for each derived type
- Emit bridge `Arbitrary` instance
- Ensure mutually recursive types use `mutual ... end` with direct name calls

This step can proceed in parallel with Step 1.3 since the unconstrained deriver (`DeriveArbitrary.lean`) is independent of the constrained deriver (`DeriveConstrainedProducer.lean`).

#### Step 1.5: Validate the pipeline

- Verify existing Specimen test cases still pass (update snapshots for new output shape)
- Verify `derive Arbitrary` produces working `GenFor` instances for standard test types
- Verify the `plausible` tactic works end-to-end with both constrained and unconstrained generators
- Write a manual soundness proof for the `HasType` example demonstrating `BacktrackGenCorrect`

### Phase 2: Lawful generation (with proof synthesis)

The goal of this phase is to make Specimen emit `BacktrackGenCorrect` certificates alongside the generators, so that every derived generator carries a machine-checked proof of soundness and completeness.

#### Step 2.1: Define `BacktrackGenCorrect` in Basalt

- Define `BacktrackGenCorrect` structure with `sound` and `complete` fields at `SetGen.Set`
- Proofs for composite generators take `BacktrackGenCorrect` certificates as hypotheses
- Provide `BacktrackGenCorrect` certificates for standard types

#### Step 2.2: Synthesize soundness/completeness proofs in Specimen

For each derived **constrained** generator, Specimen emits a proof that the generator's support at `SetGen.Set` matches the target relation. The proof structure:

1. **Top-level**: `cases` on `size`, matching the generator's pattern match.
2. **Per-branch**: `backtrack_mem_iff` decomposes into a disjunction over branches.
3. **Soundness**: For each branch producing `some a`, show `P a` holds.
4. **Completeness**: For each constructor of the inductive relation, exhibit a `size` and branch that produces the corresponding value.

Sub-generator obligations are stated as `BacktrackGenCorrect` hypotheses — keeping proofs modular.

For **unconstrained** generators, the property is `True`, so soundness is trivial. Completeness amounts to showing every inhabitant is reachable at some fuel — following the inductive structure of the type.

#### Step 2.3: End-to-end validation

- Verify derived generators carry correct proofs (no `sorry`)
- Verify proofs compose across sub-generators
- Benchmark elaboration time

### Rollback strategy

If Phase 1 reveals fundamental design issues, the changes are confined to:
- New definitions in Basalt (additive, do not break existing Basalt code)
- Modified code emission in Specimen (can be feature-flagged or reverted)

The existing `GeneratorCombinators.backtrack` path remains functional. A feature flag (`set_option specimen.basaltBridge true`) can gate the new emission path.

## Glossary

| Term | Meaning |
|---|---|
| **Constrained producer** | A generator that only produces values satisfying a user-specified inductive relation |
| **Support** | The set of values a generator can produce (with nonzero probability) |
| **Fuel / size** | A `Nat` parameter that bounds recursion depth, ensuring termination |
| **`initSize`** | The *original* fuel value passed at the top level; sub-generators receive the full budget |
| **Schedule** | Specimen's internal representation of how to order constructor attempts |
| **Backtracking** | The ability for a generator branch to signal failure, causing retry |
| **`BacktrackGen`** | A newtype wrapping `G (Option α)` — the backtracking layer used in this plan |
| **`GenFor` / `BacktrackGenFor`** | Typeclasses for sub-generator lookup (analogous to `Arbitrary` / `ArbitrarySizedSuchThat`) |

---

## Appendix A: Design Rationale

### Why `BacktrackGen` is a structure (newtype)

`BacktrackGen` is defined as a `structure` wrapping `G (Option α)` rather than a type alias for two reasons:

1. **Disambiguation.** Without the newtype, `G (Option α)` is ambiguous — it could be a generator that legitimately produces `Option` values (where `none` is a valid output) or a backtracking generator where `none` signals failure. `BacktrackGen` makes the intent explicit at the type level.

2. **Own Monad instance.** As a `structure`, `BacktrackGen G` gets its own `Monad` instance that threads `Option` automatically. This means `pure x` wraps in `some`, and `bind` short-circuits on `none`. Without this, code inside backtracking branches would need to manually construct `pure (some x)` and pattern-match on `Option` at every bind.

### Why typeclass resolution is safe here

A natural concern: typeclass resolution is opaque, so how can a proof about `genWellFormed` know which `BacktrackGenFor Expr (HasType · τ)` instance was resolved?

The answer is that we do **not** attempt to discharge this — correctness proofs are parameterized by a `BacktrackGenCorrect` hypothesis about whatever the sub-generator resolves to. The theorem states: "if the sub-generator (whatever it is) is sound and complete, then `genWellFormed` is sound and complete." This is honest about the opacity of instance resolution and avoids the instance diamond problem entirely.

In practice, for a fully-closed correctness argument, one would need to show that the specific `BacktrackGenFor` instance registered for `HasType` corresponds to `genHasType` (which has its own `BacktrackGenCorrect` certificate). This final connection step is left as an assumption — it's a statement about instance resolution stability that Lean doesn't expose as a provable fact.

### Fuel vs size vs `partial_fixpoint`

The `size`/`fuel` parameter in generated code serves two distinct purposes:

1. **Termination witness.** Lean requires structural recursion (or `partial_fixpoint`) for every recursive definition. The `size : Nat` parameter with pattern-matching on `0` vs `size + 1` provides this.

2. **Size control.** In property-based testing, generators need a knob that controls the size of generated values. Plausible's `Gen.sized` provides this via a `ReaderT (ULift Nat)` layer.

These two roles coincide in today's Specimen output (the fuel *is* the size), but are conceptually independent:

- **For constrained generators (`BacktrackGenFor`):** Both roles are essential. The fuel ensures termination and bounds derivation tree depth.

- **For unconstrained generators (`GenFor`):** The fuel is used *only* for termination and size control. In Basalt, `partial_fixpoint` could eliminate the explicit termination witness, since it provides a well-founded recursion principle with `⊥` as the default.

**Practical upshot:** Phase 1 preserves explicit fuel for both. A future optimization could emit `partial_fixpoint`-based generators:
```lean
def Tree.gen [Gen G] [GenFor α (fun _ => True)] : G (Tree α) :=
  partial_fixpoint fun self => frequency (pure Tree.leaf) [
    (1, fun () => pure Tree.leaf),
    (???, fun () => do  -- weight needs to come from somewhere
      let left ← self
      let val ← GenFor.gen (P := fun _ => True)
      let right ← self
      pure (Tree.node left val right))]
```
The open question is expressing size-dependent weights without explicit fuel. Deferred as a research question.

### Why `Bounded` is separate from `P` in `BacktrackGenCorrect`

The property `P` (e.g., `HasType e τ`) is the *semantic* specification the user cares about. But a fuel-based generator cannot produce *all* values satisfying `P` at every size — it only produces values within its size budget and sub-generator ranges. The `Bounded` predicate captures these implementation constraints: `Bounded size a` implies `P a` but additionally requires bounded depth and bounded leaf values.

This two-parameter design is a direct consequence of using explicit fuel for termination. If generators were defined via `partial_fixpoint` — where the generator's support at the fixpoint covers all values satisfying `P` — then `Bounded` would be unnecessary. The `Bounded` parameter is the price of fuel-based termination; eliminating it is a benefit of moving to `partial_fixpoint` in the future.

## Appendix B: Performance

`BacktrackGen` adds an `Option` wrapper at every bind within backtracking branches. Benchmarking (`SpecimenTest/BridgeBenchmark.lean`) shows:

| Scenario | Bridge/legacy ratio | Notes |
|---|---|---|
| Recursive generator (5-ary constructor, sizes 2–4) | 97–101% | Dominant cost is recursion; `Option` overhead invisible |
| Backtracking on guards (`isPos`, DecOpt check) | 100–105% | Within noise |
| Stress test: 5 branches × 5 `liftGen`s, 4 always fail | **118%** | Worst case: cheap branches that fail frequently |
| Same stress test with batched `liftGen`s | **106%** | Batching cuts overhead by ~2/3 |

The 18% worst-case arises when branches consist almost entirely of `liftGen` calls and multiple branches are tried per iteration. In realistic generators (like Cedar's `HasType` with 23 constructors), the `Option` overhead is amortized to < 3%.

**IR verification:** The Lean 4 compiler erases the `BacktrackGen` newtype (no `.mk`/`.run` in compiled IR), and `@[specialize]` eliminates the `[Gen G]` dictionary when instantiated at `Plausible.Gen`.

### Optimization: batching consecutive `liftGen` calls

When multiple unconstrained field generations appear consecutively (before any backtracking operation), they can be batched:

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

The batching boundary is any operation that can fail: a `BacktrackGenFor.gen` call, a `DecOpt` check, or `BacktrackGen.fail`.

### Optimization: `liftBind` for interleaved non-backtracking operations

When a `liftGen` is followed by a backtracking continuation (not another `liftGen`), a fused combinator eliminates the intermediate `Option`:

```lean
@[inline] def BacktrackGen.liftBind [Gen G] (g : G α) (f : α → BacktrackGen G β) : BacktrackGen G β :=
  ⟨do let a ← g; (f a).run⟩
```

Neither optimization affects provability: `liftBind g f` has the same denotation as `bind (liftGen g) f` at all Basalt interpretations.

## Appendix C: Proof Strategy

### `BacktrackGenCorrect`

```lean
/-- A correctness certificate for a backtracking generator: soundness + completeness
    with respect to a size-indexed predicate. This is a proof artifact only — it does not
    contain or constrain the generator code. -/
structure BacktrackGenCorrect.{u}
    (gen : ∀ {G : Type u → Type u} [Gen G], Nat → BacktrackGen G α)
    (Bounded : Nat → α → Prop) where
  sound : ∀ size a,
    some a ∈ SetGen.support ((gen (G := SetGen.Set) size).run) → Bounded size a
  complete : ∀ size a,
    Bounded size a → some a ∈ SetGen.support ((gen (G := SetGen.Set) size).run)
```

**Relationship to Basalt's `LawfulGenerator`:** Basalt's `LawfulGenerator` says "this particular generator is sound, complete, terminating, and cost-bounded." Our `BacktrackGenCorrect` serves a different purpose: it asserts that a generator function is sound and complete with respect to a bounded predicate. It omits cost and termination requirements; these could be added as future structure fields.

### The key lemma: `backtrack_mem_iff`

```lean
theorem backtrack_mem_iff (gs : List (Nat × (Unit → BacktrackGen SetGen.Set α)))
    (hpos : ∀ i : Fin gs.length, gs[i].1 > 0) (a : α) :
    some a ∈ SetGen.support ((backtrack gs).run) ↔
    ∃ i : Fin gs.length, some a ∈ SetGen.support ((gs[i].2 ()).run) := ...
```

This reduces reasoning about `backtrack` to reasoning about individual branches.

### Proof structure for the running example

**The predicate:**

```lean
def HasTypeBounded (τ : Ty) (size : Nat) (e : Expr) : Prop :=
  HasType e τ ∧ exprBounded size e
```

where `exprBounded size e` requires leaf naturals ≤ 100 and `add`-nesting ≤ `size`.

**Soundness** proceeds by induction on `size`, applying `backtrack_mem_iff` to decompose into branches, then case-splitting on `τ`. For the `isPos` branch, the `DecOpt` check produces a `Bool` matched on — only `true` reaches `pure (Expr.isPos n)`, yielding `HasType.isPos` with proof `n ≠ 0`.

**Completeness** proceeds by induction on `size`, constructing the appropriate branch index for each `HasType` constructor. `HasType.add` maps to branch 2 in the `size + 1` case.

**Compositionality.** Correctness proofs for generators that call sub-generators are parameterized by correctness certificates of those sub-generators:

```lean
theorem genWellFormed_correct
    (sub_correct : ∀ τ, BacktrackGenCorrect
      (fun {G} [Gen G] (size : Nat) => BacktrackGenFor.gen (P := fun e => HasType e τ) (G := G) size)
      (HasTypeBounded τ)) :
    BacktrackGenCorrect (fun size => genWellFormed size size) WellFormedBounded where
  sound := fun initSize p h => by ...
  complete := fun initSize p h => by ...
```

The proof uses `(sub_correct τ).sound` / `(sub_correct τ).complete` to discharge sub-generator obligations. No "lawful instance" routing is needed.

## Appendix D: Interpretations Across Basalt Instances

### `BacktrackGen`

| Instance | `BacktrackGen G α` is... | `none` means... | `some a` means... |
|---|---|---|---|
| `SetGen.Set` | `Set (Option α)` | failure is reachable | `a` is reachable |
| `SPMF` | `SPMF (Option α)` | mass on failure | mass on producing `a` |
| `SPMF.Cost` | `SPMF (Option α × Nat)` | failure with cost `n` | producing `a` with cost `n` |
| `Plausible.Gen` | `Plausible.Gen (Option α)` | generation failed | generation succeeded |

Note: `SPMF.Cost` tracks the number of `choose` calls. In `backtrack`, each retry costs one `choose` plus whatever choices that branch made. The cost of backtracking falls out automatically from existing `IsBounded_bind` and `IsBounded_choose` theorems.

### `DecOpt`

| Instance | `DecOpt.decOpt P fuel` is... | `none` means... | `some true/false` means... |
|---|---|---|---|
| `SetGen.Set` | `Set (Option Bool)` | checking may fail | P is/isn't decidable as true |
| `SPMF` | `SPMF (Option Bool)` | mass on undecided | mass on decided |
| `Plausible.Gen` | `Plausible.Gen (Option Bool)` | checker ran out of fuel | checker decided |
