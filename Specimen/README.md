Specimen extends Plausible with automatic derivation of constrained generators, enumerators, and checkers for inductive relations. This document describes the available commands and how to use them.

## Overview of Commands

### 1. `derive_mutual` — Unified Multi-Spec Derivation (Recommended)

**Purpose**: The primary command for deriving constrained generators, enumerators, and/or checkers. It handles mutual recursion, automatic dependency discovery, and multi-output generation.

**Syntax**:
```lean
derive_mutual
  [sort] spec1,
  [sort] spec2,
  ...
```

Where each `sort` is optionally one of `generator` (default), `enumerator`, or `checker`, and each spec is either:
- `(fun x1 ... xn => ∃ y1 ... ym, P x1 ... y1 ... xn)` — inputs bound by `fun`, outputs bound by `∃`
- `(∃ y1 ... ym, P y1 ... ym)` — all positions are outputs (multi-output mode)

**Key Options** (set before calling `derive_mutual`):
```lean
set_option specimen.autoDeriveDeps true  -- auto-derive sub-relation instances
set_option specimen.multiOutput true     -- allow multi-output hypothesis steps
```

**Creates**: Instances of `ArbitrarySizedSuchThat`, `EnumSizedSuchThat`, or `DecOpt` depending on the sort.

**Examples**:

```lean
-- Basic: derive a generator for balanced trees
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

derive_mutual
  (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Multiple specs: generator + checker derived together
derive_mutual
  generator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t),
  checker (fun lo hi t => BST lo hi t)

-- Mutual recursion: typing depends on lookup, both derived automatically
derive_mutual
  (fun G t => ∃ (e : term), typing G e t)

-- Multi-output: generate all existential variables at once
derive_mutual
  (∃ (Γ : List type) (e : term) (τ : type), typing Γ e τ)

-- Enumerator sort
derive_mutual enumerator
  (fun re => ∃ (s : List Nat), ExpMatch s re)

-- Checker sort
derive_mutual checker
  (fun Γ e τ => typing Γ e τ)
```

**How `autoDeriveDeps` works**: When enabled, `derive_mutual` inspects the constructors of the target relation and automatically derives generator/checker instances for any sub-relations (e.g., `typing` depends on `lookup` — both will be derived). This eliminates the need to manually derive dependencies first.

**How `multiOutput` works**: When enabled, hypothesis steps can produce multiple output variables simultaneously. For instance, a hypothesis `typing Γ e τ` can generate both `e` and `τ` in a single step (producing a `Prod`), rather than requiring separate steps.

### 2. `derive_generator` — Single-Spec Constrained Random Generators

**Purpose**: Derives a single constrained random generator. Useful for quick one-off derivations or when you don't need dependency auto-derivation.

**Syntax**:
```lean
derive_generator (fun x1 ... xn => ∃ y1 ... ym, P x1 ... y1 ... xn)
```

Where:
- `P` is an inductively defined relation
- `y1 ... ym` are values to be generated (bound by `∃`)
- `x1 ... xn` are input parameters (bound by `fun`)

**Creates**: An instance of `ArbitrarySizedSuchThat`

**Examples**:
```lean
-- Single output
derive_generator (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Multiple outputs
derive_generator (fun n => ∃ a b, Split n a b)

-- All outputs (no inputs)
derive_generator (∃ a n b, Split n a b)

-- Use the generator
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balancedTree 5 t)) 10
```

### 3. `derive_enumerator` — Single-Spec Constrained Deterministic Enumerators

**Purpose**: Derives a deterministic enumerator that systematically produces values satisfying an inductive relation.

**Syntax**: Same as `derive_generator`
```lean
derive_enumerator (fun x1 ... xn => ∃ y, P x1 ... y ... xn)
```

**Creates**: An instance of `EnumSizedSuchThat`

**Example**:
```lean
derive_enumerator (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Use the enumerator (use smaller fuel to avoid stack overflow)
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balancedTree 3 t)) 3
```

### 4. `derive_checker` — Partial Decision Procedures

**Purpose**: Derives a checker (partial decision procedure) for an inductive relation.

**Syntax**:
```lean
derive_checker (fun x1 ... xn => P x1 ... xn)
```

**Creates**: An instance of `DecOpt`

**Returns**: `Nat → Except GenError Bool` where:
- `.ok true` — the relation holds
- `.ok false` — the relation doesn't hold
- `.error _` — ran out of fuel, couldn't decide

**Example**:
```lean
derive_checker (fun lo hi t => BST lo hi t)

let result := DecOpt.decOpt (BST 0 10 myTree) 100  -- 100 is fuel
match result with
| .ok true => IO.println "Is a BST!"
| .ok false => IO.println "Not a BST!"
| .error _ => IO.println "Couldn't decide (out of fuel)"
```

### 5. `deriving Arbitrary` — Unconstrained Random Generators

**Purpose**: Derives an unconstrained random generator for an algebraic data type.

**Syntax**:
```lean
-- Inline after type definition
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Arbitrary

-- Separate command (also works for multiple/mutual types)
deriving instance Arbitrary for Tree
deriving instance Arbitrary for NatTree  -- handles mutually recursive types
```

**Creates**: An instance of `ArbitraryFueled` (from Plausible), which provides `Arbitrary`

**Example**:
```lean
#eval runArbitrary (α := Tree) 10
```

### 6. `deriving Enum` — Unconstrained Deterministic Enumerators

**Purpose**: Derives an unconstrained deterministic enumerator for an algebraic data type.

**Syntax**:
```lean
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Enum

-- Separate command (supports mutual types)
deriving instance Enum for MutEven, MutOdd
```

**Creates**: An instance of `EnumSized`

**Example**:
```lean
#eval runEnum (α := Tree) 5
```

## Typeclasses

| Command | Typeclass | Purpose |
|---------|-----------|---------|
| `derive_mutual` (generator) | `ArbitrarySizedSuchThat` | Constrained random generation |
| `derive_mutual` (enumerator) | `EnumSizedSuchThat` | Constrained enumeration |
| `derive_mutual` (checker) | `DecOpt` | Partial decision procedure |
| `derive_generator` | `ArbitrarySizedSuchThat` | Constrained random generation |
| `derive_enumerator` | `EnumSizedSuchThat` | Constrained enumeration |
| `derive_checker` | `DecOpt` | Partial decision procedure |
| `deriving Arbitrary` | `ArbitraryFueled` / `Arbitrary` (from Plausible) | Unconstrained random generation |
| `deriving Enum` | `EnumSized` / `Enum` | Unconstrained enumeration |

## Typeclass Hierarchy

```
ArbitrarySizedSuchThat α P    -- Sized constrained generator
    ↓ (automatic instance)
ArbitrarySuchThat α P         -- Unsized constrained generator

ArbitraryFueled α             -- Sized unconstrained generator (from Plausible)
    ↓ (automatic instance)
Arbitrary α                   -- Unsized unconstrained generator (from Plausible)
```

Similar hierarchy exists for enumerators (`EnumSizedSuchThat` → `EnumSuchThat`, etc.)

## Configuration Options

| Option | Default | Description |
|--------|---------|-------------|
| `specimen.autoDeriveDeps` | `false` | Automatically derive dependency instances for sub-relations referenced in constructors |
| `specimen.multiOutput` | `false` | Allow multi-output production steps (generate multiple `∃`-bound variables per hypothesis) |
| `specimen.fuel` | `10000` | Fuel (termination budget) for derived generators/enumerators/checkers |
| `specimen.richOutput` | `true` | Emit rich HTML widget in the Lean infoview showing schedule details |
| `specimen.textOutput` | `0` | Plain-text output verbosity: 0=off, 1=summary, 2=problems only, 3=full schedules |
| `specimen.searchLimit` | `200000` | Max hypothesis orderings to evaluate per constructor during branch-and-bound schedule search |
| `specimen.debug` | `false` | Enable debug messages from Specimen |

## How to Use Derived Instances

### Using Constrained Generators

```lean
-- After deriving (with derive_mutual or derive_generator)
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
derive_mutual
  (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Sample from the generator
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balancedTree 5 t)) 10
```

### Using Constrained Enumerators

```lean
derive_mutual enumerator
  (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Enumerate with fuel parameter (use smaller values to avoid stack overflow)
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balancedTree 3 t)) 3
```

### Using Checkers

```lean
derive_mutual checker
  (fun lo hi t => BST lo hi t)

-- Check if a tree satisfies BST property
let isValid := DecOpt.decOpt (BST 0 10 myTree) 100
```

### Using Unconstrained Generators

```lean
deriving instance Arbitrary for Tree

-- Direct sampling
#eval runArbitrary (α := Tree) 10

-- With plausible tactic (automatic)
example (t : Tree) : mirror (mirror t) = t := by
  plausible  -- automatically uses Arbitrary Tree instance
```

## Common Patterns

### End-to-End Property Testing

```lean
-- Derive generator for valid inputs
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
derive_mutual
  (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)

-- Derive checker for output validation
derive_mutual checker
  (fun lo hi t => BST lo hi t)

-- Test a function preserves the BST invariant
def testInsert (numTrials : Nat) : IO Unit := do
  let size := 10
  for _ in [:numTrials] do
    let x ← Gen.run (Subtype.val <$> Gen.chooseNatLt 1 10 (by decide)) size
    let t ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => BST 0 10 t) size) size
    let t' := insert x t
    let b := DecOpt.decOpt (BST 0 10 t') size
    match b with
    | .ok true => pure ()
    | .ok false => IO.println s!"Property falsified! t = {repr t}, x = {x}"
    | .error _ => IO.println "Checker ran out of fuel"
```

### Deriving for Complex Relations (STLC Typing)

```lean
-- Define types and terms
inductive typ where | Nat | Fun : typ → typ → typ
inductive term where | Const : Nat → term | Var : Nat → term | App : term → term → term | Abs : typ → term → term

-- Define the typing relation
inductive typing : List typ → term → typ → Prop where
  | TConst : ∀ Γ n, typing Γ (.Const n) .Nat
  | TAbs : ∀ Γ e τ1 τ2, typing (τ1::Γ) e τ2 → typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
  | TVar : ∀ Γ x τ, lookup Γ x = some τ → typing Γ (.Var x) τ
  | TApp : ∀ Γ e1 e2 τ1 τ2, typing Γ e2 τ1 → typing Γ e1 (.Fun τ1 τ2) → typing Γ (.App e1 e2) τ2

-- One command derives everything (typing + lookup sub-relation)
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
derive_mutual
  (fun G t => ∃ (e : term), typing G e t)
```

## Requirements

For successful derivation, ensure:

1. **For `derive_mutual` / `derive_generator` / `derive_enumerator`**:
   - The relation `P` must be inductively defined
   - Input types must have `Arbitrary` instances (for generators) or `Enum` instances (for enumerators)
   - With `autoDeriveDeps`, sub-relations are handled automatically; without it, their instances must exist

2. **For `derive_checker`**:
   - The relation must be inductively defined
   - All types involved must have decidable equality when needed

3. **For `deriving Arbitrary` / `deriving Enum`**:
   - The type must be an inductive type
   - Must have at least one non-recursive constructor (for termination)
   - Constituent types must have `Arbitrary` / `Enum` instances

## Limitations

1. **Pattern matching**: Expects variable names in lambda positions, not literals
2. **Opaque definitions**: Types hidden behind `opaque` cannot be unfolded by the deriver
3. **Enumerator fuel**: Enumerators can stack overflow with large fuel values; use smaller values (3-5)
4. **Checker fuel**: Checkers may return an error if they run out of fuel on complex relations
5. **Instance parameters**: Relations with dependent (non-typeclass) implicit arguments may require explicit annotations

## See Also

- `SpecimenTest/DeriveArbitrarySuchThat/` — Examples of constrained generators
- `SpecimenTest/DeriveEnumSuchThat/` — Examples of constrained enumerators
- `SpecimenTest/DeriveDecOpt/` — Examples of checkers
- `SpecimenTest/DeriveArbitrary/` — Examples of unconstrained generators
- `SpecimenTest/DeriveEnum/` — Examples of unconstrained enumerators
- `SpecimenTest/CedarExample/` — Real-world application: Cedar policy expression generation
- `SpecimenTest/ArithCompiler/` — End-to-end compiler correctness testing
- `README.md` — High-level overview
