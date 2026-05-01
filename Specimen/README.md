Specimen extends Plausible with automatic derivation of constrained generators, enumerators, and checkers for inductive relations. This document describes the available commands and how to use them.

## Overview of Commands

### 1. `derive_generator` - Constrained Random Generators

**Purpose**: Automatically derives a random generator that produces values satisfying an inductive relation.

**Syntax**:
```lean
derive_generator (fun x1 ... xn => ∃ x, P x1 ... x ... xn)
```

Where:
- `P` is an inductively defined relation
- `x` is the value to be generated (bound by `∃`)
- `x1 ... xn` are input parameters (bound by `fun`)

**Creates**: An instance of `ArbitrarySizedSuchThat` typeclass

**Example**:
```lean
-- Define an inductive relation for balanced trees
inductive balancedTree : Nat → BinaryTree → Prop where
  | B0 : balancedTree .zero BinaryTree.Leaf
  | B1 : balancedTree (.succ .zero) BinaryTree.Leaf
  | BS : ∀ n x l r,
    balancedTree n l → balancedTree n r →
    balancedTree (.succ n) (BinaryTree.Node x l r)

-- Derive a generator for balanced trees of height n
derive_generator (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Use the generator
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balancedTree 5 t)) 10
```

**More Examples**:
```lean
-- Generate BSTs between bounds
derive_generator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)

-- Generate well-typed STLC terms
derive_generator (fun Γ τ => ∃ (e : term), typing Γ e τ)

-- Generate strings matching a regex
derive_generator (fun re => ∃ (s : List Nat), ExpMatch s re)
```

### 2. `derive_enumerator` - Constrained Deterministic Enumerators

**Purpose**: Automatically derives a deterministic enumerator that systematically produces values satisfying an inductive relation.

**Syntax**: Same as `derive_generator`
```lean
derive_enumerator (fun x1 ... xn => ∃ x, P x1 ... x ... xn)
```

**Creates**: An instance of `EnumSizedSuchThat` typeclass

**Example**:
```lean
-- Derive an enumerator for balanced trees
derive_enumerator (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Use the enumerator (use smaller fuel to avoid stack overflow)
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balancedTree 3 t)) 3
```

**Key Difference from Generators**: Enumerators produce values deterministically in a systematic order, while generators produce random values. Enumerators are useful for exhaustive testing but require more fuel/memory.

### 3. `derive_checker` - Partial Decision Procedures

**Purpose**: Automatically derives a checker (partial decision procedure) for an inductive relation.

**Syntax**:
```lean
derive_checker (fun x1 ... xn => P x1 ... xn)
```

Where `P` is an inductively defined relation.

**Creates**: An instance of `DecOpt` typeclass

**Returns**: `Nat → Except GenError Bool` where:
- `.ok true` - the relation holds
- `.ok false` - the relation doesn't hold
- `.error _` - ran out of fuel, couldn't decide

**Example**:
```lean
-- Derive a checker for BST property
derive_checker (fun lo hi t => BST lo hi t)

-- Use the checker
let result := DecOpt.decOpt (BST 0 10 myTree) 100  -- 100 is fuel
match result with
| .ok true => IO.println "Is a BST!"
| .ok false => IO.println "Not a BST!"
| .error _ => IO.println "Couldn't decide (out of fuel)"
```

### 4. `deriving Arbitrary` - Unconstrained Random Generators

**Purpose**: Automatically derives an unconstrained random generator for an algebraic data type.

**Syntax**:
```lean
-- After type definition
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Arbitrary

-- Or as a separate command
deriving instance Arbitrary for Tree
```

**Creates**: An instance of `ArbitraryFueled` typeclass (from Plausible), which provides `Arbitrary`

**Example**:
```lean
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Arbitrary

-- Sample from the generator
#eval runArbitrary (α := Tree) 10
```

### 5. `deriving Enum` - Unconstrained Deterministic Enumerators

**Purpose**: Automatically derives an unconstrained deterministic enumerator for an algebraic data type.

**Syntax**:
```lean
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Enum

-- Or as a separate command
deriving instance Enum for Tree
```

**Creates**: An instance of `EnumSized` typeclass

**Example**:
```lean
deriving instance Enum for Tree

-- Enumerate trees
#eval runEnum (α := Tree) 5
```

## Typeclasses Created

| Command | Typeclass | Purpose |
|---------|-----------|---------|
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

## How to Use Derived Instances

### Using Constrained Generators

```lean
-- After deriving
derive_generator (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Method 1: Direct call with explicit size
#eval Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balancedTree 5 t) 10) 10

-- Method 2: Using runSizedGen helper
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balancedTree 5 t)) 10

-- Method 3: In property-based tests
def testProperty : IO Unit := do
  let t ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => BST 0 10 t) 10) 10
  -- test property on t
  pure ()
```

### Using Constrained Enumerators

```lean
derive_enumerator (fun n => ∃ (t : BinaryTree), balancedTree n t)

-- Enumerate with fuel parameter (use smaller values to avoid stack overflow)
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balancedTree 3 t)) 3
```

### Using Checkers

```lean
derive_checker (fun lo hi t => BST lo hi t)

-- Check if a tree satisfies BST property
let isValid := DecOpt.decOpt (BST 0 10 myTree) 100  -- 100 is fuel
```

### Using Unconstrained Generators

```lean
deriving instance Arbitrary for Tree

-- Method 1: Direct sampling
#eval runArbitrary (α := Tree) 10

-- Method 2: In Gen monad
let tree ← Arbitrary.arbitrary (α := Tree)

-- Method 3: With plausible tactic (automatic)
example (t : Tree) : mirror (mirror t) = t := by
  plausible  -- automatically uses Arbitrary Tree instance
```

## Common Patterns

### Testing Properties with Derived Generators

```lean
-- Derive generator for valid inputs
derive_generator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)

-- Derive checker for output validation
derive_checker (fun lo hi t => BST lo hi t)

-- Test a function
def testInsert (numTrials : Nat) : IO Unit := do
  for _ in [:numTrials] do
    let x ← Gen.run (Gen.chooseNat) 10
    let t ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => BST 0 10 t) 10) 10
    let t' := insert x t
    let isValid := DecOpt.decOpt (BST 0 10 t') 100
    match isValid with
    | .ok true => continue
    | .ok false => IO.println s!"Property violated! x={x}, t={t}"
    | .error _ => IO.println "Checker ran out of fuel"
```

### Combining Multiple Relations

```lean
-- Generate values satisfying multiple constraints
derive_generator (fun n => ∃ (t : BinaryTree), balancedTree n t)
derive_checker (fun lo hi t => BST lo hi t)

-- Generate balanced tree and check if it's also a BST
let t ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balancedTree 5 t) 10) 10
let isBST := DecOpt.decOpt (BST 0 100 t) 100
```

## Requirements

For successful derivation, ensure:

1. **For `derive_generator` / `derive_enumerator`**:
   - The relation `P` must be inductively defined
   - Input types must have `Arbitrary` instances (for generators) or `Enum` instances (for enumerators)
   - The relation should be well-formed (see limitations below)

2. **For `derive_checker`**:
   - The relation must be inductively defined
   - All types involved must have decidable equality when needed

3. **For `deriving Arbitrary` / `deriving Enum`**:
   - The type must be an inductive type
   - Must have at least one non-recursive constructor (for termination)
   - Constituent types must have `Arbitrary` / `Enum` instances

## Limitations

1. **Pattern matching**: Currently expects variable names in lambda positions, not literals
2. **Mutually recursive relations**: Require manual instance stubs (see `MutuallyRecursiveRelationsTest.lean`)
3. **Enumerator fuel**: Enumerators can stack overflow with large fuel values; use smaller values (3-5)
4. **Checker fuel**: Checkers may return an error if they run out of fuel on complex relations

## See Also

- `SpecimenTest/DeriveArbitrarySuchThat/` - Examples of constrained generators
- `SpecimenTest/DeriveEnumSuchThat/` - Examples of constrained enumerators
- `SpecimenTest/DeriveDecOpt/` - Examples of checkers
- `SpecimenTest/DeriveArbitrary/` - Examples of unconstrained generators
- `SpecimenTest/DeriveEnum/` - Examples of unconstrained enumerators
- `README.md` - High-level overview
- `Specimen/README.md` - this file; detailed command overview