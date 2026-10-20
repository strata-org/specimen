# Deriving generators against Basalt

Specimen can emit derived **generators** against [Basalt](https://github.com/hgoldstein95/basalt/)'s
generator algebra instead of `Plausible.Gen`. The body of such a generator is polymorphic in Basalt's
`Gen` class, so one derived term elaborates at every `Gen` instance: `Plausible.Gen` to run it, and
Basalt's semantic instances to reason about it. Behind the option `specimen.emitBasalt`, off by
default.

What changes is only the emitted code. The commands (`derive_generator`, `derive_mutual`, the
`specimen` tactics) are the same, and a Basalt-derived generator runs wherever an
`ArbitrarySizedSuchThat` is expected. Enumerators and checkers are not affected.

## Contents

1. Using it
2. The Basalt API the emitter targets
3. What is emitted
4. Running Basalt generators through Plausible
5. Unconstrained values: `deriving instance Basalt.ArbitraryFueled`
6. Constraints and pitfalls
7. Not done

---

## 1. Using it

```lean
import Specimen
import Specimen.Basalt

set_option specimen.emitBasalt true

derive_generator (fun τ => ∃ e, HasType e τ)
```

- **`import Specimen.Basalt`** is required in any file that derives generators under the flag. It
  brings Basalt's classes (the emitted code names them), the bridge back to `ArbitrarySizedSuchThat`
  (§4) and the `Basalt.ArbitraryFueled` deriving handler (§5). It is not part of `import Specimen`,
  because Basalt keeps `Gen` at the root namespace, where it is ambiguous with `Plausible.Gen` in any
  file with `open Plausible`. With the flag on and the import missing, deriving stops with an error
  naming the import.
- **Dependency.** Specimen requires `basalt`, which requires Mathlib. So Mathlib is cloned and a few GB
  of prebuilt artefacts downloaded, by `lake exe cache get` (`lake update` runs it). It is never built
  from source or elaborated into Specimen: the only Basalt modules Specimen imports are the generation
  ones (`Gen`, `RandomChoice`, the combinators, `BacktrackGen`, `Arbitrary`, the Plausible bridge), and
  those import no Mathlib.
- **Set the flag for a whole library, not per file** (§6.1):

  ```toml
  [[lean_lib]]
  name = "MyLib"
  leanOptions = { weak.specimen.emitBasalt = true }
  ```

  For a single file on the command line: `lake env lean -Dweak.specimen.emitBasalt=true File.lean`
  (no space after `-D`).

## 2. The Basalt API the emitter targets

From `Basalt/Gen.lean`, `Basalt/BacktrackGen.lean` and `Basalt/Arbitrary.lean`:

```lean
class Gen (g : Type u → Type v)            -- Monad, RandomChoice, Inhabited, CCPO, MonoBind

inductive Outcome (α : Type) where
  | ok (a : α) | refuted | exhausted

abbrev BacktrackGen (G : Type → Type) (α : Type) := Producer .gen G α   -- run : G (Outcome α)

def BacktrackGen.backtrack (gs : List (Nat × (Unit → BacktrackGen G α))) : BacktrackGen G α
-- also: liftGen, refute, exhaust, refutedToExhausted

class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G], Nat → BacktrackGen G α

namespace Basalt
class Arbitrary (α : Type) where
  arbitrary : ∀ {G : Type → Type} [Gen G], G α
class ArbitraryFueled (α : Type) where
  arbitraryFueled : ∀ {G : Type → Type} [Gen G], Nat → G α
end Basalt
```

- **Failure is a value.** `BacktrackGen G α` produces an `Outcome`: a definite refutation and an
  exhausted budget are different constructors, where Plausible's generators throw one `GenError` for
  both and tell them apart by its message.
- **`backtrack`** picks a branch by weight, runs it, and on failure drops it and picks again among the
  rest; it is `refuted` only if every branch refuted, `exhausted` if any branch exhausted. Branches
  are functions, so only those tried are built. It is the same algorithm as Specimen's
  `GeneratorCombinators.backtrack`.
- **`BacktrackGenFor α P`** is the counterpart of `ArbitrarySizedSuchThat α P`, polymorphic in `G`.
- **`Basalt.Arbitrary` / `Basalt.ArbitraryFueled`** are the counterparts of Plausible's
  unconstrained classes; a blanket instance gives `ArbitraryFueled` from `Arbitrary`.

## 3. What is emitted

Running example:

```lean
inductive HasType : Expr → Ty → Prop
  | lit (n) : HasType (.lit n) .nat
  | isPos (n) : n ≠ 0 → HasType (.isPos n) .bool
  | add (l r) : HasType l .nat → HasType r .nat → HasType (.add l r) .nat

derive_generator (fun τ => ∃ e, HasType e τ)
```

Under the flag (abridged: the `size + 1` case, without the input-dispatch guards):

```lean
instance : BacktrackGenFor Expr (fun e => HasType e τ) where
  gen :=
    let rec aux_arb {G : Type → Type} [_root_.Gen G] (fuel initSize size : Nat) (τ : Ty) :
        BacktrackGen G Expr :=
      match fuel with
      | 0 => BacktrackGen.exhaust
      | fuel' + 1 =>
        match size with
        | 0 => BacktrackGen.refutedToExhausted (BacktrackGen.backtrack [ … ])
        | size' + 1 =>
          BacktrackGen.backtrack
            [(4, fun (_ : Unit) => match τ with
                | .nat => do
                  let n ← BacktrackGen.liftGen (Basalt.ArbitraryFueled.arbitraryFueled initSize)
                  return Expr.lit n
                | _ => BacktrackGen.refute),
             (4, fun (_ : Unit) => match τ with
                | .bool => do
                  let n ← BacktrackGen.liftGen (Basalt.ArbitraryFueled.arbitraryFueled initSize)
                  match DecOpt.negOpt (DecOpt.decOpt (n = 0) initSize) with
                  | .ok true => return Expr.isPos n
                  | .ok false => BacktrackGen.refute
                  | _ => BacktrackGen.exhaust
                | _ => BacktrackGen.refute),
             (…, fun (_ : Unit) => match τ with
                | .nat => do
                  let l ← aux_arb fuel' initSize size' .nat
                  let r ← aux_arb fuel' initSize size' .nat
                  return Expr.add l r
                | _ => BacktrackGen.refute)]
    fun size => aux_arb 10000 size size τ
```

Compared with the Plausible output, the size and fuel structure, weights, schedule and dispatch guards
are identical. What changes:

| Plausible path | Basalt path |
|---|---|
| `instance : ArbitrarySizedSuchThat …`, field `arbitrarySizedST` | `instance : BacktrackGenFor …`, field `gen` |
| worker returns `Plausible.Gen α` | worker binds `{G} [_root_.Gen G]`, returns `BacktrackGen G α` |
| `GeneratorCombinators.backtrack [(w, b), …]` | `BacktrackGen.backtrack [(w, fun (_ : Unit) => b), …]` |
| `throw Gen.genericFailure` | `BacktrackGen.refute` |
| `throw Gen.outOfFuelError` (fuel 0) | `BacktrackGen.exhaust` |
| `DecOpt` premise: anything but `ok true` throws | `ok false` → `refute`, error → `exhaust` |
| size 0 list as is | `refutedToExhausted` around it when recursive constructors are withheld |
| `Arbitrary.arbitrary` | `BacktrackGen.liftGen (Basalt.ArbitraryFueled.arbitraryFueled initSize)` |
| `ArbitrarySizedSuchThat.arbitrarySizedST P n` | `BacktrackGenFor.gen P n` |
| type parameter binder `[Plausible.Arbitrary α]` | `[Basalt.ArbitraryFueled α]` |

Notes:

- **Branches are `fun (_ : Unit) => …`**, with the binder type written out: under input dispatch a
  branch sits inside `List.filterMap` with no expected type, and `fun () =>` there leaves a universe
  constraint unsolved.
- **`_root_.Gen`.** Derived code lands in the user's file, where `open Plausible` is common, and a bare
  `Gen` there is ambiguous. The other names are unambiguous as emitted.
- **The `G` binder sits on the inner function.** A `let rec` is lifted to a top-level declaration and
  cannot capture a binder from an enclosing lambda; `derive_mutual`'s definitions each carry their own
  `{G}`, which unify at the call sites.
- **`refute` vs `exhaust` at a `DecOpt` premise.** `ok false` says the constructor does not apply;
  an error only says the checker ran out of budget. Collapsing the second into `refute` would let
  `backtrack` report `refuted` for an inhabited relation.
- **At size 0** only the non-recursive constructors are offered, so their failing is not a refutation
  of the relation; `refutedToExhausted` downgrades it. For a relation with no recursive constructors the
  size-0 list is complete and stays as is.
- **Unconstrained values use the fueled class**, at `initSize`: a derived datatype only ever has
  `Basalt.ArbitraryFueled` (§5), and Basalt's `Gen` has no ambient size from which an unfueled
  generator could take one.
- **The `specimen_test` theorem checker stays on the Plausible path** with the flag on: it runs in
  `Plausible.Gen` and calls generators through `ArbitrarySizedSuchThat`, which the bridge (§4)
  supplies for Basalt-derived ones.

## 4. Running Basalt generators through Plausible

`Specimen.BasaltBridge` has one blanket instance:

```lean
instance (priority := low) [BacktrackGenFor α P] : ArbitrarySizedSuchThat α P where
  arbitrarySizedST size :=
    BacktrackGen.toPlausibleGen (BacktrackGenFor.gen (P := P) (G := Plausible.Gen) size)
```

So every consumer of `ArbitrarySizedSuchThat` (the `plausible` tactic, `specimen_test`,
`printSamples`, generators derived with the flag off) runs a Basalt-derived generator unchanged.
`toPlausibleGen` throws `Gen.genericFailure` for `refuted` and Plausible's `"out of fuel"` error for
`exhausted`, which `Gen.GenError.isInconclusive` classifies as inconclusive, so the distinction
survives the boundary as a message. Low priority, so a hand-written `ArbitrarySizedSuchThat` for the
same relation still wins.

The module also has the equality leaves the Basalt path needs (`x = e`, `e = x`, and a pair
`l = r`), mirroring Specimen's `ArbitrarySizedSuchThat` ones. Basalt's own `PlausibleBridge` gives
`Plausible.Arbitrary` from `Basalt.Arbitrary` and `Plausible.ArbitraryFueled` from
`Basalt.ArbitraryFueled`, also at low priority.

There is no bridge the other way, and cannot be: a single `Plausible.Gen α` does not give a
`∀ {G} [Gen G], G α`. This one-way street is the source of most of §6.

## 5. Unconstrained values: `deriving instance Basalt.ArbitraryFueled`

When a Basalt-derived generator needs an unconstrained value of a datatype, it asks for
`Basalt.ArbitraryFueled`, and the datatype's `Plausible.Arbitrary` cannot stand in. The handler in
`Specimen.DeriveBasaltArbitrary` derives one:

```lean
deriving instance Basalt.ArbitraryFueled for Tree
```

emits

```lean
def Tree.basaltArbitraryFueled {G : Type → Type} [_root_.Gen G] : Nat → G Tree
  | 0     => oneOf [fun (_ : Unit) => pure Tree.leaf]
  | n + 1 => oneOf [fun (_ : Unit) => pure Tree.leaf,
                    fun (_ : Unit) => Tree.basaltArbitraryFueled n >>= fun a0 => … pure (Tree.node a0 a1 a2)]

instance : Basalt.ArbitraryFueled Tree where
  arbitraryFueled := Tree.basaltArbitraryFueled
```

Uniform over the non-recursive constructors at fuel 0 and all constructors otherwise. A field is
generated by the recursive call at one less fuel, else by `Basalt.ArbitraryFueled` at the same fuel if
an instance exists, else by `Basalt.Arbitrary`. Type parameters are supported. Indexed families,
nested occurrences (`List T` inside `T`) and fields whose type depends on an earlier field
(`bitvecConst (n : Nat) (b : BitVec n)`) are rejected with an error naming the field; write those
instances by hand.

## 6. Constraints and pitfalls

### 6.1 The flag must be set for a whole import closure

If module `A` derives an instance with the flag off and module `B` uses it with the flag on, `B` fails
with `failed to synthesize BacktrackGenFor …` for an instance that visibly exists in `A`: `A`
registered an `ArbitrarySizedSuchThat`, and there is no bridge from it to `BacktrackGenFor` (§4). Hence
the library-level `leanOptions` in §1. The `weak.` prefix is required there because Lake passes the
option to every module of the library, including those that never import `Specimen`, which would
otherwise fail with `unknown configuration option`.

For the same reason, setting the flag inside one file only tests that file against imports compiled
without it. To compare the two paths on an example, build both ways and compare against the flag-off
result before attributing a failure to the flag.

A hand-written constrained producer that has to serve both paths needs both instances: the
`ArbitrarySizedSuchThat` one for the Plausible path, a `BacktrackGenFor` twin for the Basalt path.
(Writing only the `BacktrackGenFor` one also serves both, through the bridge, but then the Plausible
path runs the bridge rather than the instance as written.)

### 6.2 Every datatype needs its own `Basalt.ArbitraryFueled`

Each datatype a Basalt-derived generator draws unconstrained values of needs
`deriving instance Basalt.ArbitraryFueled for T`. A missing one is a synthesis error naming the class.

**Curated instances are the silent case.** A file that overrides `Arbitrary String` with a small pool,
so that generated keys collide, still generates on the Basalt path without its counterpart, but from
Basalt's own `Arbitrary String` (random printable ASCII): every key-lookup premise then takes its
trivial branch, and the only symptom is worse test data. When porting a file, give every hand-written
`Arbitrary` / `ArbitraryFueled` instance a `Basalt.ArbitraryFueled` twin, not just the datatypes that
fail. Declare such pools `local`: a global one is seen by every module importing the file, and two of
them for the same type make generation depend on which one instance resolution picks.

Deriving these instances implicitly inside `derive_generator` does not work: an instance is a global
declaration, so two modules each deriving a relation over the same datatype would each declare one,
and nothing importing both would compile.

### 6.3 Seed statistical tests

The two paths draw from the same primitive (`RandomChoice Plausible.Gen` is `Gen.choose`) and run the
same `backtrack` algorithm. They differ in one respect: a failed Plausible branch throws, and since
Plausible's `Gen` is `StateT StdGen` under `Except`, the RNG rolls back; a failed Basalt branch returns
a value and keeps the randomness it consumed. This has had no measurable effect on generation quality,
but comparing the paths with unseeded runs showed differences in both directions from run to run. Use
`Gen.sampleWithSeed` (one seeded stream, not a seed per iteration: `mkStdGen` on consecutive seeds
correlates the first draw, which picks the top-level constructor).

### 6.4 Rebuild after flipping the flag

Lake has replayed cached test modules across a flag change, reporting results for the configuration
before the flip. A replayed module shows as `Replayed …` in the log. If in doubt, remove
`.lake/build/lib/lean/<Lib>` and `.lake/build/ir/<Lib>` before trusting a flag-on result.

## 7. Not done

- **Enumerators and checkers** keep their own types. They are structurally recursive over fuel and want
  a different algebra.
- **Proofs about derived generators.** The point of a `G`-polymorphic body is that it can be
  interpreted at a semantic `Gen` instance to state soundness and completeness; nothing here does that
  yet.
- **The `Basalt.ArbitraryFueled` requirement** is manual (§6.2). A better error at the point of the
  synthesis failure, naming the `deriving` line to add, is the realistic improvement.
- **Packaging.** `basalt` is required by local path until Specimen's additions to it are merged upstream.
