# Deriving generators against Basalt

Specimen can emit derived **generators** against [Basalt](https://github.com/hgoldstein95/basalt/)'s
generator algebra instead of `Plausible.Gen`. The body of such a generator is polymorphic in Basalt's
`Gen` class, so one derived term elaborates at every `Gen` instance: `Plausible.Gen` to run it, and
Basalt's semantic instances to reason about it. Behind the option `specimen.emitBasalt`, off by
default.

What changes is only the emitted code. The commands (`derive_generator`, `derive_mutual`, the
`specimen` tactics) are the same, and a Basalt-derived generator runs wherever an
`ArbitrarySizedSuchThat` is expected. `derive_mutual enumerator` is emitted the same way (§6); checkers
and the older `derive_enumerator` command are not affected.

## Contents

1. Using it
2. The Basalt API the emitter targets
3. What is emitted
4. Running Basalt generators through Plausible
5. Unconstrained values: `deriving instance Basalt.ArbitrarySized`
6. Enumerators
7. Constraints and pitfalls
8. Not done

---

## 1. Using it

```lean
import Specimen
import Specimen.Basalt

set_option specimen.emitBasalt true

derive_generator (fun τ => ∃ e, HasType e τ)
```

- **`import Specimen.Basalt`** is required in any file that derives generators under the flag. It
  brings Basalt's classes and Specimen's lookup classes (the emitted code names them), the bridge back to `ArbitrarySizedSuchThat`
  (§4) and the `Basalt.ArbitrarySized` deriving handler (§5). It is not part of `import Specimen`,
  because Basalt keeps `Gen` at the root namespace, where it is ambiguous with `Plausible.Gen` in any
  file with `open Plausible`. With the flag on and the import missing, deriving stops with an error
  naming the import.
- **Dependency.** Specimen requires `basalt`, which requires Mathlib. So Mathlib is cloned and a few GB
  of prebuilt artefacts downloaded, by `lake exe cache get` (`lake update` runs it). It is never built
  from source or elaborated into Specimen: the only Basalt modules Specimen imports are the generation
  ones (`Gen`, `RandomChoice`, the combinators, `OptionT`, the Plausible `Gen` instance), and
  those import no Mathlib.
- **Set the flag for a whole library, not per file** (§7.1):

  ```toml
  [[lean_lib]]
  name = "MyLib"
  leanOptions = { weak.specimen.emitBasalt = true }
  ```

  For a single file on the command line: `lake env lean -Dweak.specimen.emitBasalt=true File.lean`
  (no space after `-D`).

## 2. The Basalt API the emitter targets

From Basalt's `Gen`, Specimen's `Specimen.Enum` (the choice and failure classes, hosted in Specimen
until Basalt has a stable API for them) and `Specimen.BasaltClasses`:

```lean
class Gen (g : Type u → Type v)            -- Monad, RandomChoice, Inhabited, CCPO, MonoBind
class Specimen.Fail (G : Type → Type) where fail : G α               -- a refutation
class Specimen.FailWith (ε : Type) (G : Type → Type) where failWith : ε → G α   -- not a refutation
class Specimen.Backtrack (G : Type → Type) where
  backtrack : List (Nat × (Unit → G α)) → G α
class Specimen.MonoBacktrack (G) [Backtrack G] [∀ α, PartialOrder (G α)]   -- for partial_fixpoint

-- Specimen
inductive Specimen.Exhaustion where | fuel | truncated | inconclusive

class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G] [Fail G] [FailWith Specimen.Exhaustion G] [Backtrack G]
    [MonoBacktrack G] [Pick G], Nat → G α

namespace Basalt
class Arbitrary (α : Type) where
  arbitrary : ∀ {G : Type → Type} [Gen G], G α
class ArbitrarySized (α : Type) where
  arbitrarySized : ∀ {G : Type → Type} [Gen G] [Pick G], Nat → G α
end Basalt
```

- **Failure is part of the monad, in two kinds.** `Fail.fail` says the rule does not apply;
  `FailWith.failWith e` says the search gave up without deciding, and why. Plausible's generators throw
  one `GenError` for both and tell them apart by its message.
- **`backtrack`** picks a branch by weight, runs it, and on either failure drops it and picks again
  among the rest. Branches are functions, so only those tried are built. What it means depends on the
  interpretation: the search itself when sampling, the union of the branches at an enumeration
  (`Specimen.Enum.Backtrack`'s docstring, and its laws in `Specimen.Enum.Laws`).
- **`BacktrackGenFor α P`** is the counterpart of `ArbitrarySizedSuchThat α P`, polymorphic in `G`.
- **`Basalt.Arbitrary` / `Basalt.ArbitrarySized`** are the counterparts of Plausible's
  unconstrained classes; a blanket instance gives `ArbitrarySized` from `Arbitrary`. Basalt has no
  lookup classes of its own, so these and `BacktrackGenFor` are Specimen's. `ArbitrarySized`'s base
  instances (`Nat`, `Bool`, `Int`, `Char`, `String`, `Fin`, and `List`, `Option`, `Prod` and `Sum` of
  them) are bounded by the size as Plausible's are by its ambient size, so the same instance serves a
  generator and an enumeration.
- **`pick`** is a weighted choice without retry, taking the proof that some weight is positive; it
  runs where nothing fails (`Plausible.Gen`, `SPMF`) as `frequency`, and at an enumeration lists each
  branch once. `pickOr` is the choice whose weights may all be `0`.

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
    let rec aux_arb {G : Type → Type} [_root_.Gen G] [Specimen.Fail G]
        [Specimen.FailWith Specimen.Exhaustion G] [Specimen.Backtrack G] [Specimen.MonoBacktrack G]
        [Specimen.Pick G] (fuel initSize size : Nat) (τ : Ty) : G Expr :=
      match fuel with
      | 0 => Specimen.outOfFuel
      | fuel' + 1 =>
        match size with
        | 0 => Specimen.Backtrack.backtrack
            [ …,   -- the non-recursive constructors, as below
             (1, fun (_ : Unit) => match τ with      -- `add`, cut off where it would apply
                | .nat => Specimen.truncated
                | _ => Specimen.refute)]
        | size' + 1 =>
          Specimen.Backtrack.backtrack
            [(4, fun (_ : Unit) => match τ with
                | .nat => do
                  let n ← Basalt.ArbitrarySized.arbitrarySized initSize
                  return Expr.lit n
                | _ => Specimen.refute),
             (4, fun (_ : Unit) => match τ with
                | .bool => do
                  let n ← Basalt.ArbitrarySized.arbitrarySized initSize
                  match DecOpt.negOpt (DecOpt.decOpt (n = 0) initSize) with
                  | .ok true => return Expr.isPos n
                  | .ok false => Specimen.refute
                  | _ => Specimen.inconclusive
                | _ => Specimen.refute),
             (…, fun (_ : Unit) => match τ with
                | .nat => do
                  let l ← aux_arb fuel' initSize size' .nat
                  let r ← aux_arb fuel' initSize size' .nat
                  return Expr.add l r
                | _ => Specimen.refute)]
    fun size leafSize => aux_arb 10000 leafSize size τ
```

Compared with the Plausible output, the size and fuel structure, weights, schedule and dispatch guards
are identical. What changes:

| Plausible path | Basalt path |
|---|---|
| `instance : ArbitrarySizedSuchThat …`, field `arbitrarySizedST` | `instance : BacktrackGenFor …`, field `gen` |
| worker returns `Plausible.Gen α` | worker binds `{G} [Gen G] [Fail G] [FailWith Exhaustion G] [Backtrack G] [MonoBacktrack G] [Pick G]`, returns `G α` |
| one size; leaves read Plausible's ambient size | two, the search's `size` and the leaf size `initSize`; the bridge (§4) passes the ambient size as the leaf size |
| `GeneratorCombinators.backtrack [(w, b), …]` | `Specimen.Backtrack.backtrack [(w, fun (_ : Unit) => b), …]` |
| `throw Gen.genericFailure` | `Specimen.refute` (`Fail.fail`) |
| `throw Gen.outOfFuelError` (fuel 0) | `Specimen.outOfFuel` (`failWith .fuel`) |
| `DecOpt` premise: anything but `ok true` throws | `ok false` → `refute`, error → `inconclusive` |
| size 0 list as is | each recursive constructor as its conclusion match, then `Specimen.truncated` |
| `Arbitrary.arbitrary` | `Basalt.ArbitrarySized.arbitrarySized initSize` |
| `ArbitrarySizedSuchThat.arbitrarySizedST P n` | `BacktrackGenFor.gen P n initSize` |
| type parameter binder `[Plausible.Arbitrary α]` | `[Basalt.ArbitrarySized α]` |

Notes:

- **Branches are `fun (_ : Unit) => …`**, with the binder type written out: under input dispatch a
  branch sits inside `List.filterMap` with no expected type, and `fun () =>` there leaves a universe
  constraint unsolved.
- **`_root_.Gen`.** Derived code lands in the user's file, where `open Plausible` is common, and a bare
  `Gen` there is ambiguous. The rest are written qualified.
- **The `G` binder sits on the inner function.** A `let rec` is lifted to a top-level declaration and
  cannot capture a binder from an enclosing lambda; `derive_mutual`'s definitions each carry their own
  `{G}`, which unify at the call sites.
- **`refute` vs `inconclusive` at a `DecOpt` premise.** `ok false` says the constructor does not
  apply; an error only says the checker ran out of budget. Collapsing the second into `refute` would let
  `backtrack` report a refutation for an inhabited relation.
- **At size 0** a recursive constructor cannot recurse, so it is offered only as its conclusion: the
  leading input matches and input-only checks of its schedule, then `Specimen.truncated` where they
  match. A search that only meets refutations and truncations ends truncated if some recursive
  constructor could have applied, and refuted if none could, which is a genuine refutation. The
  branch has weight `1`, since a recursive constructor's own weight is `0` at size 0 and a branch of
  weight `0` is never tried. `backtrack` retries past a truncation, so the successes are unchanged.
- **Unconstrained values use the sized class, at the leaf size `initSize`**, which is passed unchanged
  while the search's `size` is split: `Gen` has no ambient size, so the leaf size Plausible's leaves
  read from it is an argument instead. Constrained dependencies on other relations get the leaf size
  too.
- **The `specimen_test` theorem checker stays on the Plausible path** with the flag on: it runs in
  `Plausible.Gen` and calls generators through `ArbitrarySizedSuchThat`, which the bridge (§4)
  supplies for Basalt-derived ones.

## 4. Running Basalt generators through Plausible

`Specimen.BasaltBridge` has one blanket instance:

```lean
abbrev Specimen.BasaltSampler := ExceptT Exhaustion (OptionT Plausible.Gen)

instance (priority := low) [BacktrackGenFor α P] : ArbitrarySizedSuchThat α P where
  arbitrarySizedST size :=
    (BacktrackGenFor.gen (P := P) (G := Specimen.BasaltSampler) size).toPlausibleGen
```

So every consumer of `ArbitrarySizedSuchThat` (the `plausible` tactic, `specimen_test`,
`printSamples`, generators derived with the flag off) runs a Basalt-derived generator unchanged.
At `BasaltSampler` a refutation is `none` and a labelled failure an `.error`, and the `Backtrack`
instance for it is the search, retrying past both. `toPlausibleGen` throws
`Gen.genericFailure` for a refutation and Plausible's `"out of fuel"` error for a labelled failure, which `Gen.GenError.isInconclusive` classifies as inconclusive, so the distinction
survives the boundary as a message. Low priority, so a hand-written `ArbitrarySizedSuchThat` for the
same relation still wins.

The module also has the equality leaves the Basalt path needs (`x = e`, `e = x`, and a pair
`l = r`), mirroring Specimen's `ArbitrarySizedSuchThat` ones. It also gives
`Plausible.Arbitrary` from `Basalt.Arbitrary` and `Plausible.ArbitraryFueled` from
`Basalt.ArbitrarySized`, also at low priority.

There is no bridge the other way, and cannot be: a single `Plausible.Gen α` does not give a
`∀ {G} [Gen G], G α`. This one-way street is the source of most of §7.

## 5. Unconstrained values: `deriving instance Basalt.ArbitrarySized`

When a Basalt-derived generator needs an unconstrained value of a datatype, it asks for
`Basalt.ArbitrarySized`, and the datatype's `Plausible.Arbitrary` cannot stand in. The handler in
`Specimen.DeriveBasaltArbitrary` derives one:

```lean
deriving instance Basalt.ArbitrarySized for Tree
```

emits

```lean
def Tree.basaltArbitrarySized {G : Type → Type} [_root_.Gen G] [Specimen.Pick G] : Nat → G Tree
  | 0     => oneOf [fun (_ : Unit) => pure Tree.leaf]
  | n + 1 => oneOf [fun (_ : Unit) => pure Tree.leaf,
                    fun (_ : Unit) => Tree.basaltArbitrarySized n >>= fun a0 => … pure (Tree.node a0 a1 a2)]

instance : Basalt.ArbitrarySized Tree where
  arbitrarySized := Tree.basaltArbitrarySized
```

Uniform over the non-recursive constructors at fuel 0 and all constructors otherwise. A field is
generated by the recursive call at one less fuel, else by `Basalt.ArbitrarySized` at the same fuel if
an instance exists, else by `Basalt.Arbitrary`. Type parameters are supported. Indexed families,
nested occurrences (`List T` inside `T`) and fields whose type depends on an earlier field
(`bitvecConst (n : Nat) (b : BitVec n)`) are rejected with an error naming the field; write those
instances by hand.

## 6. Enumerators

Under the flag, `derive_mutual enumerator` emits the generator's code shape over the same classes, from
the enumerator's own schedules. It is registered as `EnumFor α P` rather than `BacktrackGenFor`, and
draws unconstrained values from `Basalt.ArbitrarySized`, as a generator does.

An enumerator is read at `ExceptT Exhaustion Finite`: everything up to the size, with truncation and
out-of-fuel as labels. `Specimen.BasaltBridge` serves `EnumSizedSuchThat` from `EnumFor` and `Enum` from
`Basalt.ArbitrarySized` at that reading, which is how a derived checker draws its premises; checkers themselves
stay on `DecOpt`. The law that the reading lists exactly what the sampler can succeed with
(`EnumeratesWith`) is walked for a derived enumerator in `SpecimenTest/Correctness/DerivedEnumLaw.lean`.

`derive_enumerator`, the single-relation command `derive_mutual` superseded, ignores the flag and emits
the lazy-list enumerator.

## 7. Constraints and pitfalls

### 7.1 The flag must be set for a whole import closure

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

### 7.2 Every datatype needs its own `Basalt.ArbitrarySized`

Each datatype a Basalt-derived generator draws unconstrained values of needs
`deriving instance Basalt.ArbitrarySized for T`. A missing one is a synthesis error naming the class.

**Curated instances are the silent case.** A file that overrides `Arbitrary String` with a small pool,
so that generated keys collide, still generates on the Basalt path without its counterpart, but from
Basalt's own `Arbitrary String` (random printable ASCII): every key-lookup premise then takes its
trivial branch, and the only symptom is worse test data. When porting a file, give every hand-written
`Arbitrary` / `ArbitraryFueled` instance a `Basalt.ArbitrarySized` twin, not just the datatypes that
fail. Declare such pools `local`: a global one is seen by every module importing the file, and two of
them for the same type make generation depend on which one instance resolution picks.

Deriving these instances implicitly inside `derive_generator` does not work: an instance is a global
declaration, so two modules each deriving a relation over the same datatype would each declare one,
and nothing importing both would compile.

### 7.3 Seed statistical tests

The two paths draw from the same primitive (`RandomChoice Plausible.Gen` is `Gen.choose`) and run the
same `backtrack` algorithm. They differ in one respect: a failed Plausible branch throws, and since
Plausible's `Gen` is `StateT StdGen` under `Except`, the RNG rolls back; a failed Basalt branch is a
value of the `OptionT`/`ExceptT` layers above it and keeps the randomness it consumed. This has had no measurable effect on generation quality,
but comparing the paths with unseeded runs showed differences in both directions from run to run. Use
`Gen.sampleWithSeed` (one seeded stream, not a seed per iteration: `mkStdGen` on consecutive seeds
correlates the first draw, which picks the top-level constructor).

### 7.4 Rebuild after flipping the flag

Lake has replayed cached test modules across a flag change, reporting results for the configuration
before the flip. A replayed module shows as `Replayed …` in the log. If in doubt, remove
`.lake/build/lib/lean/<Lib>` and `.lake/build/ir/<Lib>` before trusting a flag-on result.

## 8. Not done

- **Checkers** keep `DecOpt`. A checker interface with run, specification and expense readings is
  separate work.
- **Soundness and completeness of derived generators** against their relation. The enumeration law
  above relates two readings of one derived term; stating either against the relation is not done.
- **The `Basalt.ArbitrarySized` requirement** is manual (§7.2). A better error at the point of the
  synthesis failure, naming the `deriving` line to add, is the realistic improvement.
- **Packaging.** `basalt` is pinned to `hgoldstein95/basalt#35` (a fix to `walk fixpoint` the laws in
  `Specimen.Enum.Laws` need), until it is merged; then to `main`.
