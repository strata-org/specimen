# Structure-parameterized output types in the constrained deriver

## 1. What this supports

`derive_generator` / `derive_enumerator` / `derive_mutual` can produce values of
an inductive relation whose output type is parameterized by a **structure** `P`
(not just a plain `Sort`/type parameter), with `P` kept **abstract** (no
monomorphization).

The motivating case is Strata's Lambda IR, where a single structure parameter
bundles the language's configuration types:

```lean
inductive LExpr (T : LExprParamsT) : Type where
  | const (m : T.base.Metadata) (c : LConst)
  | bvar  (m : T.base.Metadata) (i : Nat)
  | ...
```

Here `T : LExprParams` is a structure bundling the metadata / identifier /
type-annotation types. Deriving a producer for a relation like
`@LExpr.HasTypeA T …` requires handling three things about `T`:

1. **The parameter appears as an implicit constructor argument.** `T.mono`
   rides along as an implicit argument of every `LExpr` constructor. It is
   determined entirely by the producer's inputs and has no `Arbitrary` instance
   (and typically lives in a higher universe than the value being generated), so
   it must **not** be lifted into a generated unknown.
2. **Constructor fields have projection types.** Fields like
   `m : T.base.Metadata` or `name : T.VarId` can only be produced if an
   `Arbitrary`/`Enum` instance for that projection type is in scope. The derived
   instance must carry the matching binders (e.g. `[Arbitrary T.base.Metadata]`).
3. **Implicit args must be re-inferred, not placed positionally.** The produced
   value must omit implicit constructor arguments (like the `T` of
   `LExpr.const`) so Lean re-infers them from the explicit arguments.

**Design invariant — strictly additive.** None of this changes behavior when no
structure parameter is involved. Ordinary fixed value subterms that *do* have an
`Arbitrary` instance (e.g. `n * n : Nat`) still flatten as before; plain `Sort`
parameters are unaffected.

## 2. Implementation

Three parts of the pipeline cooperate. All are guarded so the non-struct path is
unchanged.

### 2a. Don't generate fixed, ungeneratable subterms

*Files: `Specimen/Utils.lean`, `Specimen/DeriveConstrainedProducer.lean`.*

Conclusion flattening (`collectUnmatchableSubterms` /
`collectUnmatchableProperSubterms`) normally turns non-matchable subterms into
fresh generated unknowns plus equality hypotheses. A set of **fixed-input
fvars** is threaded through these collectors, and a subterm that is *fixed and
ungeneratable* is left in place instead:

- `allFVarsFixed fixed e` — every free variable of `e` is a fixed input, so `e`
  is fully determined by the producer's inputs.
- `isFixedUngenerable fixed e` — `allFVarsFixed` **and** `e`'s type has no
  `Arbitrary` instance. Conservative: returns `false` (old behavior) if the type
  has metavariables, and only reports `true` when an `Arbitrary ty` synthesis
  probe genuinely fails. This distinguishes `T.mono` (no `Arbitrary` → leave
  fixed) from `n * n : Nat` (`Arbitrary Nat` exists → flatten).

`linearizeAndFlatten` takes a `fixedFVars` parameter;
`getScheduleForInductiveRelationConstructor` computes it as the conclusion's
non-output argument positions that are bare fvars (the inductive's parameters,
including `P`).

### 2b. Emit demand-driven struct-param leaf binders

*Files: `Specimen/DeriveConstrainedProducer.lean`,
`Specimen/MakeConstrainedProducerInstance.lean`.*

`computeStructLeafBinders` scans a spec's schedule steps and returns the
`(className, leafSyntax)` binders the producer needs — one per struct-param
projection leaf that **actually appears**, and none for unused fields. This is
the leaf-granularity analogue of the constraint propagation in
`Docs/Constraint-propagation.md` (`computeSpecConstraints`): where that discovers
which classes a spec needs on its plain `Sort` type parameters, this discovers
them for each `Type`-valued projection leaf of a structure parameter. In both,
**the class attached to a leaf is discovered from how the leaf is used, not
hardcoded**, so a leaf gets only the classes it strictly needs.

Three kinds of step contribute binders:

- **Unconstrained generation** — a step that draws a value of a leaf type from an
  unconstrained `Arbitrary`/`Enum` instance demands the producer's own class
  (`Arbitrary` for generators, `Enum` for enumerators). Two shapes:
  - *Direct leaf*: the step's source *is* a projection chain rooted at the struct
    param (`isStructProjChain`), e.g. generating a value of type `P.Label`.
  - *Compound leaf*: an argument *contains* a projection chain but the overall
    type is not itself a leaf, e.g. `List P.Label`. `collectStructProjChains`
    finds the chains; a synthesis probe (opening the type constructor's telescope
    with `[Arbitrary/Enum/DecidableEq]` on its `Sort`-typed positions) confirms
    leaf instances suffice; then each chain present in the step is mapped back to
    its leaves.
- **Equality check** — an `Eq`/`Ne` `Check` over a leaf type demands
  `[DecidableEq leaf]` on that leaf. Equality on a type always needs decidable
  equality — the one constraint knowable statically, exactly as
  `computeSpecConstraints` special-cases it for plain type params. (Without this,
  a relation like `Distinct P (.mk a b)` where `a b : P.Key` and the rule requires
  `a ≠ b` would fail to derive: the generated checker needs `DecidableEq P.Key`.)
- **`SuchThat` on a leaf output** — a step that draws a leaf-typed value
  satisfying a relation (a *constrained* producer dependency, e.g. finding a
  witness `x : P.A`) demands the producer's unconstrained class on that leaf,
  because the dependency's own producer requires it. Only *proper* projections
  count here: an output that merely mentions the bare parameter inside a compound
  (e.g. producing `TaggedTree P`) is handled by that dependency's own binders, so
  bare-parameter chains are skipped (`leafProjsInArgs`) to avoid re-expanding all
  of `P`'s fields.

So a leaf used only for generation gets just `Arbitrary`/`Enum` (never a spurious
`DecidableEq`), a leaf used only in an equality check gets just `DecidableEq`, and
a leaf used both ways gets both. `resolveChainType` maps a projection chain to its
root structure type and projection path; `structLeavesFromType` is the shared
recursive walk (a `Type u` value is a leaf; a structure-typed value recurses
through each field's projection). Leaves are represented identifier-agnostically
as `StructLeaf` (root structure + projection-function path), so the *same* leaf
compares equal across specs regardless of how each spec freshens the parameter's
name; `structLeafBindersToSyntax` renders each leaf rooted at the emitting spec's
own parameter identifier.

**Cross-spec propagation.** A leaf constraint often originates in a *dependency*:
a generator that checks `¬ HasWitness` needs whatever `HasWitness`'s checker needs
to enumerate its leaf-typed witness (`[Enum P.A]`). `propagateStructLeafBinders`
handles this — the leaf-level analogue of `propagateConstraints`. Walking
components in topological order (mutual SCCs to a fixed point), each spec's binders
are its own (`computeOwnStructLeafBinders`) unioned with those of every
relation/checker dependency it uses. Because leaves are identifier-agnostic, a
dependency's leaf re-renders correctly against the dependant's own parameter — all
specs in one `derive_mutual` share the same structure parameter, just under
different freshened names.

These binders are threaded into every emission path in
`MakeConstrainedProducerInstance.lean`:

- **Single-instance path** (`mkConstrainedProducerTypeClassInstance`): appended
  to the type-param instances.
- **Mutual-`def` path** (`mkConstrainedProducerMutualPieces`): placed
  **innermost**, after all value params, because a leaf like
  `P.info.Metadata` references the value param `P`, which must already be in
  scope. Both the `∀`-type and the matching lambda insert them there, and the
  wrapper `instance` commands append them too.

All deriver entry points compute the binders and pass them through:
`deriveConstrainedProducer` (used by `derive_generator` / `derive_enumerator`)
and `deriveConstrainedProducerParts` (used by `deriveFromScheduleDep`) each derive
`structParams` from their non-output, non-`Sort` arguments and call
`computeStructLeafBinders` directly; `compileInductiveSchedule` (the
`derive_mutual` path) instead receives the SCC-propagated binders from
`propagateStructLeafBinders` and falls back to its own only when none is supplied.

### 2c. Drop implicit constructor args from produced values

*File: `Specimen/MExp.lean`.*

`dropImplicitCtorArgsExpr` recursively removes arguments at implicit /
instance-implicit positions of every genuine data-constructor application in the
produced value:

- `.Ctor c args`: recurse into args; if `c` is a real constructor, use
  `forallTelescopeReducing` on its type to keep only the explicit positions. If
  the arg count doesn't match the arity, leave it unchanged. `.Ctor` nodes that
  are actually abbrevs/defs (e.g. `LExprParams.mono`) are left alone.
- `.TyCtor` / `.FuncApp`: recurse into args but don't filter their own arg lists
  (they are emitted implicit-allowing already).

This drops, e.g., `LExpr.const`'s implicit `T` and `Option.some`'s implicit `α`
so the implicit-allowing emission re-infers them. `scheduleToMExp` applies this
to the producer schedule's `conclusionOutputs` before converting them to `MExp`s.

## 3. Tests

- **`SpecimenTest/DeriveArbitrarySuchThat/StructParamBinderTest.lean`** isolates
  the binder logic across leaf shape (direct field / compound `List P.Label` /
  nested `P.inner.Needed`), emission path (single-instance vs. mutual), and
  producer sort (generator / enumerator), plus a case checking that per-leaf
  *constraints* are discovered rather than hardcoded — a leaf compared with `≠`
  gets `DecidableEq` on top of `Arbitrary`. Every fixture monomorphizes the
  *unused* sibling field to `Empty` (which has no `Arbitrary`/`Enum` instance), so
  an over-emitted binder would fail to synthesize at use-site; a computable oracle
  is `#eval`'d over samples wherever the relation fixes the value's shape.

- **`SpecimenTest/DeriveArbitrarySuchThat/DeriveStructParamGenerator.lean`** is a
  self-contained miniature STLC witness: a structure parameter with one nested
  field, deriving a generator and enumerator together over the genuine abstract
  `Tm P`.

- **`SpecimenTest/StrataLexprGen.lean`** is the end-to-end witness. It derives a
  sound generator for well-typed Strata `LExpr`s from `@LExpr.HasTypeA T …` with
  `T` abstract:

  ```lean
  derive_mutual (fun (T : LExprParams) (Δ : List LMonoTy) (τ : LMonoTy) =>
    ∃ e : LExpr T.mono, @LExpr.HasTypeA T Δ e τ)
  ```

  An embedded `#eval` samples the derived generator at the monomorphic
  instantiation `P := ⟨Unit, Unit⟩` and type-checks every sample with the
  vendored `LExpr.typeCheck` oracle (from `SpecimenTest/StrataDefs/LambdaCore.lean`,
  proved equivalent to `HasTypeA` upstream), throwing on any ill-typed term. This
  example also relies on two capabilities beyond struct-param support: the
  classifier tolerating a function-application premise (the `bvar` de-Bruijn
  lookup `Δ[i]? = some t`), and the delegated-producer path routing that equality
  to a hand-written `ArbitrarySizedSuchThat`.

## 4. Open issues / limitations

- **Compound-leaf enumerators are broken.** A `derive_enumerator` whose
  struct-param leaf appears inside a *compound* type (e.g. `List P.Label`) fails
  with a spurious `Enum (Except GenError (List P.Label))` synthesis goal. This is
  a bug in the enumerator's compound-field emission (an `Except GenError` wrapper
  leaking into the enumerated element type), *not* in the binder machinery: it
  does not affect direct-leaf enumerators, nor a plain `Type` parameter of the
  same shape, nor generators. `StructParamBinderTest.lean` derives a *generator*
  only for the compound-leaf case for this reason.

- **Universe-polymorphic structure parameters are unsupported.** The leaf walk
  (`structLeavesFromType` / `resolveChainType`) reads a projection's codomain via
  `mkConst projName` with no universe-level arguments, so for a
  universe-polymorphic structure parameter the projection type would be computed
  at the wrong universe. All current Strata params are `Type 0`. A fix would
  extract the parameter type's universe levels and pass them to `mkConst`.

- **Leaf constraints are limited to the standard classes.**
  `computeStructLeafBinders` attaches to a leaf the producer class
  (`Arbitrary`/`Enum`) for generation/`SuchThat` steps and `DecidableEq` for
  `Eq`/`Ne` checks, and `propagateStructLeafBinders` carries those across the
  dependency graph (so a checker's `[Enum P.A]` reaches a generator that checks
  it). It does not run the full `synthExternalConstraints` *read-back* that
  `computeSpecConstraints` uses for plain type params, so if a leaf were passed to
  a dependency requiring some *non-standard* class (e.g. a custom `[MyHashable
  P.A]`), that class would not be discovered. No current example needs this;
  covering it would mean reading a dependency's instance binders back at leaf
  granularity rather than assuming the standard classes.
