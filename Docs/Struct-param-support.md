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
projection leaf that **actually appears**, and none for unused fields. It only
inspects `.Unconstrained` steps (the ones that draw a value from an unconstrained
`Arbitrary`/`Enum` instance) and handles two shapes:

- **Direct leaf** — the step's source *is* a projection chain rooted at the
  struct param (`isStructProjChain`), e.g. generating a value of type `P.Label`.
  Emit a binder for that leaf directly.
- **Compound leaf** — an argument *contains* a projection chain but the overall
  type is not itself a leaf, e.g. `List P.Label`. `collectStructProjChains` finds
  the chains; a synthesis probe (opening the type constructor's telescope with
  `[Arbitrary/Enum/DecidableEq]` on its `Sort`-typed positions) confirms leaf
  instances suffice; then `resolveChainType` maps **each chain present in the
  step** back to its leaf syntax and emits binders for those leaves only.

`structLeavesFromType` is the shared recursive walk: a `Type u` value is a leaf;
a structure-typed value recurses through each field's projection, building
projection-chain syntax (`P.info` → `NodeInfo.Metadata (P.info)`).
`structLeafBindersToSyntax` renders the results as `[className leaf]` binders.

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
`deriveConstrainedProducer` (used by `derive_generator` / `derive_enumerator`),
`deriveConstrainedProducerParts` (used by `deriveFromScheduleDep`), and
`compileInductiveSchedule` (the `derive_mutual` path). Each accumulates its
constructors' schedule steps, derives `structParams` from the non-output,
non-`Sort` arguments (named by their freshened names so the emitted binders match
the instance signature), and calls `computeStructLeafBinders`.

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
  the binder logic across three axes: leaf shape (direct field / compound
  `List P.Label` / nested `P.inner.Needed`), emission path (single-instance vs.
  mutual), and producer sort (generator / enumerator). Every fixture monomorphizes
  the *unused* sibling field to `Empty` (which has no `Arbitrary`/`Enum`
  instance), so an over-emitted binder would fail to synthesize at use-site; a
  computable oracle is `#eval`'d over samples wherever the relation fixes the
  value's shape.

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
