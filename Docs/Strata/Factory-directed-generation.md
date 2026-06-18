# Factory-Directed Generation

This document analyzes what Specimen needs in order to **generate `LExpr`s that
draw from a Strata `Factory`** — i.e. produce expressions that actually *call the
library functions* a factory defines, rather than only literals, variables, and
anonymous lambdas. It extends `HasType-constructor-analysis.md` (the per-rule
analysis of `HasType`) and `Delegated-producer-synthesis.md` (the producer
machinery). It draws on lessons from a prior effort to synthesize an `LExpr`
generator by hand and on two experiments — `FactoryDrawExp.lean` and
`FactoryProducerExp.lean` (Lean `v4.30.0-rc1`) — that measure the problem and the
fix.

> Source note. `Factory`, `LFunc`, etc. are summarized from Strata's
> `Strata/DL/Lambda/Factory.lean` (Apache-2.0/MIT) as read from GitHub; re-check
> field/function names against a pinned revision before writing code.

## What a `Factory` is, and what "drawing from it" means

A `Factory T` is essentially an **indexed table of function signatures**:

```
abbrev LFunc T := Func T.Identifier (LExpr T.mono) LMonoTy T.Metadata
structure Factory (T : LExprParams) where
  toArray : Array (LFunc T)            -- the functions
  nameMap : Std.HashMap String Nat     -- name → index, for O(1) lookup
  -- + invariants tying nameMap to toArray
```

Each `LFunc` carries (among other things) `inputs : ListMap Identifier LMonoTy`
(the typed parameters) and `output : LMonoTy` (the result type), plus an optional
body, axioms, preconditions, and eval hooks. `Factory.get?`/`getElem?` look up by
index; `getFunctionNames` lists names; `LFunc.type` assembles the arrow type;
`callOfLFunc`/`getLFuncCall` relate an `LExpr` application back to the `LFunc` it
calls (with an arity check). In Strata, the factory is reachable from the typing
context (`LContext`/`C.functions` in the `top`/`top_annotated` rules of
`HasType`), so it is a *fixed input* to any generation problem, exactly like `Γ`.

**Drawing from the factory during generation** means: when building an expression
of (or producing) some type, *pick a function `f` from the factory and emit a
fully-applied call* `f e₁ … eₙ`, where each argument `eᵢ` is generated **at the
type `f` declares for it** (`f.inputs[i]`), and the call has type `f.output`.

## Why this is the crux problem

A lesson from hand-writing an `LExpr` generator: a naive generator built on the
standard application rule

```
Γ ⊢ e₁ : τ' → τ      Γ ⊢ e₂ : τ'
--------------------------------- (App)
        Γ ⊢ e₁ e₂ : τ
```

**almost never generates factory calls**, because `App` forces the generator to
*guess* the argument type `τ'`. For an n-ary library function
`f : σ₁ → … → σₙ → τ`, naive `App` must (a) nest `App` n times and (b) guess all
of σ₁…σₙ correctly. For example, `take : Int → String → String` needs the
generator to independently roll `Int` and then `String` as the two argument types;
the probability of doing so is negligible, so calls to real library functions
essentially never appear.

The fix is **Pałka et al.'s "Indir" generation rule** (AST '11):

```
f : σ₁ → σ₂ → τ ∈ Γ    Γ ⊢ e₁ : σ₁    Γ ⊢ e₂ : σ₂
--------------------------------------------------- (Indir)
               Γ ⊢ f e₁ e₂ : τ
```

It is *logically redundant* (derivable from `App`) but *operationally essential*:
the argument types σ₁…σₙ are **read off the function signature**, not guessed, and
the whole call is produced in one step. The lesson is that a good generator uses
**both** `App` (for anonymous-lambda applications) and `Indir` (for named/library
functions). Strata's `top`/`top_annotated` rules are already close to `Indir` in
spirit: they look the operator up in `C.functions` and read its type. The work for
Specimen is to make its *derived* generator exploit that lookup the way Indir
prescribes, rather than inverting it by guess-and-check.

## Evidence from experiments

Two experiments model the Indir rule at minimal size, free of the
structure-parameter blocker (which is orthogonal — see `StructParamCmdShapeExp.lean`):

```lean
abbrev Factory := List FnSig          -- FnSig = { argTys : List Ty, resTy : Ty }
inductive Expr | lit : Nat → Ty → Expr | call : Nat → List Expr → Expr
mutual
  inductive HasTy (F : Factory) : Expr → Ty → Prop
    | lit  : HasTy F (.lit n t) t
    | call : F[i]? = some sig → HasTyList F args sig.argTys → HasTy F (.call i args) sig.resTy
  inductive HasTyList (F : Factory) : List Expr → List Ty → Prop   -- pointwise (Forall2)
    | nil | cons : HasTy F e t → HasTyList F es ts → HasTyList F (e::es) (t::ts)
end
```

The `call` rule *is* Indir: invert the container lookup `F[i]? = some sig` to pick
a function, then type the argument list pointwise against `sig.argTys`.

**`FactoryDrawExp.lean` — Indir is expressible but does not fire.** Derivation
succeeds in every mode (synthesis `(+F, −e, −t)`, type-directed `(+F, +t, −e)`, and
the pointwise argument-list relation `(+F, +ts, −es)`), so feasibility is not the
obstacle. But the derived generator draws **~0% factory calls**: it inverts
`F[i]? = some sig` by guessing the index and checking, which almost never hits, so
generation falls back to the trivial base rule `lit` (a literal at any type). This
holds in synthesis mode (0% at sizes 3/5/7, 200 samples each) and in type-directed
mode (asking for a type only a factory function produces still yields only literals).

**`FactoryProducerExp.lean` — supplying the producer fixes it.** This experiment
writes the lookup as an opaque `def`
(`factoryEntryAt F t i sig := F[i]? = some sig ∧ sig.resTy = t`) and hand-supplies
the bucket-1 producer — given `F` and a demanded result type `t`, scan `F` and
return a matching `(index, signature)`, reading the argument types off the matched
entry instead of guessing them (the pattern of `ModeDirectedExp.lean`). With that
one instance in scope and codegen unchanged, the same relation draws factory calls
the majority of the time (200 samples/cell, Lean v4.30.0-rc1):

| mode | no producer | with producer |
|---|---|---|
| type-directed @ a type only the binary fn produces | 0% | 80–91%, mostly depth≥2 (the full Indir chain) |
| type-directed @ a type the trivial `lit` rule also satisfies | 0% | ~80–85% |
| synthesis (result type is an output) | 0% | ~40–52% |

The experiments pin down three facts the design relies on:

- **The producer realizes Indir end to end.** At a type whose only producer is the
  binary factory function, most generated terms are depth ≥ 2 — the binary call
  whose argument is a unary call whose argument is a literal. Container inversion
  plus the (already-deriving) pointwise typed-argument recursion is the whole
  mechanism.
- **The producer needs both mode projections.** With only the type-directed
  projection `(+F, +t) → (−i, −sig)` in scope, synthesis mode `(+F) → (−t, −i, −sig)`
  fails to synthesize an instance — the scheduler requires
  `ArbitrarySizedSuchThat (Ty × Nat × FnSig) …` because the result type is also an
  output. The by-key projection (enumerate all entries, take each `resTy` as the
  output type) supplies it.
- **Weighting is a secondary lever.** In type-directed mode the producer alone
  gives ~80% calls even when `lit` also satisfies the target; in synthesis mode the
  rate is ~40–52% because the base case competes more when the type is
  unconstrained. Per-rule weighting raises that residual but is not what makes
  calls happen.

## What Specimen needs

The core is one capability: a **factory-selection producer** (need 1) that, given
the factory and a demanded result type, returns a matching function and its
argument types — so the `call`/Indir rule reads argument types off the signature
instead of guessing them. The remaining needs expand on that: weighting to tune how
often calls appear (need 2), plumbing the factory through as an input (need 3), and
size discipline for deep calls (need 4).

### 1. A factory-selection producer (container inversion, both projections)

This is the decisive capability and is precisely bucket 1 of the `HasType` analysis
(container-membership–directed generation). The oracle must recognize that
`F[i]? = some sig` with `sig.resTy` related to the conclusion is invertible by
*scanning* the factory, and produce in two modes:

- **by-value** (type-directed `(+F, +t) → (−i, −sig)`): enumerate only the entries
  whose `resTy` unifies with the target `t`, then generate each argument at the
  corresponding `argTys[i]`;
- **by-key** (synthesis `(+F) → (−t, −i, −sig)`): enumerate all entries and take
  each `resTy` as the output type.

Both are needed (the synthesis mode fails to compile without the by-key
projection). Strata's factory provides the index structure (`nameMap`, `getElem?`)
to make the scan efficient. This is the same producer as `HasType`'s
`top`/`top_annotated` (look up `C.functions[op.name]?`) and `tvar` (look up
`Γ.types`) — a factory is "just another container" — so one container-inversion
oracle supporting both projections serves variables, operators, and factory draws
uniformly.

### 2. Base-case / branch weighting to tune how often calls appear

This is a distribution lever: **weighted choice among constructors/rules** (biased
`pick`/`frequency`, the knobs `Docs/Generator-config.md` describes), with the base
case down-weighted relative to the productive recursive rules (cf. Tjoa et al.,
*Tuning Random Generators*, OOPSLA '25; visualized with Tyche). For Specimen this
is a *scheduling/codegen policy*, not a producer: the derived
`Gen.frequency`/`backtrack` lists need tunable, factory-aware weights (e.g. weight
the `call` rule by factory size, or expose a per-rule weight config).

It bites only where a cheap base rule can satisfy the same demand as a factory
call, which depends on result types. `HasType`'s constant rules have **fixed**
result types (`tint_const → .int`, `tbool_const → .bool`, …), so:

- *Type-directed at a factory-specific type* (a type no constant produces): the
  constant rules cannot fire, so they do not compete — the producer alone reaches
  ~80% calls here. This is the most important case for PBT, and weighting is
  largely unnecessary.
- *Synthesis mode, or type-directed at a primitive type* (Int/Bool, which a
  constant also produces): the cheap base case competes (the ~40–52% synthesis
  measurement), and weighting raises the factory-call fraction.

Selection (need 1) is what makes calls possible and already makes them common in
the key type-directed case; weighting tunes how often they appear. Weighting alone
accomplishes nothing — without the producer the lookup still fails to invert, so a
more-often-tried `call` branch just backtracks.

### 3. The factory as a first-class generation input (and sub-generator plumbing)

The factory is a *parameter* of the generation problem (like `Γ`), so it must be
threaded as an input to the derived producer and to every recursive sub-call —
including the pointwise argument-list producer, which needs `F` in scope to type
each argument. The experiment confirms a `List`-valued factory parameter is
threaded correctly through `derive_mutual`. Two things to confirm/extend for the
*real* `Factory`:

- **It is a structure with invariants, not a plain `List`.** Generation only
  *reads* it (`get?`/`getElem?`/`getFunctionNames`), so the invariant fields
  (`toArrayDefined`, `nameMapValid`, …) are irrelevant to the producer — but the
  deriver must treat `Factory` as an opaque indexed container with a lookup
  interface, not try to generate or destructure it. This is the bucket-1 oracle
  recognizing `Factory.get?`/`getElem?` (and `Array.getElem?` underneath)
  the same way it recognizes `Map.find?`/`List` indexing.
- **Sub-generator selection.** `Generator-config.md` lays out three ways to supply
  a sub-generator (direct call, typeclass, parameter). Drawing arguments at the
  factory-declared types is a recursive call into the *same* `HasType` producer in
  type-directed mode; the factory itself is passed by parameter. No new mechanism,
  but the factory parameter must flow to those recursive calls.

### 4. Fuel/size discipline for nested calls

A fully-applied n-ary call spends size on *n* sub-expressions at once, so a
call-of-call chain is deep relative to its node count and can exhaust a fuel budget
tuned for shallow terms (the experiment hits this when a target type is reachable
only through a nested chain). Options already in the design space: `partial_fixpoint`
(Basalt) to remove fuel as a termination device (see `Specimen-Basalt-port.md`),
and/or charging size by term *size* rather than *depth* so a wide-but-shallow
factory call is not penalized as if it were deep. This is a refinement that matters
once selection (1) makes deep factory terms reachable at all.

## Summary

| Need | Nature | Priority (measured) | Reuses | New? |
|---|---|---|---|---|
| 1. Factory selection producer (both by-value and by-key projections) | producer (filtered/enumerated container inversion) | **required** — 0%→80–91% alone | `HasType` bucket 1 (`top`/`tvar` container producer) | extends bucket 1 to a structure-backed indexed container; needs *both* mode projections |
| 2. Base-case / rule weighting | scheduler/codegen policy | secondary — only where a cheap rule shares the target type (synthesis, primitive targets) | `Generator-config.md` distribution knobs | factory-aware, tunable per-rule weights |
| 3. Factory as generation input | plumbing | required (prerequisite for 1) | `derive_mutual` parameter threading; `Generator-config.md` sub-gen plumbing | recognize `Factory.get?`/`getElem?` as a read-only indexed container |
| 4. Fuel/size for nested calls | size policy | refinement | `Generator-config.md`; Basalt `partial_fixpoint` | size-by-term-size; refinement |

**Bottom line:** Specimen can already *express* the Indir rule (container inversion
+ pointwise typed argument list both derive), but a derived generator draws ~0%
factory calls because it inverts the lookup by guess-and-check. The decisive fix is
the **need-1 factory-selection producer**, which flips the call rate to 80–91% in
type-directed mode (including deep nested chains); it must offer both mode
projections. Weighting (need 2) is a secondary lever for synthesis/primitive
targets; plumbing (need 3) and size discipline (need 4) round it out. So adding an
Indir rule to `HasType` is necessary but not sufficient on its own — its
`top`/`top_annotated`-style lookup is guess-and-check until the need-1 producer is
attached. Both core needs reuse capabilities already on the roadmap (bucket-1
container inversion; `Generator-config.md` weighting).

## Relationship to other docs

- **Experiments** — `SpecimenTest/StrataExperiments/FactoryDrawExp.lean` derives the
  Indir-style relation and shows the 0%-call failure (guess-and-check lookup);
  `SpecimenTest/StrataExperiments/FactoryProducerExp.lean` hand-supplies the need-1
  producer and measures the 0%→80–91% fix plus the two caveats (both projections;
  weighting is secondary).
- **`Delegated-producer-synthesis.md`** — the container-inversion producer (need 1)
  is the "next target" that doc names after freshness; the factory is its canonical
  real-world instance. Result-type filtering is the by-value projection of that
  same producer.
- **`HasType-constructor-analysis.md`** — needs 1–2 here are exactly that doc's
  bucket 1 (`top`/`top_annotated` container inversion) and the distribution side of
  its Blocker B, specialized to the factory.
- **`Generator-config.md`** — needs 2 and 4 are the weighting and size/distribution
  knobs that doc describes; this analysis gives them a concrete objective ("emit a
  non-trivial fraction of factory calls").
- **`Cmd-generator-analysis.md`** — command typing delegates expression typing to
  `HasType`; a `Cmd` whose `init`/`set` initializers should call library functions
  inherits this factory-draw machinery wholesale through that delegation (finding D
  there).
- **Prior hand-written `LExpr` generator** — the empirical source: the Indir rule
  and the tuned-distribution fix are the two lessons from that effort that this
  analysis maps onto Specimen capabilities.
