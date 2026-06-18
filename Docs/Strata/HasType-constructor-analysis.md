# `HasType` Constructor Analysis

This document works through every constructor of Strata's `HasType` relation
(`Strata/DL/Lambda/LExprTypeSpec.lean`) to identify what changes are needed for
Specimen to be able to synthesize generators of the forms `HasType(+C, +Γ, −e, −τ)`
and `HasType(+C, +Γ, −e, +τ)`. The changes are summarized first, then the 
analysis to justify it follows.

## Summary: what Specimen needs to change

Working through all sixteen constructors (details below), the required changes
collapse into **three buckets**. The headline finding is that, once the
structure-parameter prerequisite is cleared, *most* of the remaining work is one
mechanism — external/delegated producer synthesis — applied to different shapes.

**0. Prerequisite — fix structure-parameter projection in the constrained deriver.**
`HasType` produces an `LExpr T.mono`, whose type is a projection of the structure
parameter `T`. The constrained path (`derive_generator`/`derive_mutual`) aborts on
this (`unknown free variable T_1`), though the unconstrained `deriving Arbitrary`
path already handles it. The fix is a well-scoped *port* of existing logic from
`Specimen/DeriveArbitrary.lean`, not new machinery. Nothing else can be attempted
until this is done (or `T` is specialized to a concrete `LExprParams`). See the
*Global prerequisite* section below.

**1. The external-generation mechanism (the bulk of the work).** Once a constraint
is run in a producer *mode* ("given these inputs, produce those outputs"), the
question is only "does a producer for that mode exist, and if not, can one be
built?" — exactly the layered oracle + obligation-list + batch-construction design
in **`Delegated-producer-synthesis.md`**. The following per-constructor needs are
all *instances of this one mechanism*, differing only in the shape being produced:
  - **Container-membership–directed generation** (`tvar`, `top`, and the annotated
    variants) — produce a key/value by enumerating a fixed map/list instead of
    guessing. *Highest impact: the difference between a generator that emits only
    constants and one that emits variables and operators.*
  - **Binder-aware inversion + freshness** (`tabs`, `tquant`) — produce the
    *opened* body via the recursive producer and recover the bound form
    (`varClose`), and produce a fresh binder rather than guess-and-check it.
    Freshness is the recommended first prototype in the design doc.
  - **Length-directed list generation** and **`Except`/function-result inversion**
    (annotated rules) — smaller local producers.
  - **Delegated synthesis for opaque predicates** (`AnnotCompat`'s `∃σ, …`) — the
    canonical case for handing an obligation to an external (LLM/human) backend;
    the spec's own `AnnotCompat.of_eq` hints at a sound producer.

**2. Scheduler/deriver changes that are *not* external generation (a short list).**
Two changes are genuinely about how Specimen schedules and elaborates, not about
obtaining producers:
  - **Disjunction branch-selection** — treat `h₁ ∨ h₂` as a per-branch choice point
    (and prefer the cheap branch, e.g. `o = none`), instead of one opaque `DecOpt`
    check over the whole `∨`.
  - **Coercion-rule control** — bound or exclude non-syntax-directed constructors
    (`tinst`/`tgen`/`talias`) so they don't dominate backtracking.

**Design principle: supply a producer for each opaque predicate as written; do not
unfold its `def`.** The predicates that block `HasType` (`fresh`, `AnnotCompat`,
`toMonoType`) are ordinary `def`s, and unfolding them does not help: `AnnotCompat`
unfolds to `∃σ, AliasEquiv …`, which still needs a producer (so attach the producer
to `AnnotCompat` directly); `fresh` unfolds to `x ∉ freeVars e`, which Specimen can
only generate-and-check (`negOpt`/`decOpt`) — the very path bucket 1's freshness
producer exists to replace. Unfolding would help only for the shape `a = g(inputs)`
(output computable from inputs), and no blocking `HasType` def has that shape: in
synthesis mode the conclusion coercions like `toMonoType x_ty hx` are already plain
applications the unifier evaluates, and in type-directed mode inverting them is a
bucket-1 producer problem.

In short: **bucket 0 is a one-time port; bucket 1 is the delegated-synthesis
mechanism doing most of the heavy lifting; bucket 2 is two focused scheduler
tweaks.** The constructor-by-constructor analysis substantiating this follows.

## Two generation modes

There are two generation modes, with very different difficulty profiles:

- **Synthesis mode** `HasType(+C, +Γ, −e, −τ)` — "produce some well-typed term
  and its type." `τ` is an *output*. This is closest to what Specimen's STLC
  example already does, and to "give me arbitrary well-typed terms."
- **Type-directed mode** `HasType(+C, +Γ, −e, +τ)` — "produce a term *at* a
  given type." `τ` is an *input*. This is the more useful mode for PBT (test a
  function that consumes a term of a specific type) and the harder one, because
  most constructors must *invert* the type in their conclusion to drive
  generation.

Throughout, `m` (metadata) is an output with a trivial `Arbitrary` (or fixed
unit) instance and is ignored. `C` is a fixed input in both modes.

---

## Global prerequisite: the structure-parameter projection blocker

Before any constructor matters, the *whole relation* trips over a derivation-time
bug. `HasType` is parameterized by `{T : LExprParams}`, and the generated term
has type `LExpr T.mono` — a projection of the structure-valued parameter `T`.
`Experiments/StructParamExp.lean` shows that when the **output's type is a
projection of a structure parameter**, derivation aborts with
`error: unknown free variable p_1` (the parameter name is freshened but not
re-bound inside the projected type). Plain type parameters and even `Type 1`
structures with type-valued fields are fine; only the *projected output type*
breaks.

This is a limitation of the **constrained-producer path only**. The unconstrained
`deriving Arbitrary` handler (`Specimen/DeriveArbitrary.lean`) already handles
structure parameters with projected type-valued fields (passing test:
`SpecimenTest/DeriveArbitrary/StructureParameterTest.lean`;
`Experiments/StructParamPathsExp.lean` shows both paths on the same type — one
succeeds, the other fails). So the fix is well-scoped: **port the working
parameter-handling logic from `DeriveArbitrary.lean` into the constrained
deriver** (`derive_generator`/`derive_enumerator`/`derive_mutual`).

This affects every mode of `HasType` equally and must be resolved first, either
by that port or, as a workaround, by **specializing `T`** to a concrete
`LExprParams` (e.g. `Unit` metadata) so `LExpr T.mono` reduces to a closed type.
The per-constructor analysis below assumes this prerequisite is met.

---

## Constants: `tbool_const`, `tint_const`, `treal_const`, `tstr_const`, `tbitvec_const`

```
| tint_const : ∀ Γ m n, C.knownTypes.containsName "int" → HasType C Γ (.intConst m n) (.forAll [] .int)
```

- **Hypothesis**: `C.knownTypes.containsName "int"` — a `Bool` check on the fixed
  input `C`, no outputs. **Known** (generate-and-check degenerates to a single
  guard; no value is guessed).
- **Conclusion outputs**: `n` (the literal) is unconstrained → plain `Arbitrary`.
  Known.

**Synthesis mode**: trivial. Pick a constant constructor, check its type name is
known, emit `.intConst m n` with random `n`, output type `.int`.

**Type-directed mode**: trivial *and better* — the target `τ` selects which
constant rule applies (`.int → tint_const`, `.bool → tbool_const`, …). The
`bitvec n` case needs `n` extracted from `τ = .bitvec n` (a pattern match on the
input type), which Specimen's unification already does.

**New capability needed**: none. This is squarely in scope today.

---

## `tvar` — unannotated variable

```
| tvar : ∀ Γ m x ty, Γ.types.find? x = some ty → HasType C Γ (.fvar m x none) ty
```

- **Hypothesis**: `Γ.types.find? x = some ty`, a finite-map lookup.
- **Synthesis mode** `(−x, −ty)`: we want to produce *both* a variable `x` and
  its type `ty` from the map. The natural producer is "enumerate the bindings of
  `Γ.types`." This is a **container-inversion** producer: mode
  `find?(+Γ, −x, −ty)`. Plausibly-producible (the obligation the design doc
  flags as the highest-value second prototype). Without it, generate-and-check
  guesses `x` and tests the lookup — hopeless for anything but tiny key spaces.
- **Type-directed mode** `(−x, +ty)`: now `ty` is fixed and we want a variable of
  that type. The producer is "enumerate keys `x` of `Γ.types` whose bound value
  is `ty`" — a *filtered* container inversion, mode `find?(+Γ, +ty, −x)`. Same
  capability, different projection.

**New capability needed**: **container-membership–directed generation** — the
oracle must recognize `Map.find?`/`lookup`/`getElem?`-shaped hypotheses and
produce by enumerating the (fixed) container rather than guessing keys. This is
the single biggest quality lever for typing-relation generators and applies
identically to `top`/`top_annotated` (which look up `C.functions`).

---

## `tvar_annotated` — annotated variable

```
| tvar_annotated : ∀ Γ m x ty_o ty_s tys ann,
    Γ.types.find? x = some ty_o →
    tys.length = ty_o.boundVars.length →
    LTy.openFull ty_o tys = ty_s →
    AnnotCompat Γ.aliases ann ty_s →
    HasType C Γ (.fvar m x (some ann)) (.forAll [] ty_s)
```

Four hypotheses, increasing in difficulty:

1. `Γ.types.find? x = some ty_o` — container inversion, as in `tvar`.
2. `tys.length = ty_o.boundVars.length` — a *length* constraint on a list output
   `tys`. The producer wants "generate a list of monotypes of length
   `ty_o.boundVars.length`." This is **length-directed list generation**:
   mode `(+len, −list)`. Plausibly-producible; arguably already expressible as a
   constrained producer over `List` if Specimen can read the length off the
   input.
3. `LTy.openFull ty_o tys = ty_s` — `ty_s` is a *function* of `ty_o` and `tys`,
   both available by this point → compute it directly. Known (this is the "output
   is a computable function of inputs" filter, the easy case).
4. `AnnotCompat Γ.aliases ann ty_s := ∃ σ, AliasEquiv … (subst σ ann) ty_s` —
   here `ann` is an output. We must produce an annotation *compatible with*
   `ty_s`. This is the genuinely hard, **delegated** obligation: a `def`-wrapped
   existential. A reasonable producer ("pick `ann := ty_s`, with `σ` the identity
   substitution"; see `AnnotCompat.of_eq` in the spec, which proves
   `AnnotCompat aliases ann ann`) exists but requires *semantic* insight into the
   definition — exactly what the LLM-backed batch step is for.

**New capabilities needed**: container inversion (#1), length-directed list
generation (#2), and **delegated synthesis for an opaque existential predicate**
(#4). #3 is already in scope.

---

## `tabs` — abstraction (binder)

```
| tabs : ∀ Γ m name x x_ty e e_ty o,
    LExpr.fresh x e →
    (hx : LTy.isMonoType x_ty) →
    (he : LTy.isMonoType e_ty) →
    HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) e_ty →
    (o = none ∨ ∃ t, o = some t ∧ AnnotCompat Γ.aliases t (x_ty.toMonoType hx)) →
    HasType C Γ (.abs m name o e) (.forAll [] (.tcons "arrow" [x_ty…, e_ty…]))
```

This is the crux constructor. Several distinct issues converge:

- **Locally-nameless binder.** The recursive hypothesis types
  `LExpr.varOpen 0 x e` in a context extended with `x : x_ty`. `e` (the abstraction
  body, with a `bvar 0` hole) is the output we ultimately want, but the recursive
  call is on the *opened* term. As `TransformedRecExp.lean` shows, Specimen will
  generate `e` blind and check the recursive typing — catastrophic. What we want:
  *generate the opened body `eo` directly* via the recursive producer (in the
  extended context, at type `e_ty`), then **close** it back to `e`
  (`eo = varOpen 0 x e ⟺ e = varClose 0 x eo`). This is a **binder-aware
  inversion**: recurse on the opened form, recover the bound form by the inverse
  of `varOpen`.
- **Freshness.** `LExpr.fresh x e` — the mode-directed freshness producer
  (`Delegated-producer-synthesis.md`, prototype #1): given the body, choose a
  fresh `x`. Note the dependency order: freshness depends on `e`/`eo`, so it must
  be scheduled *after* the body is produced.
- **`isMonoType` guards.** `hx`, `he` — decidable guards on the chosen types;
  known (generate-and-check, or better, generate monotypes by construction).
- **Disjunctive annotation hypothesis.** `o = none ∨ ∃ t, …` — same opaque
  `AnnotCompat` obligation as `tvar_annotated`, wrapped in a disjunction. The
  cheap branch (`o = none`) is always available, so a competent scheduler can
  *prefer* it and avoid the hard branch entirely. **This suggests a capability:
  branch-selection within a disjunctive hypothesis**, rather than treating the
  whole `∨` as one `DecOpt` check (which `HardCasesExp.lean` shows is the current
  behaviour).

**Synthesis vs type-directed**:
- Synthesis `(−e, −τ)`: choose `x_ty` freely (a monotype), recurse to synthesize
  the body and `e_ty`, assemble the arrow type as output.
- Type-directed `(−e, +τ)`: the target must be an arrow `τ = .forAll [] (.arrow a b)`;
  pattern-match it to get `x_ty := a`, `e_ty := b`, then recurse type-directed on
  the body at `b`. This is *easier* for guiding the body, but requires inverting
  the `.tcons "arrow" [...]` structure in the conclusion (Specimen unification
  can do the pattern match; the `LTy.toMonoType _ hx` coercions around the
  subterms may obstruct it — see "Coercion noise" below).

**New capabilities needed**: binder-aware inversion (`varOpen`/`varClose`),
freshness producer, disjunction branch-selection, plus tolerance of the
`toMonoType`/`isMonoType` proof-carrying coercions.

---

## `tapp` — application

```
| tapp : ∀ Γ m e1 e2 t1 t2,
    (h1 : LTy.isMonoType t1) → (h2 : LTy.isMonoType t2) →
    HasType C Γ e1 (.forAll [] (.arrow t2 t1)) →
    HasType C Γ e2 t2 →
    HasType C Γ (.app m e1 e2) t1
```

- **Synthesis mode** `(−e, −t1)`: classic application generation. Choose argument
  type `t2` freely, recurse to synthesize `e2 : t2`, recurse to synthesize
  `e1 : t2 → t1` (which itself may pick `t1`), output `.app m e1 e2 : t1`. Both
  recursive calls are in producer mode. **In scope** modulo generating `t2`
  (needs an `Arbitrary`/producer for `LMonoTy`).
- **Type-directed mode** `(−e, +t1)`: `t1` is fixed. We must *invent* the argument
  type `t2` (it does not appear in the conclusion — it is existential and
  unconstrained by `t1`). So even type-directed, `t2` is generated, then `e1` is
  produced at `t2 → t1` and `e2` at `t2`. This is the well-known
  "application is not fully type-directed" problem; it is handled by generating
  `t2`, which Specimen can do given a producer for types.

**New capabilities needed**: a producer for `LMonoTy` (likely `deriving Arbitrary`
plus an `isMonoType`-respecting wrapper). No structural novelty beyond the type
generator.

---

## `tinst`, `tgen`, `talias` — non-syntax-directed (coercion) rules

```
| tinst : ∀ Γ e ty e_ty x x_ty, HasType C Γ e ty → e_ty = LTy.open x x_ty ty → HasType C Γ e e_ty
| tgen  : ∀ Γ e a ty, HasType C Γ e ty → TContext.isFresh a Γ → HasType C Γ e (LTy.close a ty)
| talias: ∀ Γ e mty mty', AliasEquiv Γ.aliases mty mty' → HasType C Γ e (.forAll [] mty) → HasType C Γ e (.forAll [] mty')
```

These recurse on the **same** `e` with a different type and **no structural
decrease**. `HardCasesExp.lean` establishes they do not cause nontermination
(size/fuel is decremented on every recursive call regardless of structural
decrease), but they are pure overhead: unproductive backtracking branches that
re-derive the same term at a shuffled type.

- **Synthesis mode**: they can be *dropped entirely* without losing coverage of
  the *set of well-typed terms* (every term derivable with a coercion is also
  derivable for some type without it). They only matter if we care about
  generating term/type pairs at *every* derivable type.
- **Type-directed mode**: here they are subtler. `tinst` lets a polymorphic term
  be used at an instance type; `tgen` introduces polymorphism; `talias` swaps in
  an alias-equivalent type. To hit a *specific* target `τ` these may be
  *necessary* (e.g. the target is an instance of the only available type). So
  they cannot simply be dropped — but applying them blindly explodes the search.

**New capability needed**: **coercion-rule control** — let the user/scheduler
mark certain constructors as coercions to be (a) excluded, (b) bounded to at most
*k* applications, or (c) applied only when no syntax-directed rule matches the
target. This is a scheduling-policy knob, not a producer-synthesis problem.
`tinst`/`tgen` additionally need producers for their fresh-type-variable
hypotheses (`TContext.isFresh a Γ` is a freshness producer over type variables —
same shape as the term-level freshness prototype) and for `e_ty = LTy.open x x_ty ty`
(invert `LTy.open`, or in synthesis mode just compute it).

---

## `tif`, `teq` — conditional and equality

```
| tif : ∀ Γ m c e1 e2 ty, HasType C Γ c (.forAll [] .bool) → HasType C Γ e1 ty → HasType C Γ e2 ty → HasType C Γ (.ite m c e1 e2) ty
| teq : ∀ Γ m e1 e2 ty,   HasType C Γ e1 ty → HasType C Γ e2 ty → HasType C Γ (.eq m e1 e2) (.forAll [] .bool)
```

Purely structural, all recursive hypotheses in producer mode.

- **`tif`**: both modes fine. Type-directed at `τ`: condition recurses at `.bool`
  (fixed), both branches recurse at `τ` (the input). Clean.
- **`teq`**: conclusion type is always `.bool`. In type-directed mode this means
  `teq` only fires when the target is `.bool` (unification on the conclusion
  handles this). The branch type `ty` is **not** determined by the conclusion —
  it is existential — so `ty` must be *generated* (like `t2` in `tapp`), then both
  sides produced at that type.

**New capabilities needed**: none beyond the type producer already required by
`tapp`.

---

## `tquant` — quantifier (binder)

```
| tquant: ∀ Γ m k name tr tr_ty x x_ty e o,
    LExpr.fresh x e →
    (hx : LTy.isMonoType x_ty) →
    HasType C {Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) (.forAll [] .bool) →
    HasType C {Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x tr) tr_ty →
    (o = none ∨ ∃ t, …) →
    HasType C Γ (.quant m k name o tr e) (.forAll [] .bool)
```

Combines everything from `tabs` (freshness, binder-aware `varOpen` inversion,
`isMonoType` guard, disjunctive `AnnotCompat`) with **two** opened recursive
hypotheses (`e` and the trigger `tr`) sharing the same fresh `x` and extended
context. Conclusion type is always `.bool`.

The extra wrinkle is the **shared binder across two subterms**: `x` must be fresh
for `e` (and presumably consistent for `tr`), and both `e` and `tr` are opened
with the same `x`. The binder-aware inversion must coordinate: produce both
opened bodies, choose one `x` fresh for both, close both. This is a
*multi-output binder* generalization of the `tabs` case.

**New capabilities needed**: same as `tabs`, plus coordination of a single fresh
binder across multiple opened subterms.

---

## `top`, `top_annotated` — operators

```
| top: ∀ Γ m f op ty, C.functions[op.name]? = some f → f.type = .ok ty → HasType C Γ (.op m op none) ty
| top_annotated: … C.functions[op.name]? = some f → f.type = .ok ty_o → tys.length = … → LTy.openFull … → AnnotCompat … → …
```

Directly analogous to `tvar`/`tvar_annotated`, but the container is `C.functions`
(a map keyed by operator name) and there is an extra `f.type = .ok ty` step
(invert/compute an `Except`). Same capabilities: container inversion over
`C.functions`, plus for `top_annotated` the length, `openFull`, and `AnnotCompat`
obligations already discussed.

- **Type-directed mode**: pick an operator whose recorded type *matches* (or, via
  `top_annotated`, *instantiates to*) the target `τ` — a filtered container
  inversion keyed on the value side.

**New capabilities needed**: container inversion (shared with `tvar`); `Except`
result inversion (`f.type = .ok ty` — compute when `f` is known).

---

## Cross-cutting issue: coercion noise from proof-carrying types

Many conclusions wrap subterms in proof-carrying coercions:
`LTy.toMonoType x_ty hx`, `(h1 : LTy.isMonoType t1)`, `.tcons "arrow" [toMonoType …, toMonoType …]`.

In **synthesis mode** these are not a problem: the coercions are plain function
applications of values Specimen has already produced, so the unifier just
*evaluates* them to build the conclusion — no unfolding required.

In **type-directed mode**, where the deriver must pattern-match a *given* target
type against `… .tcons "arrow" [toMonoType …, …] …`, it must relate the target's
structure to the coerced subterms. The need is to **invert the coercion** — produce
a `ty`/`x_ty` whose `toMonoType` matches a given monotype — which is a bucket-1
producer-synthesis obligation (consistent with the design principle above: supply a
producer, don't unfold the `def`).

**Capability needed**: bucket-1 producer synthesis for the coercion inverse
(type-directed mode only); nothing in synthesis mode.

---

## Summary table

| Constructor | Synthesis mode | Type-directed mode | New capability needed |
|---|---|---|---|
| `t*_const` | trivial | trivial (τ selects rule) | none |
| `tvar` | container inversion | filtered container inversion | container-membership generation |
| `tvar_annotated` | + length, openFull, AnnotCompat | same | length-directed list gen; delegated opaque-existential synthesis |
| `tabs` | binder inversion, freshness | + invert arrow target | binder-aware varOpen/varClose; disjunction branch-selection |
| `tapp` | generate arg type, recurse | generate hidden arg type | LMonoTy producer |
| `tinst`/`tgen`/`talias` | droppable | possibly required | coercion-rule control (bound/exclude) |
| `tif` | structural | structural | none |
| `teq` | generate branch type | only fires at .bool; gen branch type | LMonoTy producer |
| `tquant` | as tabs ×2 subterms | as tabs ×2 | shared-binder coordination |
| `top`/`top_annotated` | container inversion over functions | filtered | container inversion; Except inversion |

## Backlog

The reusable capabilities motivated by this case study are enumerated in the
**Summary** at the top of this document (buckets 0–2). The per-constructor
"New capabilities needed" notes above map each constructor onto those buckets.
For the mechanism behind bucket 1, see `Delegated-producer-synthesis.md`; for the
end-to-end use-case framing and the three blockers (A: opaque defs, B:
generate-and-check blowup, C: structure-parameter projection), see
`SpecimenTest/LExprGen.lean`.

For the specific case of generating expressions that **call library functions
from a Strata `Factory`** (the `top`/`top_annotated` container producers in their
most consequential application — the Pałka-et-al. "Indir" generation rule), see
`Factory-directed-generation.md`, grounded in lessons from a prior hand-written
`LExpr` generator and the experiment
`SpecimenTest/Experiments/FactoryDrawExp.lean`. That analysis shows bucket 1's
container inversion is *expressible* today but loses to the trivial base case
without (a) result-type-directed selection and (b) distribution weighting.
