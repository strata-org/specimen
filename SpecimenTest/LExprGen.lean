import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Gen
import Plausible.Arbitrary

/-! # Generator for well-typed Strata `LExpr`s

This file is a stub for deriving an `ArbitrarySizedSuchThat` instance for
`LExpr`s satisfying the `HasType` relation from Strata
(`Strata.DL.Lambda.LExprTypeSpec`).

## Required Strata imports (not yet available as a dependency)

To actually compile this file, we would need to add `Strata` as a dependency in
`lakefile.toml` and import:

```
import Strata.DL.Lambda.LExpr          -- the `LExpr` datatype
import Strata.DL.Lambda.LExprTypeSpec  -- the `HasType` relation
import Strata.DL.Lambda.LTy            -- `LMonoTy`, `LTy`
import Strata.DL.Lambda.Identifiers    -- `Identifier`
```

## Goal

We want to derive:
```
derive_generator (fun (C : LContext T) (Γ : TContext T.IDMeta) (τ : LTy) =>
  ∃ (e : LExpr T.mono), HasType C Γ e τ)
```

i.e., given a context `C`, a type environment `Γ`, and a target type `τ`,
generate an `LExpr` that is well-typed at type `τ`.

Specimen already derives a generator for a *very similar* relation — the STLC
`typing` judgement (see `SpecimenTest/DeriveArbitrarySuchThat/DeriveSTLCGenerator.lean`
and `SpecimenTest/CommonDefinitions/STLCDefinitions.lean`). Strata's `HasType`
is a Hindley-Milner system over a locally-nameless term language, which is
richer. The analysis below is grounded in experiments (see
`SpecimenTest/Experiments/`) that exercise each suspicious feature on small
inductive relations, so we can tell apart what *cannot be derived* from what
*derives but generates poorly*.

## What already works (verified experimentally)

Several features I initially assumed were unsupported turn out to be handled by
Specimen's existing **generate-and-check** strategy: when a hypothesis
constrains a value Specimen cannot invert, it generates the value with
`Arbitrary.arbitrary` and then discharges the hypothesis with a `DecOpt` check,
backtracking on failure. Concretely:

- **Bool-valued function side-conditions** (`Experiments/FuncEqExp.lean`):
  `isSmall n = true`, and `LTy.isMonoType x_ty`-shaped conditions, compile to
  `let n ← arbitrary; match DecOpt.decOpt (isSmall n = true) ... ` — i.e. they
  *do* derive, via generate-and-check.

- **Freshness / non-membership** (`Experiments/FreshExp.lean`): `x ∉ l`
  compiles to `DecOpt.negOpt (DecOpt.decOpt (x ∈ l))`. This is the *same*
  mechanism as the Bool side-conditions above — confirming that
  `LExpr.fresh x e` (`:= x ∉ freeVars e`) is **not** a different kind of issue
  from `LTy.isMonoType`. Both are decidable side-conditions discharged by a
  `DecOpt`/`negOpt` check, provided the predicate is *reducible* (see the big
  caveat below).

- **Container lookups** (`Experiments/FuncEqExp.lean`): `lookupNat l k = some v`
  derives — Specimen generates `k`, computes `lookupNat l k`, and matches the
  result against `some v`. So `Γ.types.find? x = some ty` (Strata's `tvar`) is
  expressible. It is *inefficient* (random `k` rarely hits a sparse map), but
  not unsupported.

- **Recursive calls on a transformed output** (`Experiments/TransformedRecExp.lean`):
  a constructor that recurses on `Good (wrap inner)` (an output passed through a
  function) derives — `inner` is generated unconstrained and `Good (wrap inner)`
  is checked. This is the shape of `HasType C Γ' (LExpr.varOpen 0 x e) e_ty` in
  `tabs`/`tquant`. Again: derivable, but the generated code is *very* inefficient
  (in the experiment it produced only the base case, because random `inner`
  almost never satisfied the check).

- **Non-syntax-directed / subsumption rules** (`Experiments/HardCasesExp.lean`):
  a constructor `inst : HasT e τ → HasT e τ'` that recurses on the *same* term
  with no structural decrease derives fine and **terminates**, because the
  size/fuel parameter is decremented on the recursive call regardless of
  structural decrease. So `tinst`/`tgen`/`talias` will not cause infinite loops
  — they just add (often unproductive) backtracking branches.

- **Disjunctive hypotheses** (`Experiments/HardCasesExp.lean`): `n = 0 ∨ n = 1`
  compiles to a single `DecOpt.decOpt (Or ...)` check. So the
  `o = none ∨ ∃ t, o = some t ∧ ...` hypothesis in `tabs` is handled as a check
  (again, generate-and-check on whatever `o` is, rather than a smart inversion).

The upshot: **most of `HasType` will "derive" today** in the sense of producing
a well-typed `ArbitrarySizedSuchThat` instance, *if* the prerequisite
`DecOpt`/`Arbitrary`/`ArbitrarySizedSuchThat` instances exist for the
sub-predicates and external types.

## The genuine blockers

### Blocker A (feasibility): opaque `def`-wrapped predicates in hypotheses

This is the real obstacle and it is well-defined. Specimen only "looks inside" a
hypothesis predicate if that predicate is **reducible** (`whnf` unfolds it). It
reduces `abbrev`s and structure projections, but **not** ordinary `def`s.

Verified (`Experiments/DefWrappedExp.lean` vs. the `abbrev` variant):
- `abbrev freshAbbrev x l := x ∉ myFreeVars l` in a hypothesis → unfolds, derives
  via `negOpt`.
- `def freshDef x l := x ∉ myFreeVars l` in a hypothesis → Specimen treats it
  opaquely and emits a requirement for
  `ArbitrarySizedSuchThat Nat (fun x => freshDef x l)`, which has no instance →
  `failed to synthesize instance` error.

This directly affects Strata, where the relevant predicates are `def`s, not
`abbrev`s:
- `LExpr.fresh x e := x ∉ freeVars e`  — a `def : Prop`
- `AnnotCompat aliases ann xty := ∃ σ, AliasEquiv aliases (subst σ ann) xty`
  — a `def : Prop` whose body is moreover an **existential** (verified separately
  in `Experiments/ExistsHypExp.lean`: a `def P := ∃ k, ...` used as a hypothesis
  also fails to synthesize an instance).

**Feature needed: a producer for the predicate as written** (whether supplied by
hand or by the delegated-synthesis mechanism — see `Delegated-producer-synthesis.md`).
Provide a `DecOpt`/`ArbitrarySizedSuchThat` instance for `LExpr.fresh`,
`AnnotCompat`, etc., keyed on the *opaque* predicate. This is the workaround
available today (hand-written instances; `derive_mutual` + `autoDeriveDeps` can
derive some if their bodies are inductive) and is also exactly the obligation the
external backend fills in the longer term.

**Why not configurable unfolding?** An earlier draft proposed letting the user
unfold named `def`s before analysis. That does *not* help for the defs that block
`HasType`. Unfolding `AnnotCompat` exposes `∃σ, AliasEquiv …`, which still needs an
external producer — so you might as well attach the producer to `AnnotCompat`
directly. Unfolding `LExpr.fresh` exposes `x ∉ freeVars e`, which Specimen handles
only via *generate-and-check* (`negOpt`/`decOpt`) — the inefficient path the
freshness producer is meant to replace, so unfolding steers toward the worse
option. Unfolding genuinely helps only for the shape `a = g(inputs)` (which the
unifier could then evaluate without any producer), and no problematic `HasType`
def has that shape. The rule is: **supply/synthesize a producer for the predicate
as written; do not unfold it.**

### Blocker B (practicality): explosive generate-and-check on the hard cases

Even once Blocker A is resolved, the *quality* of the derived generator is the
real problem. The cases above all rely on generating a value blindly and
checking a constraint:
  - `tabs` generates an abstraction body `e`, opens it (`varOpen 0 x e`), and
    checks the recursive typing — random bodies rarely typecheck.
  - `tvar` would generate a random identifier and check `Γ.types.find? x = some ty`
    — random identifiers rarely hit the context.
  - `tinst`/`tgen`/`talias` add unproductive branches that mostly fail their
    checks.

The `TransformedRecExp` experiment makes this concrete: the derived generator
was *correct* but produced essentially only trivial values. For `HasType`, a
generate-and-check generator would almost never produce a non-trivial well-typed
term within a reasonable size/fuel budget.

**Feature needed:** smarter, *constraint-directed* generation for these shapes,
rather than generate-and-check:
  - Generating identifiers/types **from the context** (`tvar`): treat
    `Γ.types.find? x = some ty` as "pick `(x, ty)` from `Γ.types`", i.e. invert a
    finite-map lookup instead of guessing keys. This requires Specimen to
    recognise container-membership hypotheses and enumerate the container.
  - Bounding/deprioritising non-syntax-directed coercion rules
    (`tinst`/`tgen`/`talias`) so they don't dominate the backtracking budget.
  - For locally-nameless binders (`tabs`/`tquant`), generating the *opened* body
    directly and recovering the closed form, rather than generating a closed body
    and checking after `varOpen`.

### Blocker C (feasibility): output type is a projection of a structure parameter

`HasType` is parameterized by `{T : LExprParams}` and the generated term has
type `LExpr T.mono` — i.e. the *type of the value being generated is a
projection of the structure-valued parameter `T`*. Verified
(`Experiments/StructParamExp.lean`), this is the one "lesser issue" that turns
out to be a real blocker:

- Plain type parameter, output type *is* the parameter (`α : Type`, `x : α`):
  **works** (baseline, cf. the `Foo` example in `DeriveSTLCGenerator.lean`).
- `Type 1` structure with a type-valued field, output arg has a *fixed* type
  (`Nat`): **works** — so structure parameters and `Type 1` per se are fine.
- Structure parameter, output type is a *projection* (`p : PE`, `x : p.Elem`):
  **fails at derivation time** with `error: unknown free variable p_1`. A
  `Type 0` structure suffices to trigger it, so it is not a universe problem.

**Crucially, this is a limitation of the *constrained-producer* path only, not
of structure parameters in general.** The unconstrained `deriving Arbitrary`
handler (`Specimen/DeriveArbitrary.lean`) *does* handle structure parameters with
projected type-valued fields — see the passing test
`SpecimenTest/DeriveArbitrary/StructureParameterTest.lean` (covering `T.Meta`
projections, mixed type+structure params, nested structures, and a graceful
rejection of non-Type fields). `Experiments/StructParamPathsExp.lean` exercises
both paths on the *same* structure-parameter type with the *same* projected field
`T.Elem`: `deriving Arbitrary` succeeds, `derive_generator` fails with
`unknown free variable T_1`.

Root cause: the constrained deriver freshens the parameter name (`p ↦ p_1`) but
does not consistently re-bind it inside the projected output type, so the
generated instance header references an out-of-scope `p_1`. This fails *earlier*
than Blockers A/B (during instance construction, before any code is emitted). The
fix is therefore well-scoped: **port the parameter-handling logic that already
works in `DeriveArbitrary.lean` into the constrained path** (`derive_generator` /
`derive_enumerator` / `derive_mutual`), rather than inventing new machinery.

Strata hits this directly: the existential output `∃ e : LExpr T.mono, …` has a
type that is a projection of `T`.

**Feature needed**: fix output-type handling in the *constrained* deriver so
projections of (freshened) parameters remain in scope — a derivation-machinery
bug fix (porting existing `DeriveArbitrary.lean` logic), independent of the
producer-synthesis work. Until then, the workaround is to *specialize `T`* to a
concrete `LExprParams` (e.g. `Unit` metadata) before deriving, so `LExpr T.mono`
reduces to a closed type with no projection.

### Genuinely lesser issues (verified to work)

- **Record-update syntax** in hypotheses (`{ Γ with types := Γ.types.insert ... }`):
  **verified to work** (`Experiments/RecordUpdateExp.lean`). It appears in an
  *input* position of the recursive call, so it is only constructed, never
  inverted, and derivation succeeds.
- **Rich external types** (`LMonoTy`, `LTy`): **verified** —
  `deriving Arbitrary` handles `LMonoTy'`/`LTy'`-shaped recursive inductives,
  including nested recursion through `List` and `Nat`/`String` fields
  (`Experiments/RichTypesExp.lean`). `TContext`/`LContext` contain maps and would
  still need either custom `Arbitrary` instances or (better) context-directed
  generation.

## Corrected summary

| Concern | Earlier claim | Verified reality |
|---|---|---|
| `LExpr.fresh` vs `isMonoType` | two different issues | **same** issue: decidable side-conditions, both handled by generate-and-check on a *reducible* predicate |
| Function-call / container equalities | partial / unsupported | **supported** via generate-and-check (inefficient) |
| Transformed recursive args (`varOpen`) | unsupported, high difficulty | **derives** via generate-and-check; problem is efficiency, not feasibility |
| Non-syntax-directed rules | infinite loop risk | **terminate** thanks to size/fuel; just add backtracking |
| Disjunctive hypotheses | unsupported | **supported** as a single `DecOpt` check |
| `def`-wrapped Prop hypotheses | (missed) | **genuine feasibility blocker** — opaque; needs a supplied/synthesized producer for the predicate as written (NOT unfolding) |
| Existential inside a hypothesis def | (missed) | same blocker — needs a supplied instance |
| Structure-valued implicit params | "lesser issue, likely fine" | **WRONG — genuine blocker** in the *constrained* path when output type is a projection (`LExpr T.mono`); derivation-time `unknown free variable` bug. The *unconstrained* `deriving Arbitrary` path already handles it — fix = port that logic |
| Record-update syntax in hypotheses | "expected to work" | **verified to work** |
| Rich recursive types (`LMonoTy`/`LTy`) | "should work" | **verified to work** |

## Recommended path forward

1. **Near term (no Specimen change):** add `Strata` as a dependency;
   **specialize `T` to a concrete `LExprParams`** (e.g. `Unit` metadata) so that
   `LExpr T.mono` reduces to a closed type — this sidesteps Blocker C, which
   would otherwise abort derivation outright. Then provide hand-written
   `DecOpt`/`Arbitrary` instances (or `derive_mutual` derivations) for the opaque
   sub-predicates `LExpr.fresh`, `AnnotCompat`, `LTy.isMonoType`, `AliasEquiv`,
   plus `Arbitrary` for `LMonoTy`/`LTy`/`Identifier`. With both in place,
   `derive_generator`/`derive_mutual` on the specialized `HasType` should
   *type-check and run*. It will, however, be a poor generator (Blocker B).

2. **Medium term (highest-impact Specimen features):**
   - **Fix projected-output-type handling** (Blocker C) so structure-parameter
     projections like `LExpr T.mono` stay in scope — removes the need to
     specialize `T` and is a prerequisite for the fully general relation.
   - **Delegated producer synthesis** (resolves Blocker A) — a producer for each
     opaque predicate (`LExpr.fresh`, `AnnotCompat`, …) as written, supplied by
     hand or by the external backend. See `Docs/Delegated-producer-synthesis.md`.
   - **Container-membership–directed generation** so `tvar`-style
     `find? x = some ty` hypotheses generate from the context instead of guessing
     (the single biggest win for generator quality; an instance of the above).
   - **Coercion-rule control** to bound `tinst`/`tgen`/`talias`.

These conclusions are reproducible from the files under
`SpecimenTest/Experiments/`.
-/
