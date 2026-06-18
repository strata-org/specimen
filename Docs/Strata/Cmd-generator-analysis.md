# `Cmd` Generator Analysis

This document extends `HasType-constructor-analysis.md` from Strata's *expression*
layer (`LExpr`/`HasType`) to its *imperative* layer: the `Cmd` datatype
(`Strata/DL/Imperative/Cmd.lean`) and its type checker
(`Strata/DL/Imperative/CmdType.lean`). The goal is the same — identify what
Specimen needs in order to synthesize generators of well-typed `Cmd`s — but the
imperative layer has a different shape, and the most important findings are about
those structural differences, not a constructor-by-constructor repeat.

> Grounding note. Unlike the `HasType` analysis, there is **no inductive typing
> relation** to walk constructor-by-constructor here. Strata typechecks commands
> with a *function*, `Cmd.typeCheck`, defined against a `TypeContext` typeclass.
> So this analysis has two halves: (A) what generating `Cmd`s needs *today*, given
> only the function checker; and (B) what an inductive `HasType`-equivalent for
> `Cmd` would look like *if/when one is written*, and how its constructors map
> onto the capability buckets from the `HasType` analysis. The source signatures
> below were reconstructed from the Strata repository on GitHub (Apache-2.0/MIT);
> they should be re-checked against a pinned revision before any code is written.

## The objects

```lean
-- Strata/DL/Imperative/PureExpr.lean
structure PureExpr : Type 1 where
  Ident        : Type
  EqIdent      : DecidableEq Ident
  Expr         : Type
  Ty           : Type
  ExprMetadata : Type
  TyEnv        : Type
  TyContext    : Type
  EvalEnv      : Type

-- Strata/DL/Imperative/Cmd.lean
inductive ExprOrNondet (P : PureExpr) where
  | det (e : P.Expr)
  | nondet

inductive Cmd (P : PureExpr) where
  | init   (name : P.Ident) (ty : P.Ty) (e : ExprOrNondet P) (md : MetaData P)
  | set    (name : P.Ident) (e : ExprOrNondet P)             (md : MetaData P)
  | assert (label : String) (b : P.Expr)                     (md : MetaData P)
  | assume (label : String) (b : P.Expr)                     (md : MetaData P)
  | cover  (label : String) (b : P.Expr)                     (md : MetaData P)

abbrev Cmds (P : PureExpr) := List (Cmd P)
```

```lean
-- Strata/DL/Imperative/TypeContext.lean  (the abstracted expression checker)
class TypeContext (P : PureExpr) (Context TypeEnv TypeError : Type) where
  isBoolType  : P.Ty → Bool
  freeVars    : P.Expr → List P.Ident
  preprocess  : Context → TypeEnv → P.Ty → Except TypeError (P.Ty × TypeEnv)
  postprocess : Context → TypeEnv → P.Ty → Except TypeError (P.Ty × TypeEnv)
  update      : TypeEnv → P.Ident → P.Ty → TypeEnv
  lookup      : TypeEnv → P.Ident → Option P.Ty
  inferType   : Context → TypeEnv → Cmd P → P.Expr → Except TypeError (P.Expr × P.Ty × TypeEnv)
  unifyTypes  : TypeEnv → List (P.Ty × P.Ty) → Except TypeError TypeEnv
  typeErrorFmt : TypeError → Std.Format

-- Strata/DL/Imperative/CmdType.lean  (the command checker, generic over the above)
def Cmd.typeCheck  [TypeContext P C T DiagnosticModel] (ctx : C) (τ : T) (c : Cmd P)
  : Except DiagnosticModel (Cmd P × T)
def Cmds.typeCheck [TypeContext P C T DiagnosticModel] (ctx : C) (τ : T) (cs : Cmds P)
  : Except DiagnosticModel (Cmds P × T)
```

---

## Summary: what Specimen needs (and what's new vs. `HasType`)

The `HasType` analysis collapsed its needs into three buckets: **0** (fix
structure-parameter projection in the constrained deriver), **1** (delegated
producer synthesis — container inversion, freshness, opaque-predicate producers),
and **2** (scheduler knobs — disjunction branch-selection, coercion control). The
`Cmd` layer **reuses all three** and adds structural concerns of its own. The
headline findings:

**A. The structure parameter is now everywhere, not just in the output type.**
For `HasType`, the structure-parameter blocker (bucket 0) showed up in *one*
place: the generated term had type `LExpr T.mono`. For `Cmd P`, *every field of
every constructor is a projection of the structure parameter `P`*: `P.Ident`,
`P.Ty`, `P.Expr`, `MetaData P`. So bucket 0 (porting `DeriveArbitrary.lean`'s
parameter handling into the constrained path) is not merely a prerequisite — it
is load-bearing for the *entire* `Cmd` type. And worse than for `LExpr`: `P.Expr`
and `P.Ty` are **opaque** `Type`s with no constructors of their own (they are
*interface* fields), so there is nothing to generate until `P` is instantiated.
**`P` must be specialized to a concrete `PureExpr`** (e.g. the Lambda dialect, so
`P.Expr = LExpr …` and `P.Ty = LMonoTy`) before a `Cmd` generator means anything.
This is the same "specialize `T`" workaround the `HasType` doc recommends, but
here it is mandatory rather than a convenience, because the structure fields are
the value space. The general (un-specialized) bucket-0 fix also has to be broader
for `Cmd` than for `LExpr` — see *What bucket 0 must do to cover `Cmd`* below,
grounded in `SpecimenTest/StrataExperiments/StructParamCmdShapeExp.lean`.

**B. There is no inductive relation — typechecking is a function returning
`Except`.** This is the deepest difference. Specimen derives constrained producers
by *scheduling the hypotheses of an inductive relation's constructors*. `Cmd` has
no such relation; `Cmd.typeCheck` is a recursive `def` that threads a state and
returns `Except`. Two consequences:
  - *Today*, the only relation Specimen can target is the **function-equality
    predicate** `CmdWT ctx τ c τ' := Cmd.typeCheck ctx τ c = .ok (c', τ')`. With
    `c` as an output this is pure **generate-and-check**: generate a `Cmd`, run
    `typeCheck`, keep the `.ok` ones. This is feasible (decidable, since `Except`
    equality is decidable) but is exactly the low-quality path the `HasType`
    analysis warns against — and it is *worse* here because the checker calls into
    the abstract `TypeContext` methods, which are opaque `def`s/typeclass methods
    Specimen cannot invert (Blocker A, at relation granularity).
  - *To do better*, someone must write an **inductive `HasType`-equivalent for
    commands** whose constructors expose the obligations (lookup, freshness,
    unify, sub-expression typing) as schedulable hypotheses. Section B below
    sketches that relation and shows its constructors land squarely in buckets
    1 and 2 — i.e. once the relation exists, the `Cmd` layer needs *no new
    Specimen capability beyond what `HasType` already motivated*, plus the two
    genuinely-new items C and D.

**C. State threading is a new shape (the `TypeEnv` transformer).** `HasType` has
a *fixed* context `Γ`. Command typing **updates** the environment: `init`/`set`
add or use bindings, and `Cmds.typeCheck` threads the env left-to-right through a
list (a fold). So the natural relation is a **state-transformer relation**
`CmdsWT : Context → TypeEnv → Cmds → TypeEnv → Prop` (input env *and* output env).
For Specimen this is a sequential/telescoping generation pattern: each command's
*output* env is the next command's *input* env. Synthesis mode
(`+ctx, +τ_in, −cmds, −τ_out`) is a clean left-to-right fold and is in reach.
The env-directed analog (`−cmds` given both `τ_in` and `τ_out` — "generate a
command sequence that transforms env A into env B") makes the output env an
*input*, which is the harder, less-supported mode (analogous to type-directed
`HasType`).

**D. The command checker delegates to the expression checker.** `init`/`set`
call `inferType`; `assert`/`assume`/`cover` call `inferType` + `isBoolType`.
So a `Cmd` generator **depends on** an expression generator — concretely, the
`HasType` generator from the prior analysis, when `P` is the Lambda dialect. This
is the *layered/delegated producer story at relation granularity*: command typing
is a client of expression typing. Everything in the `HasType` analysis is a
prerequisite subroutine; the `Cmd` layer adds only state threading (C), env
lookup/update/freshness (bucket 1 — same container + freshness machinery), and a
bool-type guard.

In one line: **`Cmd` needs bucket 0 even more acutely than `HasType` (specialize
`P`), reuses bucket 1 wholesale (lookup inversion, freshness, delegated
sub-expression typing), reuses bucket 2 (the `det`/`nondet` and declared/undeclared
choice points), and adds two genuinely new concerns — a state-transformer relation
shape and cross-relation delegation to the expression generator — neither of which
is a *producer*-synthesis problem.**

---

## Two (three) generation modes

Mirroring the `HasType` doc, but the state makes it three:

- **Synthesis mode** `CmdsWT(+ctx, +τ_in, −cmds, −τ_out)` — "produce a well-typed
  command sequence and the env it leaves behind." Closest to "give me arbitrary
  well-typed programs." A clean left-to-right fold; the output env is just
  computed as we go. This is the mode to target first.
- **Env/postcondition-directed** `CmdsWT(+ctx, +τ_in, −cmds, +τ_out)` — "produce a
  sequence that ends in a *specific* env." The output env is now an input; the
  last command must be inverted to hit it. Analogous to (and as hard as)
  type-directed `HasType`, and rarely needed for PBT.
- **Expression-type-directed**, *within* a single command — when generating the
  `assert b` body, do we synthesize *any* well-typed `b` (then check
  `isBoolType`) or generate `b` *at* the bool type via a type-directed expression
  producer? The latter is strictly better and is exactly the `HasType`
  type-directed mode applied to the sub-expression.

`md` (metadata, `MetaData P`) is an output with a trivial `Arbitrary`/unit
instance and is ignored throughout, as in `HasType`.

---

# Part A — Generating `Cmd`s against the function checker (today)

With no inductive relation, the only target is the decision predicate
`Cmd.typeCheck ctx τ c = .ok …`. Findings:

- **Feasible but generate-and-check.** `Except`-equality is decidable, so Specimen
  can derive a `DecOpt`-style checker and run generate-and-check: produce a random
  `Cmd P` (requires `Arbitrary (Cmd P)`, which requires a concrete `P` — finding
  A), run `typeCheck`, keep `.ok`. This is the `FuncEqExp.lean` shape (a
  function-result equality) from the StrataExperiments, lifted to a `Cmd`.
- **The checker is opaque to inversion.** `typeCheck` is a `def` that calls
  `TypeContext` *typeclass methods* (`inferType`, `unifyTypes`, `lookup`, …).
  These are even more opaque than the `def`-wrapped predicates of Blocker A: they
  are abstract members with no body at all until an instance is fixed. Specimen
  cannot look inside them; it can only call them. So there is no mode-directed
  inversion to be had from the function form — generate-and-check is the ceiling.
- **Quality will be poor for the same reasons as `HasType`.** A random `Cmd`
  rarely typechecks: `set x e` needs `x` already declared (random `x` misses the
  env), `init x` needs `x` *not* declared and `x ∉ freeVars e`, and the embedded
  expression `e : P.Expr` must itself be well-typed (random expressions almost
  never are — the whole premise of the `HasType` work).

**Conclusion for Part A:** generating `Cmd`s from the function checker is possible
once `P` is concrete (finding A) and an `Arbitrary`/`DecOpt` exists for the
concrete command and expression types, but it is pure generate-and-check stacked
*on top of* the already-hard expression generation problem. To get quality, you
want Part B.

---

# Part B — Anticipating an inductive `HasType`-equivalent for `Cmd`

Suppose Strata (or we) write an inductive relation mirroring `Cmd.typeCheck`,
exposing each obligation as a hypothesis so Specimen can schedule it. A faithful
shape would be a **state-transformer relation** (finding C):

```
CmdWT  : Context → TypeEnv → Cmd P  → TypeEnv → Prop      -- one command
CmdsWT : Context → TypeEnv → Cmds P → TypeEnv → Prop      -- a sequence
```

The sequence relation has the obvious two constructors (the fold of finding C):

```
| nil  : CmdsWT ctx τ [] τ
| cons : CmdWT ctx τ c τ' → CmdsWT ctx τ' cs τ'' → CmdsWT ctx τ (c :: cs) τ''
```

`cons` threads the env: the head produces `τ'`, the tail consumes it. In synthesis
mode this is a left-to-right producer fold — **in reach today** (it is structurally
a list generator where each step's output is the next step's input; no inversion).
Env-directed mode (τ'' an input) must invert the last step — harder, bucket-1-ish.

The single-command constructors, reading off the `typeCheck` cases:

### `init` — declare a fresh variable

```
| init_det :
    lookup τ x = none →                       -- x must be UNDECLARED
    x ∉ TC.freeVars e →                        -- no self-reference
    ExprWT ctx τ e ty_e →                      -- the initializer typechecks (delegated)
    unify (ty, ty_e) τ = .ok τ₁ →              -- declared type unifies with inferred
    update τ₁ x ty = τ₂ →                      -- env gains x : ty
    CmdWT ctx τ (.init x ty (.det e) md) τ₂
| init_nondet :
    lookup τ x = none →
    update τ x ty = τ₂ →
    CmdWT ctx τ (.init x ty .nondet md) τ₂
```

- `lookup τ x = none` — a **negative** container constraint: "produce a key *not*
  in the env." This is *freshness over the environment* — the same shape as
  `LExpr.fresh`/`x ∉ freeVars e` (bucket 1, prototype #1: compute the keys, return
  one not among them). **Container-membership generation in its negative form.**
- `x ∉ TC.freeVars e` — literally the freshness producer from
  `Delegated-producer-synthesis.md`, but note the dependency order: it depends on
  `e`, so it is scheduled *after* the initializer is produced.
- `ExprWT ctx τ e ty_e` — **delegated to the expression generator** (finding D);
  this is a recursive call into the `HasType`-style producer. In synthesis mode it
  synthesizes `e` and `ty_e`; in expression-type-directed mode it would be driven
  by `ty`.
- `unify (...) = .ok τ₁` and `update ... = τ₂` — outputs that are **computable
  functions of inputs** (the easy "output computable from inputs" case from
  `Delegated-producer-synthesis.md`): once `ty`, `ty_e`, `x` are known, `τ₁`/`τ₂`
  are computed, not guessed. *Known/in scope.*

### `set` — assign to a declared variable

```
| set_det :
    lookup τ x = some ty →                     -- x must be DECLARED (positive lookup!)
    ExprWT ctx τ e ty_e →
    unify (ty, ty_e) τ = .ok τ₁ →
    CmdWT ctx τ (.set x (.det e) md) τ₁
| set_nondet :
    lookup τ x = some ty →
    CmdWT ctx τ (.set x .nondet md) τ          -- nondet is a no-op on the env
```

- `lookup τ x = some ty` — the **positive container inversion** of `tvar`
  (`Γ.types.find? x = some ty`): produce `(x, ty)` by enumerating the env's
  bindings instead of guessing `x`. *Exactly* bucket 1's highest-value container
  producer, reused verbatim. Note `set` is the mirror of `init`: `init` wants a
  key *absent*, `set` wants a key *present* — the negative and positive forms of
  the same container producer.
- The remaining hypotheses are delegated expression typing + computable unify, as
  in `init`.

### `assert` / `assume` / `cover` — boolean side-conditions

```
| assert :
    ExprWT ctx τ b ty_b →
    TC.isBoolType ty_b = true →
    CmdWT ctx τ (.assert label b md) τ          -- env unchanged
  -- assume, cover: identical shape, different head constructor & semantics
```

- `ExprWT ctx τ b ty_b` — delegated expression typing again.
- `isBoolType ty_b = true` — a decidable `Bool` guard. *Generate-and-check works*
  (it is the `FuncEqExp` shape), but the **better** path is expression-type-directed
  generation: produce `b` *at* the bool type directly (drive `ExprWT` with the
  target `bool`), so the guard is satisfied by construction rather than filtered.
  This is the in-command type-directed mode of the modes section.
- `label : String` is a free output (plain `Arbitrary`); env is unchanged
  (`τ` out = `τ` in).

### `ExprOrNondet` and the cheap-branch choice

`init` and `set` each split on `det e` vs `nondet`. `nondet` is the **cheap
branch**: it discharges *no* expression-typing or unify obligation — only the
lookup constraint. This is precisely the `tabs` `o = none ∨ …` situation (bucket
2): a scheduler that can **prefer the cheap branch** will emit `nondet`
initializers/assignments cheaply and only pay for `det` when expression generation
is warranted. Here the choice is at the *constructor* level (two rules) rather
than a `∨` inside one rule, so it may fall out of ordinary constructor selection —
but the *coverage* concern is the same: without weighting, a generator could
drown in `nondet` and never exercise expression typing, or vice-versa. This is the
same **branch/weight control** knob, applied to constructor choice.

### Mapping to the buckets

| `Cmd` obligation | Shape | Bucket / status |
|---|---|---|
| `lookup τ x = none` (`init`) | negative container membership | **1** — freshness-over-env (prototype #1 form) |
| `x ∉ freeVars e` (`init`) | freshness | **1** — the canonical freshness producer |
| `lookup τ x = some ty` (`set`) | positive container inversion | **1** — the `tvar` container producer, reused |
| `ExprWT … e ty_e` (init/set/assert/…) | recursive call into expression typing | **D** — cross-relation delegation (= the whole `HasType` generator) |
| `unify … = .ok τ₁`, `update … = τ₂` | output computable from inputs | **known** — easy filter; compute, don't guess |
| `isBoolType ty_b = true` (assert/…) | decidable Bool guard | **known** (gen-and-check) or better, expression-type-directed |
| `det` vs `nondet` choice | constructor/branch selection | **2** — prefer/weight the cheap branch |
| env threading in `cons` | state-transformer fold | **C** — new shape; synthesis = fold (in reach) |
| `Cmd P` fields are `P.{Ident,Ty,Expr}` | structure-parameter projection | **0** — specialize `P` (mandatory here) |

**The punchline:** every per-constructor obligation of an inductive `Cmd` typing
relation is *already* covered by buckets 0–2 of the `HasType` analysis (mostly
bucket 1's container + freshness producers, plus delegation to the expression
generator). The only genuinely new items are **C** (the state-transformer relation
shape / env-threading fold) and **D** (cross-relation delegation), and *neither is
a producer-synthesis problem* — C is a scheduling/relation-shape concern and D is
"the expression generator must already exist and be callable as a sub-producer."

---

## What bucket 0 must do to cover `Cmd`

`Cmd` exercises the structure parameter in two ways that `LExpr` does not, so the
bucket-0 fix has to be broader than handling a projected *output* type. Both are
isolated at minimal size in `SpecimenTest/StrataExperiments/StructParamCmdShapeExp.lean`
(run on Lean `v4.30.0-rc1`).

**Shape 1 — projections live in constructor-argument positions.** A `CmdWT`
relation's output type is `Cmd P` (the parameter *applied*), while `P.Ident` /
`P.Ty` / `P.Expr` are the types of values *generated inside* the constructor body.
The experiment's `MiniCmdWT (P : PEpure) : MiniCmd' P → Prop` (output `MiniCmd' P`;
hypothesis outputs `name : P.Ident`, `e : P.Expr`) fails in two ways:

  - **No instance binders for the structure parameter.** The generated inner
    `aux_arb` calls `Arbitrary.arbitrary` for `name : P_1.Ident` and `e : P_1.Expr`,
    but no `[Arbitrary P.Ident]`/`[Arbitrary P.Expr]` binders are emitted, so
    instance synthesis fails. The cause is in
    `Specimen/MakeConstrainedProducerInstance.lean`: it emits `[Arbitrary _]` /
    `[DecidableEq _]` binders only for parameters where `paramType.isSort` (lines
    141, 267, 310). A structure parameter `P : PureExpr` is not a sort, so it gets
    no instance binders.
  - **The structure parameter is mis-applied as an explicit constructor argument.**
    The body emits `MiniCmd'.set P_1 name e`, passing `P_1` positionally to a
    constructor that expects `P` *implicit* — yielding `Function expected` /
    `Application type mismatch` errors.

**Shape 2 — `PureExpr` has mixed Type / non-Type fields.** The unconstrained
`deriving Arbitrary` path's `expandStructBinders` is all-or-nothing: it errors on
the first field that is not a Type-or-structure-of-Types. `PureExpr` bundles
`EqIdent : DecidableEq Ident` and `TyEnv`/`TyContext`/`EvalEnv` alongside its Type
fields, so this path *rejects* a `PureExpr`-shaped parameter outright (verified:
`structure parameter 'P✝' has a field of type 'DecidableEq P.Ident', which is not
a Type or structure of Types`), even though only `Ident`/`Ty`/`Expr` need
`[Arbitrary _]` binders.

So the bucket-0 fix has four parts:

1. **Emit instance binders for structure parameters, not only `isSort` parameters.**
   In the constrained deriver, expand a structure-of-Types parameter into per-field
   `[Arbitrary P.field]` (and `[DecidableEq …]`) binders on the emitted def/instance
   — the same expansion the unconstrained path performs. This is the dominant
   `Cmd`-shape failure.
2. **Make field expansion selective and tolerant of non-Type fields.** Expand only
   the Type-valued fields the relation consumes, and treat a `DecidableEq` field as
   the *source* of the `[DecidableEq P.Ident]` instance rather than an error.
3. **Thread the structure parameter as an implicit constructor argument**, so the
   body emits `MiniCmd'.set name e`, not `MiniCmd'.set P_1 name e`.
4. **Handle a projected *output* type** (the `LExpr T.mono` shape) so the parameter
   stays in scope inside it.

`LExpr` exercises only part 4; `Cmd` exercises parts 1–3. Build and test the fix
against both `SpecimenTest/StrataExperiments/StructParamExp.lean` /
`StructParamPathsExp.lean` (the output-type shape) and `StructParamCmdShapeExp.lean`
(the argument-position + mixed-fields shape), so "bucket 0 done" means both derive.

The cheaper alternative, recommended as the first step for `Cmd`, is to **specialize
`P` to a concrete `PureExpr`**: then `Cmd P` reduces to a closed type with no
structure parameter and bucket 0 does not arise at all.

---

## Cross-cutting notes

- **Specialize `P` first, always.** Because `Cmd`'s value space *is* the projected
  fields of `P`, none of the above is testable until `P` is a concrete `PureExpr`.
  The natural choice is the Lambda instantiation, so `P.Expr = LExpr …`,
  `P.Ty = LMonoTy`, `P.Ident = Identifier` — which also makes `ExprWT` literally
  `HasType`, unifying this analysis with the prior one. This both unblocks
  generation (bucket 0 workaround) *and* fixes which expression generator the
  command generator delegates to (finding D).
- **The function checker is a soundness oracle for the relation.** As a soundness
  gate (see `Delegated-producer-synthesis.md`), `Cmd.typeCheck … = .ok …` is a
  ready-made decidable `DecOpt` guard to wrap around any inductive-relation-derived
  producer: generate via the relation, double-check with the function. This is a
  free runtime safety net (the function and the relation should agree), and it
  costs nothing in the common case.
- **`init`/`set` are positive/negative duals of one container producer.** Worth
  flagging for the bucket-1 implementer: the env-lookup producer wants *both*
  modes — "a key present with its value" (`set`, like `tvar`) and "a key absent"
  (`init`, like freshness). Building one container oracle that serves both is the
  efficient design.
- **No coercion/subsumption rules.** Unlike `HasType` (`tinst`/`tgen`/`talias`),
  command typing is fully syntax-directed — there are no non-structural rules, so
  bucket 2's *coercion-rule control* is **not** needed here. The only bucket-2
  concern is the `det`/`nondet` (and assert/assume/cover) branch weighting.
- **`Stmt` is the next layer up.** `Strata/DL/Imperative/Stmt.lean` defines
  `Stmt P Cmd` (blocks, `ite`, `loop` with invariants/measures, `exit`,
  `funcDecl`, `typeDecl`) — control flow built on `Cmd`. It is *also* checked by a
  function (no inductive relation), embeds `Cmd`, and adds scoping (`block`/`exit`
  label discipline, loop invariants typed as `bool`). When that layer is in scope,
  expect: the same state-threading (C) but now *branching* (an `ite` must thread
  the env through *both* branches and join — a new wrinkle beyond the linear fold),
  the same delegation to expression typing for guards/invariants (D), and a new
  scoping/freshness concern for `block` labels and `exit` targets (bucket 1
  freshness again). Out of scope for this document, but the buckets already cover
  most of it.

---

## Summary table

| `Cmd` constructor | Synthesis mode | Env/type-directed mode | New capability beyond `HasType` doc |
|---|---|---|---|
| `init` (det) | neg-lookup (fresh key) + freshness + delegate expr + compute env | + drive expr at declared `ty` | none (buckets 0,1,D) |
| `init` (nondet) | neg-lookup + compute env | + invert output env for `x` | none (cheap branch — bucket 2) |
| `set` (det) | pos-lookup (`tvar` producer) + delegate expr + compute env | + drive expr at looked-up `ty` | none (buckets 1,D) |
| `set` (nondet) | pos-lookup; env unchanged | as synthesis | none (cheap branch) |
| `assert`/`assume`/`cover` | delegate expr + `isBoolType` check | drive expr at `bool` (better) | none (D; in-command type-direction) |
| `Cmds` (sequence) | left-to-right env-threading fold | invert last step to hit `τ_out` | **C** — state-transformer relation shape |

---

## Relationship to the existing docs & backlog

- **Bucket 0** (structure-parameter handling in the constrained deriver) is
  *mandatory* for `Cmd`, since `P.Ident/Ty/Expr` span the whole value space, and
  must cover the four parts in *What bucket 0 must do to cover `Cmd`* above:
  structure-parameter instance binders, selective non-Type-tolerant field
  expansion, implicit parameter threading, and the projected-output-type case.
  The cheap alternative is to specialize `P` to a concrete `PureExpr`, which
  sidesteps bucket 0 entirely for `Cmd`.
- **Bucket 1** (`Delegated-producer-synthesis.md`) is reused wholesale: the env is
  another container, so its positive (`set`) and negative (`init`) lookup producers
  are the `tvar`/freshness prototypes already on that doc's roadmap. No new
  producer *kind* is needed.
- **Bucket 2** is needed only for `det`/`nondet` branch weighting; coercion-rule
  control is *not* needed (command typing is syntax-directed).
- **New to the imperative layer:**
  1. **State-transformer relation shape (C).** Specimen should be comfortable
     deriving a producer for a relation with an *input* and *output* state where
     the cons rule threads them (output of head = input of tail). Synthesis mode is
     a fold and looks in reach; the env-directed mode is the harder analog of
     type-directed `HasType`. This is the one item warranting a dedicated
     experiment (a `StateThreadExp.lean` mirroring the existing
     `SpecimenTest/StrataExperiments/` style: a tiny relation
     `R : Env → List Item → Env → Prop` with a binding-introducing head rule).
  2. **Cross-relation delegation (D).** Confirm Specimen can schedule a hypothesis
     that is itself a *different* derived relation's producer (`ExprWT`/`HasType`),
     not just a self-recursive call. `autoDeriveDeps` (the self-derivation source in
     `Delegated-producer-synthesis.md`) is the relevant mechanism; the new bit is
     that the dependency is a separate relation over the same specialized `P`.
- **Function-vs-relation gap.** The most consequential upstream observation:
  generating high-quality `Cmd`s wants an **inductive `CmdWT`/`CmdsWT` relation**
  that does not exist in Strata yet (only `Cmd.typeCheck` does). The relation
  sketched in Part B is the artifact to request from / contribute to Strata; once
  it exists, this analysis shows the Specimen-side work is almost entirely
  already-motivated buckets 0–2 plus the two scheduling concerns C and D.
