import Specimen.Interp.Env

/-!
# Scheduling at runtime: reordering premises, not steps

`Specimen.Interp.Gen` runs a finished `Schedules.Schedule` as data. That is enough to *replay* what
`derive_mutual` chose, but not enough to try a different plan, because a `Schedule` has already
committed to the answers that the ordering determines:

```lean
-- BST.BstNode, derived for `fun lo hi => ∃ t, BST lo hi t`
[x] ← Between a₁ x b₁        -- SuchThat, Between[1]
[l] ← aux_bst a₁ x           -- SuchThat, Rec — because BST[2] *is* the mode being derived
[r] ← aux_bst x b₁
```

Permuting those three steps is almost meaningless: the data dependencies pin `x` first, so the only
other ordering swaps `l` and `r`. The interesting alternatives are the ones that change *which
variables each premise produces*. Put `BST lo x l` first and `x` is no longer bound when that premise
runs, so the premise has to produce **both** `x` and `l` — it is now a call to `BST[1,2]`, a
different generator, not a recursive call to the one being derived. `Between lo x hi` in turn has
nothing left to produce and becomes a `Check`. Nothing about that is a permutation of the original
steps; every step is different.

So this module works one level up, on what the compile-time pipeline calls a **preschedule**: the
constructor's premises as an unordered multiset, plus a plan saying what to do in what order. From a
`CtorSpec` (a constructor as data) and a `Plan`, `reschedule` recomputes, from scratch:

* which of a premise's arguments are *outputs* — the ones still holding an unbound variable —
  and hence the callee's `SpecKey.outputIndices` (`computeOutputIndicesForRewrite`);
* whether the premise is a `SuchThat` at all, or has become a `Check` because everything in it is
  already bound;
* whether the call is `Source.Rec` (its output positions coincide with the mode being derived),
  `Source.MutRec` (they coincide with a declared sibling), or `Source.NonRec` (some other spec);
* the extra `Match` steps needed when an output sits underneath a constructor
  (`Between lo (Nat.succ y) hi` cannot ask for `y`; it asks for the whole argument and destructures
  it afterwards);
* the prologue of `Match`es and equality `Check`s that unifying the conclusion against the mode's
  inputs produces, and the output expressions the schedule returns.

It also *rejects* plans, which matters as much as accepting them: a plan that would need a premise to
produce a variable trapped under a function application, or one that mixes a bound and an unbound
variable under the same constructor, is not a worse schedule — it is not a schedule at all. Those are
exactly the conditions `outputsNotConstrainedByFunctionApplication` and
`outputInputNotUnderSameConstructor` test at compile time.

## What this buys you

`RelSpec.deriveMode` turns a relation-as-data plus a `SpecKey` into a `RelSchedule` the interpreter
can run — so a mode nobody derived at compile time (`BST[1,2]`, say) becomes available at runtime,
which is what makes a real reordering runnable rather than merely printable. `plansOf` enumerates
candidate plans, and `Specimen.Interp.Runner` samples them.

## Fidelity, and where it stops

The compile-time pipeline reaches these decisions through `MetaM`: unification over `Expr`s
(`UnificationMonad`), `Range.Fixed` propagation, instance synthesis. This module reaches them by
structural computation over `ConstructorExpr`s. They agree wherever the conclusion is *linearized and
flattened* — no function application in it, no variable in it twice — which is the state
`linearizeAndFlatten` establishes before scheduling begins. Here the two halves live in two places:
`CtorSpec.linearize` flattens function applications when a spec is extracted, and `schedulePrologue`
renames repeated variables apart (`linearizePattern`) — there, because which occurrences are repeats
depends on the mode: an output position is not matched, so a variable it shares is not repeated.

Three compile-time behaviours are deliberately not reproduced:

* **Delegated equality premises** (`ScheduleEnv.delegableMap`): the pipeline probes for an
  `ArbitrarySizedSuchThat` instance to decide whether a variable under a function application can be
  produced after all, and only for premises that are equalities. Instance synthesis is not available
  here, so such a variable is treated as unproducible unless `CtorSpec.delegable` names it — which
  this module honours on any function application, not only an equality.
* **Single-output mode.** The pipeline produces at most one output per premise unless
  `specimen.multiOutput` is set, and at most one per *argument* in any case. `reschedule` always lets
  a premise produce every variable that is still unbound in it, because that is precisely what a
  reordering needs: `BST lo x l` scheduled first has to yield both `x` and `l` or the ordering is
  unusable.
* **Scoring.** Nothing here ranks plans by a static quality score the way `Scoring.lean` does. The
  point of the exercise is to run them and measure — see `InterpEnv.estimateRisk` for the one
  static estimate that is cheap enough to rank with, and `Specimen.Interp.Runner` for the measurements.
-/

open Lean Plausible Schedules

namespace Specimen.Interp

/-! ## A constructor as data -/

/-- One of a constructor's universally-quantified binders.

    `ty` is the binder's type reified as a `HypothesisExpr` — the same form an `Unconstrained` step
    carries, so `InterpEnv.lookupArbitrary` can find a generator for it when the variable is
    produced unconstrained. -/
structure VarSpec where
  /-- The binder's name, as it appears in the premises and the conclusion. -/
  name : Name
  /-- The binder's type, reified: `(``Nat, [])`, `(``List, [.TyCtor ``Nat []])`, … -/
  ty : HypothesisExpr := (`_unknownType, [])
  /-- Whether the binder is `Sort`-typed (a type variable). Type variables carry no runtime value:
      they are never generated and never counted as unbound. -/
  isSort : Bool := false
  deriving Repr, Inhabited, BEq

/-- One constructor of a relation, before a mode or an ordering has been chosen — the runtime
    counterpart of the `(vars, hypotheses, conclusion)` triple the compile-time scheduler searches
    over.

    Conventions, all matching the compile-time reification (`exprToConstructorExpr`):
    * `conclusionArgs` holds *every* argument position of the conclusion, in order, including
      implicit and instance-implicit ones (which appear as `.TyCtor`/`.CSort`/`.Hole`). Positions
      line up with `SpecKey.outputIndices` and with `RelSpec.argNames`.
    * `hypotheses` likewise keeps every argument position of each premise. -/
structure CtorSpec where
  /-- The constructor's name. -/
  ctorName : Name
  /-- The constructor's binders. Order is irrelevant; lookups are by name. -/
  vars : List VarSpec := []
  /-- The constructor's premises, in declaration order. A plan is an ordering *of these*. -/
  hypotheses : List HypothesisExpr := []
  /-- The conclusion's arguments, positionally. -/
  conclusionArgs : List ConstructorExpr := []
  /-- Variables that may be produced from a premise even though they sit under a function
      application, because a constrained producer for that premise is registered as a leaf. The
      runtime counterpart of `ScheduleEnv.delegableMap`, which the pipeline fills in by instance
      synthesis. -/
  delegable : List Name := []
  deriving Repr, Inhabited, BEq

/-- A relation as data: everything needed to schedule any of its constructors at any mode. -/
structure RelSpec where
  /-- The inductive relation's name. -/
  inductiveName : Name
  /-- Names for the relation's arguments, positionally — the names a schedule's steps refer to its
      inputs and outputs by. One per conclusion argument position. -/
  argNames : List Name
  /-- Positions in `argNames` that are type or instance arguments and so carry no runtime value. -/
  typeArgIndices : List Nat := []
  /-- The relation's constructors. -/
  ctors : List CtorSpec := []
  /-- The name `Source.Rec` steps use for this relation's own recursive calls. -/
  recFnName : Name := `aux_arb
  /-- Sibling specs in a mutual block: `(inductive, outputIndices, auxFnName)`. A premise whose
      relation and output positions match a sibling becomes a `Source.MutRec` call, exactly as
      `Schedules.rewriteMutualCalls` does at compile time. -/
  mutualSiblings : List (Name × List Nat × Name) := []
  deriving Repr, Inhabited, BEq

namespace CtorSpec

/-- The binder named `v`, if the constructor has one. -/
def varSpec? (c : CtorSpec) (v : Name) : Option VarSpec :=
  c.vars.find? (fun s => s.name == v)

/-- Whether `v` is a `Sort`-typed binder, and so carries no runtime value. -/
def isSortVar (c : CtorSpec) (v : Name) : Bool :=
  (c.varSpec? v).any VarSpec.isSort

end CtorSpec

/-! ## Plans -/

-- `PlanStep` and `Plan` live in `Interp.Env`, beside `RelSchedule`, which records per constructor the
-- plan it was lowered from (`CtorProvenance`).

/-- Renders a plan against a constructor, for reports: `use 0` prints as the premise it schedules. -/
def ppPlan (c : CtorSpec) (plan : Plan) : String :=
  let one : PlanStep → String
    | .use i => (c.hypotheses[i]?).elim s!"<no premise {i}>" ppHypothesisExpr
    | .inst v => s!"{v} ← arbitrary"
  "; ".intercalate (plan.map one)

/-! ## Why a plan can fail

    Rejection is a first-class result. A plan is not a worse schedule when the interpreter cannot
    lower it — it is not a schedule, and the reason is the interesting part. -/

/-- Why a plan cannot be lowered to a schedule. -/
inductive PlanError where
  /-- A premise would have to produce a variable trapped under a function application or a type
      constructor, which no producer can invert. The compile-time counterpart is
      `outputsNotConstrainedByFunctionApplication` returning `false`. -/
  | outputUnderFunction (hyp : String) (vars : List Name)
  /-- A premise argument mixes bound and unbound variables under one constructor, so the argument is
      neither an input (it holds an unbound variable) nor an output (producing it would overwrite a
      value already fixed). The counterpart of `outputInputNotUnderSameConstructor`.

      `vars` are the *unbound* ones, which is what generating them unconstrained would fix. -/
  | outputInputUnderSameCtor (hyp : String) (arg : String) (vars : List Name)
  /-- A premise argument is a constructor application that cannot be read as a pattern, so its
      outputs cannot be recovered by destructuring. -/
  | notAPattern (hyp : String) (arg : String)
  /-- A premise would produce one variable from two places — `P x x`, `P (x, x)` — which a producer
      cannot do: it returns one value per position, so binding both would keep only the last and lose
      the equality the premise states. The counterpart is `constructHypothesis`'s `repeatedNames`, which
      forces such a variable to be bound first. `vars` are the repeated, still-unbound variables. -/
  | repeatedOutput (hyp : String) (vars : List Name)
  /-- The plan generates or produces a variable that is already bound. -/
  | alreadyBound (v : Name) (where_ : String)
  /-- The plan refers to a premise index the constructor does not have. -/
  | noSuchPremise (hypIdx : Nat)
  /-- The plan leaves premises unscheduled. -/
  | premisesUnused (hyps : List String)
  /-- After every plan step, some variable the conclusion needs is still unbound. -/
  | outputsUnbound (vars : List Name)
  /-- The plan generates a variable the constructor does not declare, or declares without a type. -/
  | unknownVar (v : Name)
  /-- The `CtorSpec` is malformed: the conclusion has more or fewer arguments than the relation. -/
  | arityMismatch (given expected : Nat)
  /-- The conclusion is not linearized: an input position holds a function application, so its
      variables can be neither matched nor solved for. -/
  | conclusionNotLinearized (arg : String)
  deriving Repr

/-- A one-line explanation, phrased as what to change. -/
def PlanError.message : PlanError → String
  | outputUnderFunction hyp vars =>
    s!"`{hyp}` would have to produce {vars} from under a function application, which cannot be \
      inverted. Generate {vars} earlier with `PlanStep.inst`, schedule a premise that produces \
      them first, or mark them `CtorSpec.delegable` if a producer for this premise is registered."
  | outputInputUnderSameCtor hyp arg vars =>
    s!"in `{hyp}`, the argument `{arg}` holds the unbound {vars} alongside an already-bound \
      variable, so it is neither an input nor a producible output. Generate {vars} with \
      `PlanStep.inst`, or schedule a premise that produces them first."
  | notAPattern hyp arg =>
    s!"in `{hyp}`, the produced argument `{arg}` cannot be read as a pattern, so its outputs \
      cannot be recovered by destructuring."
  | repeatedOutput hyp vars =>
    s!"`{hyp}` mentions the unbound {vars} in more than one place, so producing them would keep only \
      one value per variable and drop the equality the premise states. Generate {vars} earlier with \
      `PlanStep.inst`, or schedule a premise that produces them first."
  | alreadyBound v w => s!"'{v}' is already bound when {w}."
  | noSuchPremise i => s!"the plan schedules premise #{i}, which does not exist."
  | premisesUnused hyps =>
    s!"the plan leaves {hyps.length} premise(s) unscheduled: {hyps}. Every premise is a proof \
      obligation, so every premise must appear in the plan."
  | outputsUnbound vars =>
    s!"the conclusion still needs {vars} after every plan step. Add `PlanStep.inst` steps for \
      them, or schedule a premise that produces them."
  | unknownVar v =>
    s!"'{v}' is not a declared binder of this constructor (add it to `CtorSpec.vars`, with its \
      type, so an unconstrained generator can be found for it)."
  | arityMismatch given expected =>
    s!"the conclusion has {given} argument(s) but the relation takes {expected}."
  | conclusionNotLinearized arg =>
    s!"the conclusion's input argument `{arg}` is a function application. Flatten it into a fresh \
      variable plus an equality premise first (the compile-time pipeline's `linearizeAndFlatten`)."

instance : ToString PlanError := ⟨PlanError.message⟩

/-! ## Substitution and fresh names -/

/-- Renames the variables of a `ConstructorExpr` according to an association list, leaving names it
    does not mention alone. -/
partial def substExpr (σ : List (Name × Name)) : ConstructorExpr → ConstructorExpr
  | .Unknown u => .Unknown ((σ.find? (fun p => p.1 == u)).elim u Prod.snd)
  | .Ctor c args => .Ctor c (args.map (substExpr σ))
  | .TyCtor c args => .TyCtor c (args.map (substExpr σ))
  | .FuncApp f args => .FuncApp f (args.map (substExpr σ))
  | e => e

/-- `substExpr` on a premise. -/
def substHyp (σ : List (Name × Name)) (hyp : HypothesisExpr) : HypothesisExpr :=
  (hyp.1, hyp.2.map (substExpr σ))

/-- Replaces occurrences of `Sort`-typed variables with `.Hole`.

    A polymorphic relation's type parameter reifies as an ordinary `.Unknown α` — an fvar, not a
    `.TyCtor` — so `valueArgs` cannot tell it from a value and every downstream count includes it. That
    is how `SetContains {α} : α → Set α → Prop` ended up passing two value arguments to a self-call
    that takes one.

    `.Hole` is the right replacement rather than a special case: `isTypeLevel` already drops it, and it
    is documented as standing for exactly this — an implicit argument that carries no value and is
    always inferable from the explicit ones. -/
partial def holeSortVars (isSortVar : Name → Bool) : ConstructorExpr → ConstructorExpr
  | .Unknown u => if isSortVar u then .Hole else .Unknown u
  | .Ctor c args => .Ctor c (args.map (holeSortVars isSortVar))
  | .TyCtor c args => .TyCtor c (args.map (holeSortVars isSortVar))
  | .FuncApp f args => .FuncApp f (args.map (holeSortVars isSortVar))
  | e => e

/-- `holeSortVars` on a premise. -/
def holeSortVarsHyp (isSortVar : Name → Bool) (hyp : HypothesisExpr) : HypothesisExpr :=
  (hyp.1, hyp.2.map (holeSortVars isSortVar))

/-- Renames the variables a pattern binds, **by name**: every occurrence of a variable gets the same new
    name. So it cannot make a non-linear pattern linear — `linearizePattern` does that. -/
partial def substPattern (σ : List (Name × Name)) : Pattern → Pattern
  | .UnknownPattern u => .UnknownPattern ((σ.find? (fun p => p.1 == u)).elim u Prod.snd)
  | .CtorPattern c ps => .CtorPattern c (ps.map (substPattern σ))
  | p => p

/-- A name not in `used`, obtained by appending primes. Mirrors `LocalContext.getUnusedName`'s job
    without a local context to consult. -/
partial def freshen (used : List Name) (base : Name) : Name :=
  if used.contains base then freshen used (base.appendAfter "'") else base

/-- The name `handleConstrainedOutputs` gives the fresh variable standing in for a constructor
    application whose arguments are all outputs: `vt1_t2` for `TFun t1 t2`. Spelled to match the
    compile-time rule exactly (`"v" ++ String.intercalate "_" …`, with no separator after the `v`), so
    a runtime-derived schedule is comparable to a derived one name for name. -/
def constrainedOutputName (used : List Name) (vars : List Name) : Name :=
  freshen used (Name.mkSimple ("v" ++ "_".intercalate (vars.map (fun v => v.getString!))))

/-! ## The prologue: unifying the conclusion against the mode -/

/-- What unifying a constructor's conclusion against a mode's argument names yields: the steps that
    must run before any premise, the renaming it induces, the variables it binds, and the
    expressions the schedule returns.

    The compile-time counterpart is the `UnifyState` left behind by
    `DeriveConstrainedProducer.deriveSchedule`, lowered by
    `Schedules.addConclusionPatternsAndEqualitiesToSchedule`. -/
structure Prologue where
  /-- `Match` steps for input positions that are not bare variables, then one `Eq` check per repeated
      variable occurrence — every `Match` before any check, the order
      `Schedules.addConclusionPatternsAndEqualitiesToSchedule` gives derived code. These always come
      first: every later step may read what they bind. -/
  steps : List ScheduleStep
  /-- Constructor binder ↦ relation argument name, for binders the conclusion aliases directly. -/
  subst : List (Name × Name)
  /-- Variables bound once the prologue has run: the mode's inputs and everything its patterns
      destructure. `Sort`-typed binders are included — they carry no value, so nothing generates
      them. -/
  bound : List Name
  /-- What the schedule returns: the conclusion's value-level output arguments, renamed. -/
  outputs : List ConstructorExpr
  deriving Repr

/-- `Schedules.patternOfConstructorExpr`, dropping every constructor application's **type-level**
    arguments.

    A `Val` records value-level arguments only — `toVal` on a pair emits `Prod.mk [a, b]`, not
    `Prod.mk [α, β, a, b]` — and `matchPattern` insists the arities agree exactly. So a pattern that
    keeps its type arguments can never match anything.

    Cedar's `LubRecord.cons` is where this bites: its conclusion is `(k, v₁) :: r₁`, and `Prod.mk`'s two
    type arguments survive reification as `TyCtor`s. The pattern then had four sub-patterns against the
    `Val`'s two, so **every** attempt was rejected — a relation that looked derivable, validated clean,
    and produced nothing at any size. Dropping them here is the rule `Value.valueArgs` already applies
    everywhere else in the untyped layer; `Hole` goes the same way, being type-level by `isTypeLevel`. -/
partial def valuePatternOfConstructorExpr : ConstructorExpr → Option Pattern
  | .Unknown u => some (.UnknownPattern u)
  | .Lit l => some (.LitPattern l)
  | .Ctor c args | .TyCtor c args =>
    (.CtorPattern c) <$> (valueArgs args).mapM valuePatternOfConstructorExpr
  | .FuncApp .. | .CSort _ | .Hole => none

/-- What `linearizePattern` threads through its walk of one pattern. -/
structure LinearizeState where
  /-- Variables bound so far: everything bound before this pattern, plus the occurrences walked. -/
  bound : List Name
  /-- Names a fresh variable must avoid. -/
  used : List Name
  /-- First occurrences, as `(binder, name it is bound under)` — what `schedulePrologue` records in
      `patBound`, so a later bare occurrence of the binder is checked against it. -/
  firstBinds : List (Name × Name) := []
  /-- One `Eq` check per renamed occurrence: `(name the variable is already known by) = (fresh
      name)`. -/
  eqs : List ScheduleStep := []
  deriving Inhabited

/-- Renames a pattern apart **occurrence by occurrence**, in the preorder `matchPattern` walks it, so
    that no variable occurs in it twice and none it binds is already bound.

    The first occurrence of a variable nothing has bound yet keeps its name and binds it. Every later
    occurrence — of a variable an earlier input position bound, one `subst` aliases to an argument, or
    one met earlier in *this* pattern — becomes a fresh `v_dup` plus an `Eq` check against the name the
    variable is already known by. The deriver's `linearizeAndFlatten` makes the same cut from the other
    end (`p_1` for every occurrence but the last, then `p_1 = p`); with the equality in place the two
    schedules accept the same inputs and return the same values.

    By occurrence, not by name, is the point. The version this replaces collected the pattern's
    variables and renamed them with `substPattern`, which maps a *name* to a name, so it could not give
    the two `p`s of Cedar's `binaryAppEqLitSame` — `.binaryApp .eq (.lit p) (.lit p)` — different
    names; and it tested only what was bound *before* the pattern, so the second `p` was not seen as a
    repeat at all. The pattern stayed non-linear, `matchPattern` let the second binding overwrite the
    first, and `.binaryApp .eq (.lit 1) (.lit 2)` was accepted as `.bool .tt` in seven `HasType`
    generator modes.

    Left alone: the wildcard `_`, which binds nothing, and `Sort`-typed binders. Those start out bound —
    nothing generates a type — so renaming a second occurrence would emit `α = α_dup` and then match
    against the fresh `α_dup`, which nothing ever binds; a polymorphic relation like
    `SetContains {α} : α → Set α → …` mentions its type variable in several positions, so that fired
    constantly. -/
partial def linearizePattern (isSortVar : Name → Bool) (subst : List (Name × Name)) :
    Pattern → LinearizeState → Pattern × LinearizeState
  | .UnknownPattern v, st =>
    if v == `_ || isSortVar v then (.UnknownPattern v, st)
    else
      let known := (subst.find? (fun q => q.1 == v)).elim v Prod.snd
      if st.bound.contains known then
        let fresh := freshen st.used (v.appendAfter "_dup")
        (.UnknownPattern fresh,
          { st with bound := st.bound ++ [fresh], used := st.used ++ [fresh],
                    eqs := st.eqs ++ [.Check (.NonRec (``Eq, [.Unknown known, .Unknown fresh])) true] })
      else
        (.UnknownPattern known,
          { st with bound := st.bound ++ [known], used := st.used ++ [known],
                    firstBinds := st.firstBinds ++ [(v, known)] })
  | .CtorPattern c ps, st =>
    let (ps', st') := ps.foldl (fun (acc, s) p =>
      let (p', s') := linearizePattern isSortVar subst p s
      (acc ++ [p'], s')) (([] : List Pattern), st)
    (.CtorPattern c ps', st')
  | p, st => (p, st)

/-- Unifies a constructor's conclusion against a mode.

    For each **input** position, in order: a bare variable is *aliased* to the relation's argument
    name (which is why derived schedules talk about `a_2` where the constructor said `n`); anything
    else becomes a `Match` on that argument name, binding the variables in its pattern. A variable
    reached twice — in two positions, or twice inside one (`linearizePattern`) — yields a fresh name and
    an `Eq` check rather than a non-linear pattern, matching `UnifyState.equalities` and
    `linearizeAndFlatten`'s equalities. The checks follow every `Match`, as they do in derived code.

    Each **output** position contributes its (renamed) expression to what the schedule returns.
    Type and instance positions contribute nothing either way. -/
def schedulePrologue (rel : RelSpec) (key : SpecKey) (c : CtorSpec) : Except PlanError Prologue := do
  let n := rel.argNames.length
  if c.conclusionArgs.length != n then
    throw (.arityMismatch c.conclusionArgs.length n)
  let mut steps : List ScheduleStep := []
  -- Every equality the unification yields, emitted after the last `Match` rather than beside the one
  -- that needed it. Derived code has this order (`addConclusionPatternsAndEqualitiesToSchedule`:
  -- matches, then equalities), and it keeps the input `Match`es one contiguous run, which is all
  -- `RelSchedule.guardPassesWith` reads: it stops at the first step that is not a `Match`.
  -- Interleaved, the check for `binaryAppEqLitSame`'s repeated `p` would hide the `.bool .tt` match on
  -- its type from the dispatch guard. Moving a check later is safe: it reads only inputs and pattern
  -- variables, and every `Match` binds fresh names, so nothing it reads changes in between.
  let mut eqs : List ScheduleStep := []
  let mut subst : List (Name × Name) := []
  let mut bound : List Name := c.vars.filter VarSpec.isSort |>.map VarSpec.name
  -- Variables an earlier input *pattern* bound, and the name they are bound under. Tracked separately
  -- from `subst` (which records aliases for bare-variable positions) because both are ways a variable
  -- can already be known by the time a later input position mentions it, and conflating a *pattern*
  -- binding with an alias silently loses a constraint. See the `.Unknown` case below.
  let mut patBound : List (Name × Name) := []
  -- Names a fresh `_dup` must avoid: every binder and every argument name, not only what is bound so
  -- far. A binder the walk has not reached yet counts — in `(n, n, n_dup)` the second `n` must not
  -- become `n_dup`, which the third position binds, or the third component gets equated with the
  -- second.
  -- Every name the constructor mentions, not only its declared binders, so freshening cannot depend on
  -- `vars` being complete.
  let mut used : List Name := rel.argNames ++ c.vars.map VarSpec.name
    ++ c.conclusionArgs.flatMap varsInConstructorExpr
    ++ c.hypotheses.flatMap (fun h => h.2.flatMap varsInConstructorExpr)
  -- Input positions first, so that aliases exist before outputs are read off.
  for i in List.range n do
    if rel.typeArgIndices.contains i || key.outputIndices.contains i then
      continue
    let some argName := rel.argNames[i]? | continue
    let some arg := c.conclusionArgs[i]? | continue
    match arg with
    | .Unknown v =>
      -- Already known, either as an alias or from an earlier pattern: assert the two agree.
      --
      -- The `patBound` half is load-bearing and was missing. `lookup (τ :: Γ) .zero τ` at mode `[1]`
      -- has `τ` in *two* input positions: bound by the pattern for position 0, then named bare at
      -- position 2. Without this it fell to the `none` branch and *aliased* `τ` to the second argument
      -- name, conflating the head of the list with the requested type — so `lookup[1]` returned an
      -- index whose type need not match what was asked for, and STLC's `TVar` produced ill-typed terms.
      match (subst.find? (fun p => p.1 == v)).orElse (fun _ => patBound.find? (fun p => p.1 == v)) with
      | some (_, prior) =>
        eqs := eqs ++ [.Check (.NonRec (``Eq, [.Unknown prior, .Unknown argName])) true]
        bound := bound ++ [argName]
      | none =>
        subst := subst ++ [(v, argName)]
        bound := bound ++ [argName]
    | .TyCtor .. | .CSort _ | .Hole => pure ()
    | .FuncApp .. => throw (.conclusionNotLinearized (ppConstructorExpr arg))
    | _ =>
      let some pat := valuePatternOfConstructorExpr arg
        | throw (.notAPattern (ppHypothesisExpr (rel.inductiveName, c.conclusionArgs))
            (ppConstructorExpr arg))
      -- Every occurrence that is a repeat — of a variable an earlier position bound, or of one
      -- earlier in this same pattern — is renamed apart and its equality asserted instead, as
      -- `linearizeAndFlatten` does. By occurrence: see `linearizePattern` for the by-name version it
      -- replaces and the Cedar constructor that let through. Its checks read the fresh names, which
      -- only this `Match` binds, so they go to `eqs` and are emitted after every `Match`.
      let (pat', st) := linearizePattern c.isSortVar subst pat { bound := bound, used := used }
      steps := steps ++ [.Match .allowImplicit argName pat']
      eqs := eqs ++ st.eqs
      bound := st.bound
      used := st.used
      patBound := patBound ++ st.firstBinds
  let outputs := (List.range n).filterMap (fun i =>
    if key.outputIndices.contains i && !rel.typeArgIndices.contains i then
      (c.conclusionArgs[i]?).map (fun a => holeSortVars c.isSortVar (substExpr subst a))
    else none)
  return { steps := steps ++ eqs, subst, bound, outputs }

/-! ## Lowering one premise -/

/-- Whether a premise argument is *settled*: every variable it mentions is bound, so the argument
    can be evaluated and passed as an input. -/
private def argSettled (bound : List Name) (isSortVar : Name → Bool) (arg : ConstructorExpr) :
    Bool :=
  (varsInConstructorExpr arg).all (fun v => bound.contains v || isSortVar v)

/-- The result of lowering one premise: the steps it becomes, and the variables they bind. -/
private structure StepResult where
  steps : List ScheduleStep
  bound : List Name

/-- Peels `Not` wrappers off a premise, flipping the desired truth value each time — the polarity
    logic of `preScheduleStepToScheduleStep`'s `.Checks` case. -/
partial def peelNot (hyp : HypothesisExpr) (polarity : Bool := true) (depth : Nat := 10) :
    HypothesisExpr × Bool :=
  match depth with
  | 0 => (hyp, polarity)
  | depth' + 1 =>
    if hyp.1 == ``Not then
      match hyp.2 with
      | [.Ctor name args] | [.TyCtor name args] | [.FuncApp name args] =>
        peelNot (name, args) (!polarity) depth'
      | _ => (hyp, polarity)
    else (hyp, polarity)

/-- Lowers one premise under the current bindings.

    This is where a reordering is actually *reinterpreted*. The premise's output positions are
    recomputed from what is bound (`Schedules.computeOutputIndicesForRewrite`'s rule: a position is
    an output when it holds an unbound variable), which determines whether the premise is a check or
    a producer, which spec it calls, and at which mode. -/
private def lowerPremise (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (prodSort : ProducerSort)
    (bound : List Name) (used : List Name) (hyp : HypothesisExpr) : Except PlanError StepResult := do
  let isSortVar := c.isSortVar
  let (relName, args) := hyp
  -- Classify every argument position: settled (an input) or holding unbound variables (an output).
  if args.all (argSettled bound isSortVar) then
    let (inner, polarity) := peelNot hyp
    let src :=
      if inner.1 == rel.inductiveName && key.deriveSort == .Checker && key.outputIndices.isEmpty then
        Source.Rec rel.recFnName inner.2
      else Source.NonRec inner
    return { steps := [.Check src polarity], bound := bound }
  -- A variable mentioned more than once across the unsettled positions cannot be produced: the
  -- producer returns one value per position, and binding the variable from each in turn would keep only
  -- the last — `bindVars` overwrites — silently dropping the equality `P x x` states. The deriver makes
  -- such a variable must-bind (`constructHypothesis`'s `repeatedNames`), so it is generated first and the
  -- premise becomes a check; raising a repairable error gets `repair` to do exactly that. Delegable
  -- function-call arguments are exempt, as they are there.
  let occurrences := (args.filter (fun a => !argSettled bound isSortVar a)).flatMap (fun a =>
    match a with
    | .FuncApp .. | .TyCtor .. =>
      if (varsInConstructorExpr a).any c.delegable.contains then [] else varsInConstructorExpr a
    | _ => varsInConstructorExpr a)
    |>.filter (fun v => !isSortVar v && !bound.contains v)
  let repeated := occurrences.filter (fun v => (occurrences.filter (· == v)).length > 1) |>.eraseDups
  unless repeated.isEmpty do
    throw (.repeatedOutput (ppHypothesisExpr hyp) repeated)
  -- Rewrite the unsettled positions into bare output variables, collecting the destructuring
  -- matches that recovering them needs. Mirrors `handleConstrainedOutputs`.
  let mut args' : List ConstructorExpr := []
  let mut outVars : List Name := []
  let mut destructures : List ScheduleStep := []
  let mut newBound : List Name := bound
  let mut usedNames := used
  for arg in args do
    if argSettled bound isSortVar arg then
      args' := args' ++ [arg]
      continue
    let vars := (varsInConstructorExpr arg).filter (fun v => !isSortVar v)
    match arg with
    | .Unknown v =>
      args' := args' ++ [arg]
      outVars := outVars ++ [v]
      newBound := newBound ++ [v]
      usedNames := usedNames ++ [v]
    | .Ctor .. =>
      -- Every variable underneath must be unbound: producing the argument overwrites all of them.
      if vars.any (fun v => bound.contains v) then
        throw (.outputInputUnderSameCtor (ppHypothesisExpr hyp) (ppConstructorExpr arg)
          (vars.filter (fun v => !bound.contains v)))
      let some pat := valuePatternOfConstructorExpr arg
        | throw (.notAPattern (ppHypothesisExpr hyp) (ppConstructorExpr arg))
      let fresh := constrainedOutputName usedNames vars
      usedNames := usedNames ++ [fresh] ++ vars
      args' := args' ++ [.Unknown fresh]
      outVars := outVars ++ [fresh]
      destructures := destructures ++ [.Match .allExplicit fresh pat]
      newBound := newBound ++ [fresh] ++ vars
    | .FuncApp .. | .TyCtor .. =>
      -- A function application cannot be inverted, so its variables cannot be produced — unless a
      -- producer for the whole premise is registered and they are marked delegable.
      let delegated := vars.filter (fun v => c.delegable.contains v)
      if delegated.length != vars.length then
        -- Only the unbound ones are actionable: a bound variable is already an input here, and
        -- `inst`ing it would be a contradiction.
        throw (.outputUnderFunction (ppHypothesisExpr hyp)
          (vars.filter (fun v => !c.delegable.contains v && !bound.contains v)))
      args' := args' ++ [arg]
      match delegated.head? with
      | some v =>
        outVars := outVars ++ [v]
        newBound := newBound ++ delegated
        usedNames := usedNames ++ delegated
      | none => pure ()
    | _ =>
      args' := args' ++ [arg]
  -- Raw output positions, exactly as `computeOutputIndicesForRewrite` computes them: any position
  -- mentioning an output variable. This is the callee's mode.
  let outIdxs := computeOutputIndicesForRewrite args' outVars
  let inputArgs := filterWithIndex (fun i _ => !outIdxs.contains i) args'
  -- Mode identity is a *set* of positions. `computeOutputIndicesForRewrite` returns them ascending
  -- and every compile-time construction of `SpecKey.outputIndices` scans ascending too, but
  -- `isRecCall` compares sorted on both sides rather than relying on that, and a hand-written
  -- `SpecKey` need not. Match its indifference.
  let sameMode := fun (idxs : List Nat) =>
    idxs.length == outIdxs.length && idxs.all outIdxs.contains
  let src : Source :=
    if relName == rel.inductiveName && sameMode key.outputIndices then
      .Rec rel.recFnName inputArgs
    else
      match rel.mutualSiblings.find? (fun (n, idxs, _) => n == relName && sameMode idxs) with
      | some (_, _, auxName) => .MutRec auxName inputArgs
      | none => .NonRec (relName, args')
  let outs := outVars.map (fun v => (v, none))
  return { steps := .SuchThat outs src prodSort :: destructures, bound := newBound }

/-! ## Lowering a plan -/

/-- A plan lowered to a schedule, with the provenance of each step. -/
structure Lowered where
  /-- The schedule the plan lowers to. -/
  schedule : Schedule
  /-- One entry per step of `schedule.1`, saying which plan step emitted it: `none` for the
      conclusion prologue, which belongs to the constructor rather than to any premise.

      This is what makes a discard *actionable*. The interpreter attributes a discard to a step
      index (`Specimen.Interp.rejectAt`); this maps that index back to the premise whose placement
      caused it, which is the thing a mutation can move. -/
  origins : List (Option PlanStep)

namespace Lowered

/-- The plan step that emitted schedule step `stepIdx`. -/
def originOf (l : Lowered) (stepIdx : Nat) : Option PlanStep :=
  (l.origins[stepIdx]?).bind id

/-- Attributes per-step discard counts to premises: `(premise index, discards)`, heaviest first.

    Steps from the prologue and from `inst` are dropped, since neither names a premise a swap could
    move. A premise's total includes the destructuring `Match`es its `SuchThat` emitted, because
    those fail for the same reason the premise was placed where it was. -/
def blame (l : Lowered) (perStep : List (Nat × Nat)) : List (Nat × Nat) :=
  let attributed := perStep.filterMap (fun (idx, n) =>
    match l.originOf idx with
    | some (.use i) => some (i, n)
    | _ => none)
  let totals := attributed.foldl (fun acc (i, n) =>
    match acc.find? (fun p => p.1 == i) with
    | some (_, m) => acc.map (fun p => if p.1 == i then (i, m + n) else p)
    | none => acc ++ [(i, n)]) []
  totals.foldl (fun acc p =>
    let rec ins : List (Nat × Nat) → List (Nat × Nat)
      | [] => [p]
      | q :: qs => if p.2 > q.2 then p :: q :: qs else q :: ins qs
    ins acc) []

end Lowered

/-- `reschedule`, also reporting which plan step emitted each schedule step. -/
def rescheduleLowered (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (plan : Plan) :
    Except PlanError Lowered := do
  let prodSort : ProducerSort :=
    match key.deriveSort with
    | .Checker | .Enumerator => .Enumerator
    | .Generator | .Theorem => .Generator
  let pro ← schedulePrologue rel key c
  let mut steps := pro.steps
  let mut origins : List (Option PlanStep) := pro.steps.map (fun _ => none)
  let mut bound := pro.bound
  let mut usedNames := pro.bound ++ c.vars.map VarSpec.name ++ rel.argNames
  let mut scheduled : List Nat := []
  -- Premises promoted to a check ahead of their position in the plan. Tracked apart from `scheduled`
  -- so reaching such a premise's own plan step is a no-op rather than the duplicate-use error.
  let mut hoisted : List Nat := []
  -- **Check hoisting, matching the compile-time deriver.** As soon as a premise's arguments are all
  -- settled it is a check, and the deriver emits it immediately rather than at its position in the
  -- order — `processModeChoices` promotes it out of the remaining list. Measured on `BST[2]` with the
  -- order `BST x hi r; BST lo x l; Between lo x hi` pinned, the deriver produced
  -- `[x,r] ← BST …; check Between …; [l] ← …` while this lowering produced
  -- `[x,r] ← BST …; [l] ← …; check Between …`. That is not cosmetic: a check placed earlier rejects
  -- before the third premise's work instead of after, so the two schedules discard differently — and a
  -- discard measurement taken here would not describe the schedule the pipeline emits.
  --
  -- Hoisting is also strictly the better placement, which is why the interpreter adopts the deriver's
  -- behaviour rather than the reverse. A single pass suffices per step: `lowerPremise` on a fully
  -- settled premise emits a `Check` and leaves `bound` unchanged, so emitting one can never settle
  -- another.
  -- `scheduled` is passed in rather than captured: Lean's `let mut` is not a mutable cell, so a
  -- closure over it sees its value at definition time — here `[]` — and would re-emit every premise
  -- that had already been scheduled as a spurious check.
  let hoistChecks : List ScheduleStep × List (Option PlanStep) × List Nat × List Name × List Nat →
      Except PlanError (List ScheduleStep × List (Option PlanStep) × List Nat) :=
    fun (steps0, origins0, hoisted0, bound0, scheduled0) => do
      let mut steps' := steps0
      let mut origins' := origins0
      let mut hoisted' := hoisted0
      for pstep' in plan do
        match pstep' with
        | .inst _ => pure ()
        | .use j =>
          if scheduled0.contains j || hoisted'.contains j then pure () else
          match c.hypotheses[j]? with
          | none => pure ()
          | some hyp =>
            let sub := holeSortVarsHyp c.isSortVar (substHyp pro.subst hyp)
            if sub.2.all (argSettled bound0 c.isSortVar) then
              let res ← lowerPremise rel key c prodSort bound0 usedNames sub
              steps' := steps' ++ res.steps
              origins' := origins' ++ res.steps.map (fun _ => some pstep')
              hoisted' := hoisted' ++ [j]
      return (steps', origins', hoisted')
  for pstep in plan do
    match pstep with
    | .inst v =>
      let v' := (pro.subst.find? (fun p => p.1 == v)).elim v Prod.snd
      if bound.contains v' then throw (.alreadyBound v' "it is generated unconstrained")
      let some spec := c.varSpec? v | throw (.unknownVar v)
      if spec.isSort then throw (.unknownVar v)
      steps := steps ++ [.Unconstrained v' (.NonRec (substHyp pro.subst spec.ty)) prodSort]
      origins := origins ++ [some pstep]
      bound := bound ++ [v']
      usedNames := usedNames ++ [v']
      let (s', o', h') ← hoistChecks (steps, origins, hoisted, bound, scheduled)
      steps := s'; origins := o'; hoisted := h'
    | .use i =>
      -- Already emitted as a hoisted check: its own plan step has nothing left to do.
      if hoisted.contains i then pure () else
      let some hyp := c.hypotheses[i]? | throw (.noSuchPremise i)
      if scheduled.contains i then throw (.noSuchPremise i)
      scheduled := scheduled ++ [i]
      let res ← lowerPremise rel key c prodSort bound usedNames
        (holeSortVarsHyp c.isSortVar (substHyp pro.subst hyp))
      steps := steps ++ res.steps
      origins := origins ++ res.steps.map (fun _ => some pstep)
      bound := res.bound
      usedNames := usedNames ++ res.bound
      let (s', o', h') ← hoistChecks (steps, origins, hoisted, bound, scheduled)
      steps := s'; origins := o'; hoisted := h'
  let missing := (List.range c.hypotheses.length).filter
    (fun i => !scheduled.contains i && !hoisted.contains i)
  if !missing.isEmpty then
    throw (.premisesUnused (missing.filterMap (fun i => (c.hypotheses[i]?).map ppHypothesisExpr)))
  let needed := pro.outputs.flatMap varsInConstructorExpr
    |>.filter (fun v => !bound.contains v && !c.isSortVar v)
  if !needed.isEmpty then
    throw (.outputsUnbound (needed.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []))
  -- A checker's conclusion is not a value: reaching the end of the steps *is* the verdict, which is
  -- what `ScheduleSort.CheckerSchedule` means and what `getScheduleSort` emits for `DeriveSort.Checker`.
  let sort : ScheduleSort :=
    if key.deriveSort == .Checker then .CheckerSchedule
    else .ProducerSchedule prodSort pro.outputs
  return { schedule := (steps, sort), origins := origins }

/-- Lowers a plan to a `Schedule`, recomputing every polarity decision from scratch.

    `Except`, not `Option`: a rejected plan carries the reason, and the reason is what tells you
    which other plan to try.

    Nothing here consults an `InterpEnv`. A schedule this returns is well-formed but may call a spec
    nothing is registered for — run `InterpEnv.check` to find out, which is the same check the
    hand-written path gets. -/
def reschedule (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (plan : Plan) :
    Except PlanError Schedule :=
  Lowered.schedule <$> rescheduleLowered rel key c plan

/-! ## Enumerating plans

    Two ways to get a plan. `repair` takes an ordering you care about and makes it work if it can;
    `plansOf` sweeps orderings for you. -/

/-- Every way of inserting `x` into `l`, one per position. -/
def insertions {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertions x ys).map (fun l => y :: l)

/-- Every permutation of a list. Exponential by nature — prefer `permutationsUpTo`, which never
    builds more than it is asked for. -/
def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap (insertions x)

/-- The first `k` permutations of `l`, in the order `permutations` yields them, **without building the
    rest**.

    This is not an optimisation, it is the difference between working and not. Cedar's `LubRecord` has
    14 premises, so `permutations` would build 87 billion lists; measured, the eager version already
    fails to finish at nine. The trick is that each inner permutation of the tail expands into
    `xs.length + 1` outer ones, so asking for `k` outer permutations needs only `⌈k / (|xs|+1)⌉` inner
    ones — the recursion shrinks the request as fast as it shrinks the list.

    The identity permutation comes first, as it does from `permutations`: `insertions x` puts `x` at the
    front of its first result, so the first permutation of `x :: xs` is `x` followed by the first
    permutation of `xs`. Callers rely on that to try a constructor's declared premise order first. -/
def permutationsUpTo {α : Type} (k : Nat) : List α → List (List α)
  | [] => if k == 0 then [] else [[]]
  | x :: xs =>
    if k == 0 then []
    else
      let perInner := xs.length + 1
      ((permutationsUpTo ((k + perInner - 1) / perInner) xs).flatMap (insertions x)).take k

/-! ### Inserting the unconstrained generations an ordering needs

    Three situations force a variable to be generated out of thin air rather than produced by a
    premise, and an ordering is unusable until each is answered:

1. **Nothing produces it.** The conclusion needs it and no premise mentions it — `BST[1,2]`'s
   `BstLeaf`, whose upper bound is an output that no premise constrains. Surfaces as
   `outputsUnbound`.
2. **A premise could only produce it from under a function application**, which cannot be inverted:
   `outputUnderFunction`. Generating it first turns that argument into an ordinary input.
3. **A premise argument mixes it with an already-bound variable** under one constructor —
   STLC's `typing Γ e₁ (.Fun τ₁ τ₂)` reached with `τ₂` bound and `τ₁` not. Producing the argument
   would overwrite `τ₂`; treating it as an input would read the unbound `τ₁`. Generating `τ₁` first
   settles the argument. Surfaces as `outputInputUnderSameCtor`.

    All three name the variables that would unblock them, so the repair is mechanical rather than a
    guess. **Where** the generation goes matters: it must precede the premise that needs it, but
    putting it any earlier can demote an *unrelated* premise from a producer to a check. So each
    `inst` lands immediately before the first premise mentioning the variable, and at the very end
    when no premise mentions it at all — which is where the compile-time scheduler puts its own
    trailing `InstVars`. -/

/-- Every variable a plan generates unconstrained. -/
def Plan.instVars (plan : Plan) : List Name :=
  plan.filterMap (fun s => match s with | .inst v => some v | _ => none)

/-- Inserts `PlanStep.inst v` immediately before the first premise that mentions `v`, or at the end
    if none does.

    Placement is exact rather than conservative. No premise scheduled *before* the blocking one can
    mention `v`: if one did, it would have produced `v` (an unbound variable in a premise is an
    output), so `v` would already be bound and nothing would have blocked. -/
def Plan.insertInst (c : CtorSpec) (plan : Plan) (v : Name) : Plan :=
  let mentions : PlanStep → Bool
    | .use i => ((c.hypotheses[i]?).elim [] (fun h => h.2.flatMap varsInConstructorExpr)).contains v
    | .inst _ => false
  match plan.findIdx? mentions with
  | some i => plan.insertIdx i (.inst v)
  | none => plan ++ [.inst v]

/-- Lowers a plan, inserting the unconstrained generations it needs, and retrying.

    Returns the repaired plan alongside the schedule, so a report can show what it took — the
    difference between the plan you asked for and the plan that works is itself informative.
    `budget` bounds the number of insertion rounds. -/
def repairLowered (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (plan : Plan) (budget : Nat := 8) :
    Except PlanError (Plan × Lowered) :=
  match rescheduleLowered rel key c plan, budget with
  | .ok low, _ => .ok (plan, low)
  | .error e, 0 => .error e
  | .error e, budget' + 1 =>
    -- Only the four "this variable needs binding" rejections are repairable, and only by binding
    -- the variable earlier. Everything else is a property of the constructor, not of the ordering.
    let blockers : List Name :=
      match e with
      | .outputUnderFunction _ vars => vars
      | .outputInputUnderSameCtor _ _ vars => vars
      | .repeatedOutput _ vars => vars
      | .outputsUnbound vars => vars
      | _ => []
    -- A `Sort`-typed binder carries no runtime value, so nothing can generate it; a variable already
    -- being generated cannot be the blocker, and re-adding it would loop.
    let generable := blockers.filter (fun v =>
      (c.varSpec? v).any (fun s => !s.isSort) && !plan.contains (PlanStep.inst v))
    match generable with
    | [] => .error e
    | vs => repairLowered rel key c (vs.foldl (Plan.insertInst c) plan) budget'
  termination_by budget

/-- `repairLowered`, keeping only the schedule. The plan it returns is the *repaired* one, including any
    `inst`s it had to insert. -/
def repair (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (plan : Plan) (budget : Nat := 8) :
    Except PlanError (Plan × Schedule) :=
  (fun (p, l) => (p, l.schedule)) <$> repairLowered rel key c plan budget

/-- The variables an ordering has to generate unconstrained, and so the `Arbitrary` leaves it needs
    registered. `[]` means every variable is produced by a premise or bound by the conclusion;
    `none` means the ordering cannot be made to work at all. -/
def requiredInstVars (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (plan : Plan) :
    Option (List Name) :=
  match repair rel key c plan with
  | .ok (plan', _) => some (plan'.instVars.filter (fun v => !plan.instVars.contains v))
  | .error _ => none

/-- Every sublist of `l`, shortest first. The compile-time counterpart is
    `subsetsAndComplements`, which splits the producible variables into the ones a premise produces
    and the ones generated unconstrained.

    Exponential; prefer `subsetsUpToSize`. -/
def subsetsBySize {α : Type} (l : List α) : List (List α) :=
  let all := l.foldr (fun x acc => acc ++ acc.map (fun s => x :: s)) [[]]
  (List.range (l.length + 1)).flatMap (fun k => all.filter (fun s => s.length == k))

/-- Sublists of `l` of size at most `maxSize`, shortest first.

    Bounded rather than exponential, and the bound is not much of a restriction: pre-generating a
    variable is a move that trades a producer for a check, and doing it to *many* variables at once is
    almost never the schedule you want — it is generate-and-test on everything. Two at a time covers
    the useful cases and keeps the count quadratic. -/
def subsetsUpToSize {α : Type} (maxSize : Nat) (l : List α) : List (List α) :=
  let rec go (n : Nat) (xs : List α) : List (List α) :=
    match n, xs with
    | 0, _ => [[]]
    | _, [] => [[]]
    | n' + 1, y :: ys =>
      let without := go (n' + 1) ys
      let with_ := (go n' ys).map (fun s => y :: s)
      without ++ with_
  -- `go` already yields each subset once — the two branches differ on whether `y` is present — so
  -- only the size ordering is left to impose.
  let all := go maxSize l
  (List.range (maxSize + 1)).flatMap (fun k => all.filter (fun s => s.length == k))

/-- The variables a plan may choose to generate unconstrained instead of having a premise produce
    them: the constructor's value-level binders that the conclusion does not already bind. -/
def CtorSpec.producibleVars (rel : RelSpec) (key : SpecKey) (c : CtorSpec) : List Name :=
  match schedulePrologue rel key c with
  | .error _ => []
  | .ok pro =>
    c.vars.filterMap (fun s =>
      let n := (pro.subst.find? (fun p => p.1 == s.name)).elim s.name Prod.snd
      if s.isSort || pro.bound.contains n then none else some n)

/-! ### Which premises does moving this one actually commute with?

    Relocating a premise past one it shares no variable with cannot change which variables are bound
    where, so it lowers to the same steps in a different order: the same polarity decision for every
    premise, the same callee mode for every call. Only premises that *do* share a variable — plus the
    `inst` of one of this premise's own variables, since crossing that flips whether the premise
    produces or consumes it — delimit positions that mean anything.

    `SearchTree.getNeighbors`/`splitIntoChunks` call these **anchors**, and the compile-time pipeline
    has always enumerated orderings per connected component (`enumSchedulesChunked` over `sccGroups`)
    rather than over all `n!`. This is the runtime counterpart, and it is why a blind permutation is
    the wrong generator: a premise with two anchors has a handful of distinct positions, not `n`. -/

/-- The value-level variables premise `i` mentions. Sort variables are excluded: they carry no runtime
    value, so sharing one is not a data dependency. -/
def CtorSpec.premiseVars (c : CtorSpec) (i : Nat) : List Name :=
  match c.hypotheses[i]? with
  | none => []
  | some hyp =>
    let sorts := (c.vars.filter VarSpec.isSort).map VarSpec.name
    ((hyp.2.flatMap varsInConstructorExpr).filter (fun v => !sorts.contains v)).eraseDups

/-- Premises that do **not** commute with premise `i`: those sharing at least one value variable.
    The neighbour relation of `SearchTree.getNeighbors`, computed on `CtorSpec` instead of `Expr`. -/
def CtorSpec.anchorsOf (c : CtorSpec) (i : Nat) : List Nat :=
  let mine := c.premiseVars i
  (List.range c.hypotheses.length).filter (fun j =>
    j != i && (c.premiseVars j).any mine.contains)

/-- Connected components of the share-a-variable graph, as premise-index groups, each ascending and in
    order of first appearance.

    Cross-component order cannot affect any premise's polarity, so enumerating orderings *within*
    components and leaving the components where they are covers every distinct polarity assignment —
    whereas a blind `permutationsUpTo` merely truncates and can lose the best ordering unseen. -/
def CtorSpec.premiseComponents (c : CtorSpec) : List (List Nat) :=
  let n := c.hypotheses.length
  -- Repeated absorption rather than union-find: clearer, and `n` is a premise count.
  let grow := fun (comp : List Nat) =>
    (List.range n).filter (fun j =>
      comp.contains j || comp.any (fun i => (c.anchorsOf i).contains j))
  let rec close (comp : List Nat) (fuel : Nat) : List Nat :=
    match fuel with
    | 0 => comp
    | f + 1 =>
      let comp' := grow comp
      if comp'.length == comp.length then comp else close comp' f
  (List.range n).foldl (fun acc i =>
    if acc.any (fun g => g.contains i) then acc else acc ++ [close [i] n]) []

/-- Orderings of `0 .. n-1` that permute *within* each connected component and leave the components in
    place, capped at `limit`.

    The product of the components' factorials rather than `n!`. When a constructor's premises are one
    big component this degrades to `permutationsUpTo` and is no worse; when they are not — the common
    case — it is both smaller and *complete*, because the orderings it omits provably lower to the same
    schedule as ones it keeps. -/
def componentOrderings (c : CtorSpec) (limit : Nat) : List (List Nat) :=
  let comps := c.premiseComponents
  -- Positions each component occupies in the declared order; a component's permutations are written
  -- back into exactly those slots, so the components never interleave differently.
  let slotsOf := fun (g : List Nat) => g
  comps.foldl (fun (acc : List (List Nat)) g =>
    let perms := permutationsUpTo limit g
    let slots := slotsOf g
    -- Splice each permutation of this component into the running orderings.
    let out := acc.flatMap (fun base =>
      perms.map (fun p =>
        base.map (fun idx =>
          match slots.zipIdx.find? (fun (s, _) => s == idx) with
          | some (_, pos) => p[pos]!
          | none => idx)))
    (out.foldl (fun a x => if a.contains x then a else a ++ [x]) []).take limit)
    [List.range c.hypotheses.length]

/-- Candidate plans for one constructor at one mode, with the schedule each lowers to.

    Two dimensions, because both change the schedule and neither reduces to the other:

* the **order** of the premises, which decides what each one has left to produce;
* which variables are generated **unconstrained** rather than produced by a premise, which is what
  turns `Between lo x hi` from a producer for `x` into a check on an `x` that already exists.

    Enumerated most-faithful-first — the declared order with nothing pre-generated comes first — so
    a caller taking the head gets what the compile-time pipeline would most likely have chosen.
    Rejected candidates come back with their reason rather than being dropped: "this ordering cannot
    work, and here is why" is the useful half of a sweep. `limit` caps the result, since the
    enumeration is a product of a factorial and a powerset. -/
def plansOfLowered (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (limit : Nat := 24)
    (maxInsts : Nat := 2) : List (Plan × Except PlanError Lowered) :=
  let nh := c.hypotheses.length
  let declared := (List.range nh).map PlanStep.use
  -- Orderings first, each with nothing pre-generated. Two reasons for that priority. An ordering is
  -- the dimension `repair` cannot reach on its own, whereas a *needed* `inst` it inserts by itself —
  -- so spending the budget on orderings loses nothing. And pairing every ordering with the empty
  -- subset is what stops a constructor with several producible variables from burning the whole budget
  -- on subsets of one ordering, which is what the previous ordering-outer/subset-inner enumeration did.
  let plain := (componentOrderings c limit).map (fun o => o.map PlanStep.use)
  let rest :=
    if plain.length ≥ limit then []
    else
      let insts := (subsetsUpToSize maxInsts (c.producibleVars rel key)).filter (fun s => !s.isEmpty)
      (insts.take (limit - plain.length)).map (fun vs => vs.map PlanStep.inst ++ declared)
  -- Deduplicate on the *lowered schedule*, not on the plan. Distinct plans routinely lower to the same
  -- schedule, and measuring the same schedule twice is the most expensive thing the search can do —
  -- 115s a go on Cedar. This prune is definitional, not score-based: nothing that could rank
  -- differently is dropped.
  let lowered : List (Plan × Except PlanError Lowered) := (plain ++ rest).map (fun plan =>
    match repairLowered rel key c plan with
    | .ok (plan', low) => (plan', .ok low)
    | .error e => (plan, .error e))
  lowered.foldl (fun (acc : List (Plan × Except PlanError Lowered)) (p, r) =>
    match r with
    | .error _ => acc ++ [(p, r)]
    | .ok low =>
      if acc.any (fun (_, r') =>
          match r' with | .ok l' => l'.schedule == low.schedule | .error _ => false) then acc
      else acc ++ [(p, r)]) []

/-- `plansOfLowered`, keeping only each schedule. -/
def plansOf (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (limit : Nat := 24)
    (maxInsts : Nat := 2) : List (Plan × Except PlanError Schedule) :=
  (plansOfLowered rel key c limit maxInsts).map (fun (p, r) => (p, Lowered.schedule <$> r))

/-- The plans that lowered successfully, with their provenance. -/
def viablePlansLowered (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (limit : Nat := 24) :
    List (Plan × Lowered) :=
  (plansOfLowered rel key c limit).filterMap (fun (p, r) =>
    match r with
    | .ok l => some (p, l)
    | .error _ => none)

/-- The plans that lowered successfully. -/
def viablePlans (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (limit : Nat := 24) :
    List (Plan × Schedule) :=
  (viablePlansLowered rel key c limit).map (fun (p, l) => (p, l.schedule))

/-! ## Estimating where a schedule will discard, without running it

    Measuring discards costs `n` samples per candidate, which is fine for a handful of plans and
    hopeless for a factorial of them. So estimate first, measure the survivors.

    The model follows `Scoring.BudgetAwareScore`, the most developed of the compile-time scorers,
    because the question is the same one and its answers were arrived at the hard way. Four ideas
    carry over:

* **A `SuchThat` is not safe.** It fails exactly as often as the spec it calls fails, and that spec's
  schedule may be full of checks. `Scoring.budgetAwareStepScorer` handles this by reading the
  callee's density out of the derivation memo; here the whole `InterpEnv` is already in hand, so
  `modeDensities` computes the least fixpoint over the mode graph instead — which also copes with the
  cycles a reordering creates (`BST[2]` calling `BST[1,2]` calling `BST[2]`).
* **Risk composes by `max`, not by sum.** A constructor is as weak as its weakest step
  (`Scorable.combine` takes `Density.max`), and a *relation* is as strong as its best constructor
  (`budgetAwareLeafAggregator` takes `bestOf`), because `backtrack` gets to try them all. Summing —
  which an earlier version of this module did — says two cheap checks are worse than one hopeless
  one, and that is backwards.
* **Where a call goes matters as much as whether it fails.** A self-recursive call shares the size
  budget; a call to a *different mode of the same relation* spins up a separate instance and can
  cascade. `Scoring.CallLocality` ranks the latter worst, and reordering premises produces exactly
  those calls, so a sweep that ignored locality would recommend them freely.
* **Most-constrained-producer regret.** If some relation pins a variable to a finite set, producing
  that variable from an open source instead is a generate-and-test in disguise —
  `BudgetAwareScore.selectivity`. The compile-time version needs `Expr`s to find the pinned
  positions; the runtime version reads them off `RelSpec.conclusionArgs`, which is pure data.

What is still *not* modelled is how *likely* a check is to fail. `Scoring` estimates it
(`classifyPassLikelihood`, via arity, polarity and constructor counts); here it is left to
measurement, which is more accurate and, for a plan that survives the static ranking, affordable. -/

/-- The spec a `SuchThat` step on a non-recursive premise calls, at the mode the step needs it in.

    Only `SuchThat` contributes: an `Unconstrained` step's source names a *type*, so it is answered
    by a leaf generator rather than by a spec, and `Rec`/`MutRec` name an already-known function.

    The step's own producer sort decides the callee's: an enumerator step needs an enumerator.

    `typeArgs` records the instantiation, so a polymorphic callee demanded at two different types is two
    different modes rather than one that silently serves both. -/
def stepDepKey? : ScheduleStep → Option SpecKey
  | .SuchThat vs (.NonRec hyp) ps =>
    some { inductiveName := hyp.1,
           deriveSort := if ps == .Enumerator then DeriveSort.Enumerator else .Generator,
           outputIndices := computeOutputIndicesForRewrite hyp.2 (vs.map Prod.fst),
           typeArgs := renderedTypeArgs hyp }
  | _ => none

/-- The *checker* a `Check` step on a non-recursive premise needs.

    A check is a dependency too, and reporting it is what makes a demoted premise self-sufficient:
    without this, every relation that some schedule checks has to have a checker registered by hand —
    25 of them for Cedar's `HasType` closure. `Eq` and `Ne` are excluded, being structural. -/
def stepCheckKey? : ScheduleStep → Option SpecKey
  | .Check (.NonRec hyp) _ =>
    if builtinRelations.contains hyp.1 then none
    else some { inductiveName := hyp.1, outputIndices := [], deriveSort := .Checker,
                typeArgs := renderedTypeArgs hyp }
  | _ => none

/-! ### The two lattices

    `Schedules.Density` already names the four failure modes, so it is reused rather than redeclared;
    it carries no ordering, which is what the helpers below add. Locality has no counterpart outside
    `Scoring` (which the interpreter deliberately does not import — see `Specimen.Interp.CtorWeightFn`
    for the same choice about weights), so it is redeclared here. -/

/-- Badness rank of a failure mode, lower is better: producing a value unconditionally is best,
    rejecting because a proposition is false is worst. Matches `Scoring.Density.toNat`. -/
def densityRank : Density → Nat
  | .Total => 0
  | .Partial => 1
  | .Backtracking => 2
  | .Checking => 3

/-- The worse of two densities — how a constructor's steps combine, since a constructor is as weak as
    its weakest step. -/
def densityWorse (a b : Density) : Density := if densityRank a ≥ densityRank b then a else b

/-- The better of two densities — how a relation's constructors combine, since `backtrack` gets to
    try every one of them. -/
def densityBetter (a b : Density) : Density := if densityRank a ≤ densityRank b then a else b

/-- One-word rendering. -/
def densityRender : Density → String
  | .Total => "total"
  | .Partial => "partial"
  | .Backtracking => "backtracking"
  | .Checking => "checking"

/-- What a call costs in budget terms, mirroring `Scoring.CallLocality`. -/
inductive CallLocality where
  /-- Self or mutual recursion: shares the caller's size budget. -/
  | internal
  /-- A different relation: its own budget, but no interaction with this one's. -/
  | external
  /-- A *different mode of the same relation*: a separate generator over the same data, which is where
      reordering premises tends to land, and where cascades come from. -/
  | sameIndCrossMode
  deriving Repr, BEq, Inhabited

namespace CallLocality

/-- Badness rank, lower is better — matching `Scoring.CallLocality.toNat`. -/
def toNat : CallLocality → Nat
  | .internal => 0
  | .external => 1
  | .sameIndCrossMode => 2

/-- The worse of two localities. -/
def max (a b : CallLocality) : CallLocality := if a.toNat ≥ b.toNat then a else b

/-- One-word rendering. -/
def render : CallLocality → String
  | .internal => "internal"
  | .external => "external"
  | .sameIndCrossMode => "cross-mode"

end CallLocality

/-- What one step contributes to a schedule's risk. -/
structure StepRisk where
  /-- Index of the step in the schedule. -/
  stepIdx : Nat
  /-- The step, rendered. -/
  rendered : String
  /-- How this step can fail. For a `SuchThat` this is the callee's density, not `.Total`. -/
  density : Density
  /-- Where this step's call goes. -/
  locality : CallLocality
  /-- Producing steps that ran before this one, whose work a rejection here throws away. -/
  wasted : Nat
  /-- Whether this rejection could be designed away by a different plan. -/
  avoidable : Bool
  /-- The spec whose risk this step inherited, when it inherited one. What to look at next. -/
  viaCallee : Option SpecKey
  deriving Repr

/-- A whole schedule's risk. Ordered lexicographically by
    `(selectivity, density, locality, wastedWork)`, the same precedence
    `Scoring.BudgetAwareScore` uses. -/
structure ScheduleRisk where
  /-- Worst step density: how this constructor can fail at all. -/
  density : Density := .Total
  /-- Worst call locality. -/
  locality : CallLocality := .internal
  /-- Most-constrained-producer regret: variables produced from an open source that some relation
      pins to a finite set. -/
  selectivity : Nat := 0
  /-- Summed `wasted + 1` over the steps that can reject: how much work rejection costs, and where. -/
  wastedWork : Nat := 0
  /-- Estimated total enumeration width this schedule's steps open up — the number of candidates a
      consumer would sift, summed over the steps that hand it an enumeration.

      Only meaningful for a checker or enumerator schedule. A generator's `SuchThat` draws *one* value
      from its callee, so it pays nothing per candidate; a checker's applies the check to all of them.
      `0` for a generator schedule, which correctly makes the dimension inert there. -/
  enumWidth : Nat := 0
  /-- Per-step detail, in schedule order; only the steps that can reject appear. -/
  steps : List StepRisk := []
  deriving Repr

/-- Whether some spec could produce arguments of `relName`, rather than only test them: a registered
    schedule or leaf producer for any mode of it, or a `RelSpec` able to derive one. -/
def InterpEnv.canProduce (env : InterpEnv) (derivable : List Name) (relName : Name) : Bool :=
  derivable.contains relName
    || env.relations.toList.any (fun p => p.1.inductiveName == relName && !p.1.outputIndices.isEmpty)
    || env.producers.toList.any (fun p => p.1.inductiveName == relName && !p.1.outputIndices.isEmpty)

/-- The density of one step, given what the modes around it cost.

    `.Rec`/`.MutRec` are `.partial` rather than looked up: a self-call shares the size budget and is
    the recursion the schedule is built on, so charging it its own density would be circular. That is
    what `Scoring.budgetAwareStepScorer` does too. -/
def stepDensity (densities : Std.HashMap SpecKey Density) (step : ScheduleStep) : Density :=
  match step with
  | .Unconstrained _ (.NonRec _) _ => .Total
  | .Unconstrained .. => .Partial
  | .Match .. => .Backtracking
  | .Check .. => .Checking
  | .SuchThat _ (.Rec ..) _ | .SuchThat _ (.MutRec ..) _ => .Partial
  | .SuchThat vs (.NonRec hyp) _ =>
    if builtinRelations.contains hyp.1 then .Partial
    else
      match stepDepKey? (.SuchThat vs (.NonRec hyp) .Generator) with
      | some key => (densities[key]?).getD .Partial
      | none => .Partial

/-- The density of one constructor's schedule: its worst step. -/
def scheduleDensity (densities : Std.HashMap SpecKey Density) (sched : Schedule) : Density :=
  sched.1.foldl (fun acc s => densityWorse acc (stepDensity densities s)) .Total

/-- Densities for every registered mode, as the least fixpoint of "a constructor is as weak as its
    weakest step, a relation as strong as its best constructor".

    Iterating from `.total` upward is what makes cycles work: `BST[2]` calling `BST[1,2]` calling
    `BST[2]` has no well-founded order to recurse on, but the system is monotone, so repeated
    relaxation settles. `fuel` bounds it; four density levels times the number of modes is a generous
    ceiling, and stopping early only under-reports. -/
def InterpEnv.modeDensities (env : InterpEnv) (fuel : Nat := 64) :
    Std.HashMap SpecKey Density :=
  let keys := env.relations.toList.map Prod.fst
  let init : Std.HashMap SpecKey Density := keys.foldl (fun m k => m.insert k .Total) ∅
  let step := fun (m : Std.HashMap SpecKey Density) =>
    keys.foldl (fun acc k =>
      match env.relations[k]? with
      | none => acc
      | some rel =>
        let ctorDensities := rel.allSchedules.map (fun (_, s) => scheduleDensity m s)
        -- `backtrack` tries every constructor, so the relation is as good as its best one.
        let d := match ctorDensities with
          | [] => Density.Checking
          | c :: cs => cs.foldl densityBetter c
        acc.insert k d) m
  let rec go (m : Std.HashMap SpecKey Density) : Nat → Std.HashMap SpecKey Density
    | 0 => m
    | n + 1 =>
      let m' := step m
      if keys.all (fun k => (m'[k]?).map densityRank == (m[k]?).map densityRank) then m'
      else go m' n
  go init fuel

/-- Argument positions a relation pins to a *finite* set: positions whose conclusion term is ground —
    no variables — in *every* constructor.

    The runtime counterpart of `Scoring.finitePinnedArgPositions`, which needs `Expr`s and a cache;
    here `RelSpec.conclusionArgs` already holds what is needed. A relation with no constructors pins
    nothing. -/
def RelSpec.finitePinnedPositions (rel : RelSpec) : List Nat :=
  match rel.ctors with
  | [] => []
  | c :: cs =>
    let groundOf := fun (k : CtorSpec) =>
      k.conclusionArgs.map (fun a => (varsInConstructorExpr a).isEmpty)
    let combined := cs.foldl (fun acc k =>
      (acc.zip (groundOf k)).map (fun (a, b) => a && b)) (groundOf c)
    combined.zipIdx.filterMap (fun (ground, i) => if ground then some i else none)

/-- Most-constrained-producer regret, after `BudgetAwareScore.selectivity`: a variable this schedule
    produces from an *open* source (an unconstrained generator or a recursive call) while some
    premise elsewhere pins it to a finite set.

    The pinning premise is the better producer — it can only yield finitely many values — so producing
    the variable freely and letting the pinning premise filter is a generate-and-test in disguise. -/
def scheduleSelectivity (specs : List RelSpec) (sched : Schedule) : Nat :=
  let pinnedOf := fun (relName : Name) =>
    match specs.find? (fun r => r.inductiveName == relName) with
    | some r => r.finitePinnedPositions
    | none => []
  -- Variables produced at all, and those produced from a pinning position.
  let (produced, finitely) := sched.1.foldl (fun (prod, fin) step =>
    match step with
    | .Unconstrained v _ _ => (prod ++ [v], fin)
    | .SuchThat outs (.NonRec (relName, args)) _ =>
      let names := outs.map Prod.fst
      let pinned := pinnedOf relName
      let here := names.filter (fun n => pinned.any (fun i =>
        match args[i]? with | some (ConstructorExpr.Unknown v) => v == n | _ => false))
      (prod ++ names, fin ++ here)
    | .SuchThat outs _ _ => (prod ++ outs.map Prod.fst, fin)
    | _ => (prod, fin)) ([], [])
  -- Variables *some* premise pins, whether or not that premise produced them.
  let pinnable := sched.1.foldl (fun acc step =>
    let srcOf := match step with
      | .SuchThat _ src _ | .Check src _ => some src
      | _ => none
    match srcOf with
    | some (.NonRec (relName, args)) =>
      (pinnedOf relName).foldl (fun a i =>
        match args[i]? with | some (ConstructorExpr.Unknown v) => a ++ [v] | _ => a) acc
    | _ => acc) []
  (pinnable.foldl (fun acc v =>
    if produced.contains v && !finitely.contains v && !acc.contains v then acc ++ [v] else acc)
    []).length

/-! ### How wide is the search a step opens?

    Density says whether a step can *fail*. It says nothing about how much a step makes a consumer
    *sift*, and for a checker that is the dominant cost: `EnumeratorCombinators.enumeratingOpt` applies
    the check to every element of the enumeration it is handed, so a step whose sub-enumerator emits ten
    thousand candidates costs ten thousand check evaluations while looking perfectly `Total`.

    So estimate the width. A constructor's enumeration is the *product* of its producing steps' widths —
    each combination of their outputs is a candidate — and a mode's is the **sum** over its
    constructors, because `enumerate` concatenates rather than choosing. That sum-of-products is the
    opposite of the generator's min-of-max, and for the same reason: an enumerator visits every
    alternative, a generator picks one.

    The recurrence terminates without a fixpoint. A same-family call reduces the size budget
    (`sizeExpr`), so it recurses on a strictly smaller size; a cross-family call keeps `initSize` but
    families form a DAG once `linkMutualCalls` has run, so it cannot cycle. `fuel` is a backstop, and
    `ceiling` caps the arithmetic so an estimate on a wide domain stays a number rather than an
    overflow. -/

/-- A static estimate of how many elements a mode's enumeration emits.

    **A width of `0` is a correctness signal, not a cost win.** It means no constructor contributes at
    that size — typically a relation with no base case, asked at size `0` — so the enumeration is
    *empty*. A checker consulting it can only ever answer `false` or "don't know", and a product
    containing it collapses to `0`, which makes the whole schedule look free. Cheap and useless are not
    the same thing, and the analogous confusion in the generator model is what `Scoring`'s
    `uncoveredPenalty` exists to prevent. Read `count == 0` as "this will not produce anything", and see
    it in Cedar as `LubQualified` at small sizes. -/
structure EnumWidth where
  /-- Estimated element count, capped at the caller's ceiling. -/
  count : Nat := 1
  /-- Whether the ceiling or the fuel bound was hit, so `count` is a lower bound. -/
  saturated : Bool := false
  deriving Repr, Inhabited

namespace EnumWidth

/-- Combines two widths multiplicatively — two producing steps in the same constructor, whose outputs
    pair up. -/
def mul (ceiling : Nat) (a b : EnumWidth) : EnumWidth :=
  let n := a.count * b.count
  if n ≥ ceiling then { count := ceiling, saturated := true }
  else { count := n, saturated := a.saturated || b.saturated }

/-- Combines two widths additively — two constructors of the same mode, whose enumerations
    concatenate. -/
def add (ceiling : Nat) (a b : EnumWidth) : EnumWidth :=
  let n := a.count + b.count
  if n ≥ ceiling then { count := ceiling, saturated := true }
  else { count := n, saturated := a.saturated || b.saturated }

/-- Rendering for reports. -/
def render (w : EnumWidth) : String := s!"{w.count}{if w.saturated then "+" else ""}"

end EnumWidth

/-- Declared widths for the enumerator *leaves* — the unconstrained enumerators, keyed by type head.

    These cannot be derived: the interpreter holds a `ValEnum` as a function, so its cardinality is
    only discoverable by walking it. `InterpEnv.enumCost` measures one; this table is where a caller
    records what it found, or an a-priori bound. An unlisted type is assumed to contribute
    `defaultLeafWidth`, which is deliberately not 1 — assuming a leaf yields a single value would make
    every plan that draws from one look free. -/
structure EnumWidthModel where
  /-- Per-type-head widths, as a function of the size the enumerator is given. -/
  leaves : List (Name × Nat) := []
  /-- Assumed width of a leaf with no entry. -/
  defaultLeafWidth : Nat := 8
  /-- Ceiling on any estimate; also the point at which `saturated` is reported. -/
  ceiling : Nat := 100000
  deriving Repr, Inhabited

/-- The recorded or assumed width of a leaf enumerator. -/
def EnumWidthModel.leafWidth (m : EnumWidthModel) (tyHead : Name) : Nat :=
  ((m.leaves.find? (fun p => p.1 == tyHead)).map Prod.snd).getD m.defaultLeafWidth

/-- Memo for `enumWidthOf`, keyed by the mode and the size it was asked about.

    Not an optimisation. Without it the recursion is exponential in depth — each mode expands every
    dependency, which expands every one of *its* dependencies — and on Cedar's 145-mode closure it does
    not terminate in ten minutes. The `ceiling` caps the arithmetic, not the recursion. With the memo,
    total work is bounded by (modes × distinct sizes), which is small. -/
abbrev EnumWidthMemo := Std.HashMap (SpecKey × Nat) EnumWidth

/-- Estimates the enumeration width of a mode at a size, memoised.

    `fuel` bounds the descent as a backstop for a cycle the memo cannot break — a same-size
    cross-family call, which `linkMutualCalls` should have converted to `MutRec` but which a
    hand-written schedule could still contain. Exceeding it reports `saturated`, never a wrong number.

    The memo is seeded with the in-progress key before recursing, so a cycle sees a saturated
    placeholder rather than looping. -/
partial def InterpEnv.enumWidthCore (env : InterpEnv) (m : EnumWidthModel) (key : SpecKey)
    (size : Nat) (fuel : Nat) : StateM EnumWidthMemo EnumWidth := do
  if let some cached := (← get)[(key, size)]? then
    return cached
  match fuel with
  | 0 => return { count := m.ceiling, saturated := true }
  | fuel' + 1 =>
    -- Seed before recursing: a cycle then reads this placeholder instead of looping forever.
    modify (·.insert (key, size) { count := m.ceiling, saturated := true })
    let result ←
      match env.relations[key]? with
      | none =>
        -- Two very different reasons a mode is absent, and conflating them inverts the ranking. A
        -- registered leaf enumerator has an unknown but presumably ordinary width. A mode absent
        -- *entirely* is one the closure never derived, so its width is genuinely unknown — and since
        -- this is an upper bound on cost, unknown must be pessimistic. Treating it as
        -- `defaultLeafWidth` made a plan calling an underived mode rank as the *cheapest* available,
        -- which is exactly backwards.
        pure (if (env.enumProducers[key]?).isSome then { count := m.defaultLeafWidth }
              else { count := m.ceiling, saturated := true })
      | some rel => do
        let (baseScheds, recScheds) := rel.bucketedSchedules
        let scheds := match size with
          | 0 => baseScheds
          | _ => baseScheds ++ recScheds
        let mut total : EnumWidth := { count := 0 }
        for (_, sched) in scheds do
          let steps := sched.1
          let numRecCalls := countSizeConsumingCalls rel.key.inductiveName steps
          let size' := match size with | 0 => 0 | n + 1 => n
          let sizeExpr := if numRecCalls ≤ 1 then size' else size' / numRecCalls
          let mut ctorWidth : EnumWidth := { count := 1 }
          for step in steps do
            match step with
            | .Unconstrained _ (.NonRec hyp) _ =>
              ctorWidth := EnumWidth.mul m.ceiling ctorWidth { count := m.leafWidth hyp.1 }
            | .Unconstrained _ (.Rec ..) _ | .Unconstrained _ (.MutRec ..) _
            | .SuchThat _ (.Rec ..) _ | .SuchThat _ (.MutRec ..) _ =>
              -- Shares the caller's budget, so it recurses on a strictly smaller size.
              let w ← env.enumWidthCore m { key with deriveSort := .Enumerator } sizeExpr fuel'
              ctorWidth := EnumWidth.mul m.ceiling ctorWidth w
            | .SuchThat vs (.NonRec hyp) ps =>
              if builtinRelations.contains hyp.1 then
                -- `Eq` solves for its unknown side: exactly one solution.
                pure ()
              else
                match stepDepKey? (.SuchThat vs (.NonRec hyp) ps) with
                | none =>
                  ctorWidth := EnumWidth.mul m.ceiling ctorWidth { count := m.defaultLeafWidth }
                | some dep =>
                  -- Same inductive shares the budget; anything else restarts at `initSize`, which is
                  -- safe because families form a DAG after `linkMutualCalls`.
                  let depSize := if hyp.1 == rel.key.inductiveName then sizeExpr else size
                  let w ← env.enumWidthCore m { dep with deriveSort := .Enumerator } depSize fuel'
                  ctorWidth := EnumWidth.mul m.ceiling ctorWidth w
            -- Checks and matches only ever *prune*, and by an unknown factor. Treating them as
            -- neutral makes the estimate an upper bound, which is the safe direction for a cost.
            | .Check .. | .Match .. => pure ()
          total := EnumWidth.add m.ceiling total ctorWidth
        -- The size-0 failsafe: with recursive constructors left untried, the enumeration ends in one
        -- out-of-fuel entry (as the emitted code's does), which a consumer walks like any other.
        if size == 0 && !recScheds.isEmpty then
          total := EnumWidth.add m.ceiling total { count := 1 }
        pure total
    modify (·.insert (key, size) result)
    return result

/-- Estimates the enumeration width of a mode at a size — how many candidates a consumer would sift.

    A constructor's width is the *product* of its producing steps' widths (each combination of their
    outputs is a candidate); a mode's is the **sum** over constructors, because `enumerate`
    concatenates rather than choosing. That sum-of-products is the mirror image of the generator's
    min-of-max, and for the same reason: an enumerator visits every alternative, a generator picks one.

    An upper bound: checks and matches prune by a factor no static pass can know, so they count as
    neutral. Upper is the safe direction for a cost. -/
def InterpEnv.enumWidthOf (env : InterpEnv) (m : EnumWidthModel) (key : SpecKey)
    (size : Nat) (fuel : Nat := 32) : EnumWidth :=
  (env.enumWidthCore m key size fuel).run' ∅

/-- Estimates a schedule's risk without running it.

    `specs` supplies the relations `selectivity` needs to find finitely-pinned positions, and
    `derivable` names the relations a caller would derive a new mode of on demand (which is what makes
    a check on one of them *avoidable*). -/
def InterpEnv.estimateRisk (env : InterpEnv) (key : SpecKey) (sched : Schedule)
    (specs : List RelSpec := []) (derivable : List Name := []) (size : Nat := 8)
    (widthModel : EnumWidthModel := {}) : ScheduleRisk :=
  let densities := env.modeDensities
  let (steps, _) := sched.1.zipIdx.foldl (fun (acc, produced) (step, i) =>
    let d := stepDensity densities step
    let callee := stepDepKey? step
    let locality : CallLocality :=
      match step with
      | .SuchThat _ (.Rec ..) _ | .SuchThat _ (.MutRec ..) _
      | .Unconstrained _ (.Rec ..) _ | .Unconstrained _ (.MutRec ..) _
      | .Check (.Rec ..) _ | .Check (.MutRec ..) _ => .internal
      | .SuchThat _ (.NonRec (n, _)) _ | .Check (.NonRec (n, _)) _ =>
        if n == key.inductiveName then .sameIndCrossMode else .external
      | _ => .internal
    let produced' := match step with
      | .SuchThat .. | .Unconstrained .. => produced + 1
      | _ => produced
    -- Only steps that can reject carry an entry; a `Total` step cannot.
    if d == .Total then (acc, produced')
    else
      let avoidable := match step with
        | .Check (.NonRec (n, _)) _ => env.canProduce derivable n
        -- A `SuchThat` that inherits `checking` is avoidable when a *different* mode of the callee
        -- might not be: that is precisely what reordering the premises explores.
        | .SuchThat _ (.NonRec (n, _)) _ => d == .Checking && env.canProduce derivable n
        | _ => false
      (acc ++ [{ stepIdx := i, rendered := ppStep step, density := d, locality := locality,
                 wasted := produced, avoidable := avoidable, viaCallee := callee : StepRisk }],
       produced'))
    ([], 0)
  -- Enumeration width, for the sorts that pay per candidate. A generator's sub-producer yields one
  -- value per call, so the dimension is inert there and is left at 0.
  let enumWidth :=
    if key.deriveSort == .Generator then 0
    else sched.1.foldl (fun acc step =>
      match step with
      | .Unconstrained _ (.NonRec hyp) _ => acc + widthModel.leafWidth hyp.1
      | .SuchThat _ (.Rec ..) _ | .SuchThat _ (.MutRec ..) _
      | .Unconstrained _ (.Rec ..) _ | .Unconstrained _ (.MutRec ..) _ =>
        acc + (env.enumWidthOf widthModel { key with deriveSort := .Enumerator } size).count
      | .SuchThat vs (.NonRec hyp) ps =>
        if builtinRelations.contains hyp.1 then acc
        else match stepDepKey? (.SuchThat vs (.NonRec hyp) ps) with
          | none => acc + widthModel.defaultLeafWidth
          | some dep =>
            acc + (env.enumWidthOf widthModel { dep with deriveSort := .Enumerator } size).count
      | _ => acc) 0
  { density := steps.foldl (fun acc r => densityWorse acc r.density) .Total
    locality := steps.foldl (fun acc r => CallLocality.max acc r.locality) .internal
    selectivity := scheduleSelectivity specs sched
    enumWidth := enumWidth
    wastedWork := steps.foldl (fun acc r =>
      acc + (r.wasted + 1) * (if r.avoidable then 2 else 1)) 0
    steps := steps }

/-- Ranking key, lower is better, in `Scoring.BudgetAwareScore`'s precedence: regret first, then how
    the schedule can fail, then what its calls cost, then how wide a search they open, then how much
    work a rejection throws away.

    `enumWidth` sits below `locality` and above `wastedWork`: it is `0` for a generator, so it never
    disturbs the generator ranking, and for a checker it is the dominant real cost — far more so than
    the position of a rejecting step, which is what `wastedWork` measures. -/
def ScheduleRisk.rank (r : ScheduleRisk) : Nat × Nat × Nat × Nat × Nat :=
  (r.selectivity, densityRank r.density, r.locality.toNat, r.enumWidth, r.wastedWork)

/-- Lexicographic comparison on `ScheduleRisk.rank`. -/
def ScheduleRisk.better (a b : ScheduleRisk) : Bool :=
  let (a₁, a₂, a₃, a₄, a₅) := a.rank
  let (b₁, b₂, b₃, b₄, b₅) := b.rank
  if a₁ != b₁ then a₁ < b₁
  else if a₂ != b₂ then a₂ < b₂
  else if a₃ != b₃ then a₃ < b₃
  else if a₄ != b₄ then a₄ < b₄
  else a₅ < b₅

/-- A single number for coarse ranking and reports. Prefer `ScheduleRisk.better`, which does not
    conflate the dimensions. -/
def ScheduleRisk.score (r : ScheduleRisk) : Nat :=
  r.selectivity * 1000 + densityRank r.density * 100 + r.locality.toNat * 20
    + r.enumWidth + r.wastedWork

/-- Renders a risk estimate: the summary, then each step that can reject and why. -/
def renderRisk (r : ScheduleRisk) : String :=
  let head :=
    s!"[interp] risk: {densityRender r.density} · {r.locality.render} · selectivity {r.selectivity} \
      · enum width {r.enumWidth} · wasted {r.wastedWork}"
  if r.steps.isEmpty then head ++ "\n  nothing in this schedule can reject"
  else
    let rows := r.steps.map (fun s =>
      let tag := if s.avoidable then "avoidable" else "irreducible"
      let via := match s.viaCallee with
        | some k => s!" via {renderSpecKey k}"
        | none => ""
      s!"  step {s.stepIdx}: {densityRender s.density}{via}, {s.locality.render}, \
        wastes {s.wasted}, {tag}  —  {s.rendered}")
    head ++ "\n" ++ "\n".intercalate rows

/-- Candidate plans ranked by estimated risk, cheapest first, without running anything.

    The cheap pre-filter for a sweep: rank every ordering statically, then spend samples on the top
    few. Plans that are not schedules sort last, since they have no risk to compare. -/
def rankPlansByRisk (env : InterpEnv) (rel : RelSpec) (key : SpecKey) (c : CtorSpec)
    (limit : Nat := 24) (specs : List RelSpec := []) (derivable : List Name := []) :
    List (Plan × Except PlanError Schedule × Option ScheduleRisk) :=
  let scored := (plansOf rel key c limit).map (fun (p, r) =>
    match r with
    | .ok sched => (p, r, some (env.estimateRisk key sched specs derivable))
    | .error _ => (p, r, none))
  scored.foldl (fun acc t =>
    let rec ins : List (Plan × Except PlanError Schedule × Option ScheduleRisk) →
        List (Plan × Except PlanError Schedule × Option ScheduleRisk)
      | [] => [t]
      | u :: us =>
        match t.2.2, u.2.2 with
        | some a, some b => if a.better b then t :: u :: us else u :: ins us
        | some _, none => t :: u :: us
        | none, _ => u :: ins us
    ins acc) []


/-! ## Mutating a plan where it discards

    A discard-guided search needs mutations aimed at the premise that caused the discards, not random
    reshuffles. Two things can be done to a premise that rejects too often:

* **Move it earlier.** A check that fails 90% of the time should fail before the work it invalidates,
  not after. This is pure win when it is legal.
* **Make it produce instead of test.** A premise that is a `Check` only because its variable was
  already bound becomes a producer once that variable is *not* pre-generated — dropping the
  corresponding `inst` step, or moving the premise ahead of whatever bound the variable, converts a
  rejection sampler into a constrained one. That is the mutation that actually removes discards
  rather than relocating them.

The reverse is worth trying too: a premise that produces via an expensive or badly-distributed
producer sometimes does better as `arbitrary`-then-check. `mutationsFor` offers both directions and
lets measurement decide. -/

namespace Plan

/-- Where premise `hypIdx` sits in the plan, if it is scheduled. -/
def useIndex? (plan : Plan) (hypIdx : Nat) : Option Nat :=
  (plan.zipIdx.find? (fun (s, _) => s == PlanStep.use hypIdx)).map Prod.snd

/-- Moves the entry at `from_` to position `to`, shifting the rest. -/
def moveTo (plan : Plan) (from_ to : Nat) : Plan :=
  match plan[from_]? with
  | none => plan
  | some s => (plan.eraseIdx from_).insertIdx (min to (plan.length - 1)) s

/-- Moves premise `hypIdx` one position earlier. -/
def moveUseEarlier (plan : Plan) (hypIdx : Nat) : Plan :=
  match plan.useIndex? hypIdx with
  | some i => if i == 0 then plan else plan.moveTo i (i - 1)
  | none => plan

/-- Moves premise `hypIdx` to the very front, ahead of everything that might have bound its
    variables — the mutation that can turn a `Check` back into a producer. -/
def moveUseFirst (plan : Plan) (hypIdx : Nat) : Plan :=
  match plan.useIndex? hypIdx with
  | some i => plan.moveTo i 0
  | none => plan

/-- Moves premise `hypIdx` one position later. -/
def moveUseLater (plan : Plan) (hypIdx : Nat) : Plan :=
  match plan.useIndex? hypIdx with
  | some i => plan.moveTo i (i + 1)
  | none => plan

/-- Swaps the positions of two premises. -/
def swapUses (plan : Plan) (i j : Nat) : Plan :=
  match plan.useIndex? i, plan.useIndex? j with
  | some a, some b =>
    plan.zipIdx.map (fun (s, k) => if k == a then .use j else if k == b then .use i else s)
  | _, _ => plan

/-- Drops the unconstrained generation of `v`, so a premise mentioning `v` must produce it. -/
def dropInst (plan : Plan) (v : Name) : Plan :=
  plan.filter (fun s => s != PlanStep.inst v)

end Plan

/-- Every position for premise `i` that yields a distinct schedule, as a plan.

    The slots are the ones the anchors delimit: before the first anchor, and on either side of each
    anchor thereafter. Two insertion points with no anchor between them produce the same lowering, so
    only one of them is emitted. An `inst` of a variable of `i` counts as an anchor. -/
def Plan.anchorMoves (c : CtorSpec) (plan : Plan) (i : Nat) : List Plan :=
  let anchors := c.anchorsOf i
  let mine := c.premiseVars i
  let isAnchor := fun (s : PlanStep) =>
    match s with
    | .use j => anchors.contains j
    | .inst v => mine.contains v
  match plan.useIndex? i with
  | none => []
  | some at_ =>
    let rest := plan.eraseIdx at_
    let anchorIdxs := (rest.zipIdx.filter (fun (s, _) => isAnchor s)).map Prod.snd
    -- Before the first anchor, then both sides of each anchor. Deduplicated, and clamped by
    -- `insertIdx`'s own bound.
    let slots := ([0] ++ anchorIdxs ++ anchorIdxs.map (· + 1) ++ [rest.length]).foldl
      (fun (acc : List Nat) k => if acc.contains k then acc else acc ++ [k]) []
    slots.map (fun k => rest.insertIdx (min k rest.length) (PlanStep.use i))

/-- Mutations to try next, given the premises that discarded most (heaviest first).

    Ordered by how much they could help. First: stop pre-generating the variables this premise tests
    and put it in front, so it *produces* them instead — that removes the discards rather than
    relocating them. Then every anchor-delimited position, which is the complete set of distinct
    relocations of the blamed premise. Then swaps with its anchors, which move two premises at once and
    so are not relocations. Then the unconstrained generations.

    Blind moves are deliberately absent: `moveUseEarlier`/`moveUseLater` and an all-pairs `swapUses`
    spend most of their candidates on reorderings that lower to the same schedule. Duplicates and
    no-ops are dropped, so an empty result means this plan is a local optimum under these moves. -/
def mutationsFor (c : CtorSpec) (plan : Plan) (blamed : List Nat) : List Plan :=
  let worst := blamed.take 2
  let promote := worst.filterMap (fun i =>
    let vs := (c.premiseVars i).filter (fun v => plan.instVars.contains v)
    if vs.isEmpty then none else some (vs.foldl Plan.dropInst (plan.moveUseFirst i)))
  let moves : List Plan :=
    promote
      ++ worst.flatMap (fun i => plan.anchorMoves c i)
      ++ worst.flatMap (fun i => (c.anchorsOf i).map (fun j => plan.swapUses i j))
      ++ plan.instVars.map (fun v => plan.dropInst v)
      ++ (c.vars.filterMap (fun s =>
        if s.isSort || plan.instVars.contains s.name then none
        else some (PlanStep.inst s.name :: plan)))
  moves.foldl (fun acc p =>
    if p == plan || acc.contains p then acc else acc ++ [p]) []

/-! ## Linking a mutual family

    `HasType`, `HasTypeList`, `HasTypeRecord` and `HasTypeExtCall` call each other. Left as
    `Source.NonRec`, each of those calls is treated as an independent dependency and handed the **full
    `initSize`** with fresh fuel (`interpConstrained`), so the size budget never decreases around the
    cycle and only fuel stops it. `Source.MutRec` instead threads `fuel'` and the caller's split size,
    which is what makes a mutual family shrink.

    So the family has to be identified. The compile-time pipeline does this as a *post-pass* —
    `Schedules.rewriteMutualCalls` over the finished step list, driven by `ScheduleEnv.mutualSiblings` —
    rather than during lowering, and the same works here for a good reason: rewriting `NonRec` to
    `MutRec` never changes *which* mode is called, only how the budget reaches it. So the closure can be
    discovered first with everything `NonRec`, and linked afterwards, with no fixpoint to iterate. -/

/-- Which relations each relation's premises mention. -/
def relationEdges (specs : List RelSpec) : List (Name × List Name) :=
  specs.map (fun r =>
    (r.inductiveName,
     (r.ctors.flatMap (fun c => c.hypotheses.map Prod.fst)).foldl
       (fun acc n => if acc.contains n then acc else acc ++ [n]) []))

/-- Every relation reachable from `a`, including `a`. -/
partial def reachableRelations (edges : List (Name × List Name)) (visited : List Name) (a : Name) :
    List Name :=
  if visited.contains a then visited
  else
    let visited := visited ++ [a]
    match edges.find? (fun e => e.1 == a) with
    | none => visited
    | some (_, outs) => outs.foldl (fun v n => reachableRelations edges v n) visited

/-- Relations partitioned into mutually-recursive families: `a` and `b` share a family when each
    reaches the other through premise references. A relation with no mutual partner is a family of
    one. -/
def mutualGroups (specs : List RelSpec) : List (List Name) :=
  let edges := relationEdges specs
  let names := specs.map RelSpec.inductiveName
  let reach := names.map (fun n => (n, reachableRelations edges [] n))
  let succOf := fun (n : Name) => ((reach.find? (fun p => p.1 == n)).map Prod.snd).getD [n]
  names.foldl (fun groups n =>
    if groups.any (fun g => g.contains n) then groups
    else
      let fam := names.filter (fun m => (succOf n).contains m && (succOf m).contains n)
      groups ++ [if fam.contains n then fam else n :: fam]) []

/-- Rewrites cross-relation `NonRec` calls to `MutRec` wherever caller and callee belong to the same
    mutual family, so those calls share the caller's fuel and split size instead of restarting the
    budget.

    Run *after* the closure is complete: `RelSchedule.depKeys` reads `NonRec` steps to discover what
    still needs deriving, and a `MutRec` step reports nothing, so linking first would truncate the
    walk. -/
def InterpEnv.linkMutualCalls (env : InterpEnv) (specs : List RelSpec) : InterpEnv :=
  let groups := mutualGroups specs
  let familyOf := fun (n : Name) => ((groups.find? (fun g => g.contains n)).getD [n])
  let allModes : List (Name × List Nat × Name × DeriveSort) :=
    env.relations.toList.map (fun (p : SpecKey × RelSchedule) =>
      (p.1.inductiveName, p.1.outputIndices, p.2.recFnName, p.1.deriveSort))
  env.relations.toList.foldl (fun acc (p : SpecKey × RelSchedule) =>
    let (key, rel) := p
    let family := familyOf key.inductiveName
    -- Siblings are the other modes in the family. This mode itself is excluded: a self-call at the
    -- same mode is already `Source.Rec`, which shares the budget by construction.
    let sibs := allModes.filter (fun (n, idxs, _, srt) =>
      family.contains n
        && !(n == key.inductiveName && idxs == key.outputIndices && srt == key.deriveSort))
    let upd := fun (l : List (Name × Schedule)) =>
      l.map (fun (ctor, (steps, srt)) => (ctor, (rewriteMutualCalls steps sibs, srt)))
    acc.addRelation { rel with
      baseSchedules := upd rel.baseSchedules, recSchedules := upd rel.recSchedules }) env

/-! ## Deriving a whole mode at runtime -/

/-- Whether a constructor is recursive at a mode: some premise is about the relation itself.
    Matches the compile-time split into `baseSchedules` and `recSchedules`, whose consequence is the
    emitted `match size with | 0 => <base only> | size' + 1 => <all>`. -/
def CtorSpec.isRecursive (rel : RelSpec) (c : CtorSpec) : Bool :=
  c.hypotheses.any (fun (n, _) => n == rel.inductiveName)

/-- Derives a `RelSchedule` for a mode at runtime: for each constructor, the first plan that
    lowers, starting from the constructor's declared premise order.

    This is what makes a reordering *runnable*. Putting `BST lo x l` before `Between lo x hi`
    turns that premise into a call to `BST[1,2]` — a mode no compile-time derivation produced. Ask
    for it here and the interpreter has it.

    `select` chooses among a constructor's viable plans; the default takes the first, which is the
    declared order with nothing pre-generated. Pass something else to explore.

    `recFnName` overrides the name this mode's own recursive calls use. One relation can have several
    modes registered at once, and `InterpEnv.byFn` maps a name to exactly one of them, so a second
    mode of the same relation needs a distinct name or its self-calls resolve to the first mode's
    generator. `InterpEnv.deriveClosure` mints one; supply it yourself if you register modes by
    hand. -/
def RelSpec.deriveModeBy (rel₀ : RelSpec) (key : SpecKey)
    (choose : RelSpec → CtorSpec → Except String (Schedule × Option CtorProvenance))
    (recFnName : Option Name := none) : Except String RelSchedule := do
  let rel := { rel₀ with recFnName := recFnName.getD rel₀.recFnName }
  if key.inductiveName != rel.inductiveName then
    throw s!"[interp] cannot derive {renderSpecKey key} from a spec for '{rel.inductiveName}'"
  let mut base : List (Name × Schedule) := []
  let mut recs : List (Name × Schedule) := []
  let mut prov : List CtorProvenance := []
  for c in rel.ctors do
    let (sched, p) ← choose rel c
    if let some p := p then prov := prov ++ [p]
    if c.isRecursive rel then recs := recs ++ [(c.ctorName, sched)]
    else base := base ++ [(c.ctorName, sched)]
  return {
    key := key, argNames := rel.argNames, recFnName := rel.recFnName,
    baseSchedules := base, recSchedules := recs, typeArgIndices := rel.typeArgIndices,
    provenance := prov }

/-- The provenance of a plan that lowered to `low`, for `CtorProvenance`. -/
def CtorProvenance.ofLowered (c : CtorSpec) (plan : Plan) (low : Lowered) : CtorProvenance :=
  { ctorName := c.ctorName, plan := plan, origins := low.origins }

def RelSpec.deriveMode (rel₀ : RelSpec) (key : SpecKey) (limit : Nat := 24)
    (select : CtorSpec → List (Plan × Schedule) → Option (Plan × Schedule) := fun _ ps => ps.head?)
    (recFnName : Option Name := none) : Except String RelSchedule :=
  rel₀.deriveModeBy key (recFnName := recFnName) (choose := fun rel c =>
    let lowered := viablePlansLowered rel key c limit
    match select c (lowered.map (fun (p, l) => (p, l.schedule))) with
    | some (plan, sched) =>
      -- The selected pair came from `lowered`, so its provenance is right there: no second lowering.
      .ok (sched, (lowered.find? (fun (p, l) => p == plan && l.schedule == sched)).map
        (fun (p, l) => CtorProvenance.ofLowered c p l))
    | none =>
      -- Report the first reason, which is the one for the declared order.
      let reason :=
        match (plansOf rel key c limit).head? with
        | some (_, .error e) => e.message
        | _ => "no plan enumerated"
      .error s!"[interp] no viable schedule for '{c.ctorName}' at {renderSpecKey key}: {reason}")

/-- Derives modes for several relations and registers them all, so mutually-dependent specs can be
    brought up together. Each entry pairs a relation with the mode wanted from it. -/
def InterpEnv.withDerivedModes (env : InterpEnv) (specs : List (RelSpec × SpecKey))
    (limit : Nat := 24) : Except String InterpEnv :=
  specs.foldlM (fun e (rel, key) => e.addRelation <$> rel.deriveMode key limit) env

/-! ## Choosing a plan this environment can actually run

    `deriveMode` takes the first plan that *lowers*. Lowering only asks whether the plan is
    well-formed, not whether anything can answer the calls it makes, so the first plan may call a
    spec no schedule and no leaf provides. `deriveModeIn` prefers a plan whose every step this
    environment resolves — which, for `Between[1,2]`, is the difference between picking
    `m ← arbitrary Nat; check a₂ ≤ m` and picking `m ← <a producer for a₂ ≤ m>` that nobody
    registered. -/

/-- Whether this environment can answer everything one step needs.

    `selfFn` is the recursive function name of the relation being derived, whose own calls resolve
    once it is registered. `derivable` names the relations a caller is willing to derive a new mode
    of on demand: without it, a plan calling a dependency that has not been reached yet looks
    unresolvable, which biases selection *away* from producer-based plans and towards
    generate-and-check ones — the opposite of what makes a generator efficient. -/
def InterpEnv.stepResolvable (env : InterpEnv) (selfFn : Name) (derivable : List Name)
    (step : ScheduleStep) : Bool :=
  match step with
  | .Match .. => true
  | .Unconstrained _ (.NonRec ty) _ => (env.lookupArbitrary ty).isSome
  | .Unconstrained _ (.Rec f _) _ | .Unconstrained _ (.MutRec f _) _ =>
    f == selfFn || (env.keyOfFn? f).isSome
  | .SuchThat _ (.Rec f _) _ | .SuchThat _ (.MutRec f _) _ =>
    f == selfFn || (env.keyOfFn? f).isSome
  | .SuchThat vs (.NonRec hyp) _ =>
    if builtinRelations.contains hyp.1 || derivable.contains hyp.1 then true
    else match stepDepKey? (.SuchThat vs (.NonRec hyp) .Generator) with
      | some key => (env.relations[key]?).isSome || (env.producers[key]?).isSome
      | none => false
  | .Check (.NonRec hyp) _ => builtinRelations.contains hyp.1 || env.checkers.contains hyp.1
  | .Check (.Rec f _) _ | .Check (.MutRec f _) _ => env.checkers.contains f

/-- Whether this environment can answer every step of a schedule. -/
def InterpEnv.scheduleResolvable (env : InterpEnv) (selfFn : Name) (derivable : List Name)
    (sched : Schedule) : Bool :=
  sched.1.all (env.stepResolvable selfFn derivable)

/-- `RelSpec.deriveMode`, preferring per constructor a plan whose every step this environment resolves,
    and falling back to the first plan that lowers when none does — so a missing leaf shows up in
    `InterpEnv.checkReport` rather than as a silent rejection.

    Among the resolvable plans it takes the one with the fewest `Check` steps, which is the same
    preference `PlanBook.ofInterpDefaults` applies and for the same reason: a `Check` is a premise the
    plan gave up on *producing*, so its outputs get generated freely and tested afterwards, and what
    survives the test is the easy cases. Taking the first resolvable plan instead left that to
    enumeration order — on Cedar's `HasType.set` it produced the element and the list independently and
    then checked `AllLub`, where preferring producers builds the element types from `AllLub` and generates
    elements to fit. `scheduleResolvable` exists to avoid exactly this bias (see its docstring); it rules
    out plans the environment cannot run, but among those it can, order alone decided.

    **Measured as a no-op today, and kept anyway.** A/B on Cedar's `HasType[0,4]` closure: identical
    either way — 152 modes, 3187 steps, *355* `Check` steps, 215 k-paths plain / 336 with dispatch, 780‰ /
    379‰ absorbed. The reason is that `scheduleResolvable` already excludes most check-demoting plans for
    an unrelated reason: a `.Check` step needs a *registered checker*, and most relations have none, so
    those plans are unresolvable before ranking sees them. That protection is incidental and shrinks as
    checkers get registered — Cedar gained thirteen in one sitting — at which point check-demoting plans
    become resolvable and the tie-break starts deciding. `PlanBook.ofInterpDefaults` had no such
    protection, which is why the `set` demote showed up there and not here. -/
def RelSpec.deriveModeIn (rel : RelSpec) (env : InterpEnv) (key : SpecKey) (limit : Nat := 24)
    (recFnName : Option Name := none) (derivable : List Name := []) :
    Except String RelSchedule :=
  let self := recFnName.getD rel.recFnName
  let checksOf := fun (sched : Schedule) =>
    (sched.1.filter (fun st => match st with | .Check _ _ => true | _ => false)).length
  rel.deriveMode key limit (recFnName := recFnName) (select := fun _ ps =>
    let resolvable := ps.filter (fun (_, s) => env.scheduleResolvable self derivable s)
    let fewestChecks := resolvable.foldl (fun acc ps' =>
      match acc with
      | none => some ps'
      | some cur => if checksOf ps'.2 < checksOf cur.2 then some ps' else some cur) none
    fewestChecks.orElse (fun _ => ps.head?))

/-- A recursive-function name for a new mode that no registered relation answers to already.

    Two modes of one relation are two different generators. `InterpEnv.byFn` resolves a name to one
    spec, so reusing `aux_bst` for both `BST[2]` and `BST[1,2]` would silently point one mode's
    self-calls at the other's generator — the arity check in `InterpEnv.check` catches it, but only
    after the fact. -/
def InterpEnv.freshRecFnName (env : InterpEnv) (rel : RelSpec) (key : SpecKey) : Name :=
  if (env.byFn[rel.recFnName]?).isNone then rel.recFnName
  else
    let suffix := "_" ++ "_".intercalate (key.outputIndices.map toString)
    freshen (env.byFn.toList.map Prod.fst) (rel.recFnName.appendAfter suffix)

/-! ## Instantiating a polymorphic relation

    A polymorphic relation is unusable un-instantiated. `MapNotContainsKey {α β} : Map α β → α → Prop`
    has a constructor binder `k : α`, and an `Unconstrained` step for it asks for a generator for `α` —
    a *variable*, which no leaf can answer, so every mode of it is stuck no matter what leaves are
    registered. On Cedar that was the last thing standing between `HasType[0,4]` and a clean closure.

    But the type is never actually unknown: every *call site* supplies it. `HasType` calls
    `MapNotContainsKey` at `α = Attr`, `β = QualifiedType`, and those arguments are sitting in the call's
    reified premise as type-level `ConstructorExpr`s. So monomorphise — substitute them into the
    relation before deriving, the way Lean itself specialises at elaboration.

    Which type variable gets which argument is read off the conclusion: the relation's `typeArgIndices`
    say which conclusion positions are type-level, and a constructor's conclusion names its own sort
    binder there. -/

/-- Substitutes type variables throughout a reified type expression. -/
partial def substTypeVars (subst : List (Name × ConstructorExpr)) :
    ConstructorExpr → ConstructorExpr
  | .Unknown v =>
    match subst.find? (fun p => p.1 == v) with
    | some (_, t) => t
    | none => .Unknown v
  | .TyCtor n args => .TyCtor n (args.map (substTypeVars subst))
  | .Ctor n args => .Ctor n (args.map (substTypeVars subst))
  | e => e

/-- Substitutes type variables in a variable's *type*, including when the type variable is the head.

    The head case is the one that matters for a bare `k : α`; the argument case is what makes
    `r : List (α × β)` resolve, which is how Cedar's record helpers are actually written. -/
def substHypType (subst : List (Name × ConstructorExpr)) (ty : HypothesisExpr) : HypothesisExpr :=
  let args' := ty.2.map (substTypeVars subst)
  match subst.find? (fun p => p.1 == ty.1) with
  | some (_, .TyCtor n as) | some (_, .Ctor n as) => (n, as ++ args')
  | some (_, .Unknown v) => (v, args')
  | _ => (ty.1, args')

/-- The relation with its type parameters replaced by the types a call site supplies.

    A no-op for a monomorphic relation, which is every relation in a first-order development — so this
    costs nothing where it is not needed. -/
def RelSpec.instantiate (rel : RelSpec) (typeArgs : List (Nat × ConstructorExpr)) : RelSpec :=
  if typeArgs.isEmpty then rel
  else
    { rel with ctors := rel.ctors.map fun c =>
        -- The premise's argument position `i` is the conclusion's position `i`, and the constructor names
        -- its own sort binder there. A position whose conclusion is not a bare sort binder contributes
        -- nothing: there is no variable to bind.
        let subst : List (Name × ConstructorExpr) :=
          typeArgs.filterMap fun (i, ta) =>
            match c.conclusionArgs[i]? with
            | some (.Unknown v) => if c.isSortVar v then some (v, ta) else none
            | _ => none
        if subst.isEmpty then c
        else
          { c with
            vars := c.vars.map fun v =>
              if v.isSort then v else { v with ty := substHypType subst v.ty }
            -- Premises and conclusion too, so the instantiation *propagates*. Without this a sibling or
            -- self call still reads `α` in its arguments, `renderedTypeArgs` finds nothing there, and the
            -- callee is derived polymorphic again — one hop down from a mode that knew the answer.
            hypotheses := c.hypotheses.map fun h => (h.1, h.2.map (substTypeVars subst))
            conclusionArgs := c.conclusionArgs.map (substTypeVars subst) } }

/-! ## Closing over the modes a reordering needs

    The runtime counterpart of `specimen.autoDeriveDeps`: putting `BST lo x l` first asks for
    `BST[1,2]`, which asks for `Between[1,2]`, which nothing derived. Rather than making that the
    user's problem, derive the closure. -/

/-- Every spec a registered schedule calls through a non-recursive premise.

    `includeChecks` additionally reports the checkers its `Check` steps need. Off by default, because
    switching it on changes what a *generator* closure contains: a checked relation that would have
    been answered by a registered leaf gets an interpreted checker derived for it instead, and
    `checkSourceIn` prefers the interpreted one. On is what you want when you would otherwise be
    hand-writing checkers; a checker closure forces it on, since a checker schedule is *made* of
    `Check` steps and could not be closed otherwise. -/
def RelSchedule.depKeys (rel : RelSchedule) (includeChecks : Bool := false) : List SpecKey :=
  let checks := if includeChecks then rel.allSchedules.flatMap
    (fun (_, (steps, _)) => steps.filterMap stepCheckKey?) else []
  (rel.allSchedules.flatMap (fun (_, (steps, _)) => steps.filterMap stepDepKey?) ++ checks)
    |>.filter (fun k => !builtinRelations.contains k.inductiveName)

/-- `depKeys`, keeping the type-level arguments each call applies its relation to.

    Needed because a polymorphic callee cannot be derived without them — see `RelSpec.instantiate`. The
    arguments belong to the *call*, not to the key, so they travel alongside it rather than in it. -/
def RelSchedule.depKeysTyped (rel : RelSchedule) (includeChecks : Bool := false) :
    List (SpecKey × List (Nat × ConstructorExpr)) :=
  let typedOf := fun (step : ScheduleStep) (k : SpecKey) =>
    match step with
    | .SuchThat _ (.NonRec hyp) _ | .Check (.NonRec hyp) _ => (k, typeArgsOf hyp)
    | _ => (k, [])
  let deps := rel.allSchedules.flatMap fun (_, (steps, _)) =>
    steps.filterMap fun s => (stepDepKey? s).map (typedOf s)
  let checks := if !includeChecks then [] else rel.allSchedules.flatMap fun (_, (steps, _)) =>
    steps.filterMap fun s => (stepCheckKey? s).map (typedOf s)
  (deps ++ checks).filter (fun (k, _) => !builtinRelations.contains k.inductiveName)

/-- Derives `roots`, then whatever those need, until nothing is missing.

    A key with no `RelSpec` to derive it from is left alone: a leaf producer may already cover it,
    and if not, `InterpEnv.checkReport` names it. `fuel` bounds the worklist; exceeding it is
    reported rather than silently truncated, since a truncated environment would look like a
    schedule that merely fails. -/
def InterpEnv.deriveClosure (env : InterpEnv) (specs : List RelSpec) (roots : List SpecKey)
    (limit : Nat := 24) (fuel : Nat := 64) (deriveCheckers : Bool := false) :
    Except String InterpEnv := do
  let deriveCheckers := deriveCheckers || roots.any (fun k => k.deriveSort != .Generator)
  let mut e := env
  -- Each entry is a mode together with the type arguments the call site that asked for it supplied.
  -- Roots are asked for by the caller, who has no premise to read them off, so they start monomorphic.
  let mut queue : List (SpecKey × List (Nat × ConstructorExpr)) := roots.map (·, [])
  let mut seen : Std.HashSet SpecKey := ∅
  -- What each derived mode was instantiated at, so a second demand at a *different* instantiation is
  -- reported rather than silently answered by the first one's schedule.
  let mut instantiatedAt : List (SpecKey × List (Nat × ConstructorExpr)) := []
  let mut budget := fuel
  while !queue.isEmpty do
    let (key, typeArgs) := queue.headD (default, [])
    queue := queue.tailD []
    if seen.contains key then
      -- Already derived. Fine if this call agrees about the types; a genuine conflict needs the key to
      -- carry the instantiation, which it does not, so say so instead of miscompiling.
      match instantiatedAt.find? (fun p => p.1 == key) with
      | some (_, prior) =>
        if prior != typeArgs then
          throw s!"[interp] {renderSpecKey key} is needed at two different instantiations — \
            {prior.map (fun p => ppConstructorExpr p.2)} and {typeArgs.map (fun p => ppConstructorExpr p.2)}. One schedule cannot \
            serve both, and `SpecKey` does not carry the instantiation, so the modes cannot be told \
            apart. Split the relation, or extend `SpecKey` with its type arguments."
      | none => pure ()
      continue
    seen := seen.insert key
    if (e.relations[key]?).isSome || (e.producers[key]?).isSome then
      continue
    match specs.find? (fun r => r.inductiveName == key.inductiveName) with
    | none => continue
    | some rel₀ =>
      if budget == 0 then
        throw s!"[interp] mode closure did not settle within {fuel} derivations; still wanted \
          {(queue.filter (fun (k, _) => !seen.contains k)).map (fun (k, _) => renderSpecKey k)}"
      budget := budget - 1
      let rel := rel₀.instantiate typeArgs
      instantiatedAt := instantiatedAt ++ [(key, typeArgs)]
      let derived ← rel.deriveModeIn e key limit (recFnName := e.freshRecFnName rel key)
        (derivable := specs.map RelSpec.inductiveName)
      e := e.addRelation derived
      queue := queue ++ (derived.depKeysTyped deriveCheckers).filter (fun (k, _) => !seen.contains k)
  return e.linkMutualCalls specs

/-! ## A plan per constructor, across the whole closure

    One constructor's plan is a local choice; a *generator* is the whole set of them, across every
    mode the closure needs. A `PlanBook` is that set, so a search can hold one candidate assignment,
    swap a single entry, and rebuild everything. -/

/-- Chosen plans, keyed by mode and constructor. Entries are overrides: a mode or constructor absent
    from the book is derived the default way (`RelSpec.deriveModeIn`, resolvable-first). -/
structure PlanBook where
  /-- `(mode, constructor, plan)`. Later entries win, so `set` can simply prepend. -/
  entries : List (SpecKey × Name × Plan) := []
  deriving Repr, Inhabited

namespace PlanBook

/-- The plan chosen for a constructor, if the book names one.

    A mode keyed at type arguments (`SpecKey.typeArgs`, a polymorphic relation at one instantiation)
    falls back to the book's entry for the **uninstantiated** mode when it has none of its own. That is
    what an entry keyed at `typeArgs := []` means: the compile-time pipeline mints only such keys, and
    one polymorphic generator serves every instantiation, so a book read off the deriver
    (`ofOrders` over `chosenOrdersRef`) holds `SetContains[1]` and never `SetContains[1]@(0:EntityType)`.
    Without the fallback those entries were silently never consulted: on Cedar's `HasType[0,4]` closure
    52 generator constructors across 24 instantiated modes ran the interpreter's own default instead of
    the deriver's choice — `MapNotContainsKey.skip` generating `k` blind and checking, where the deriver
    produces it from the recursive call — while being counted as modes the deriver never derived. An
    entry at the instantiated key still wins, so learning can specialise one instantiation. -/
def find? (b : PlanBook) (key : SpecKey) (ctorName : Name) : Option Plan :=
  let exact := fun (k : SpecKey) =>
    (b.entries.find? (fun e => e.1 == k && e.2.1 == ctorName)).map (fun e => e.2.2)
  match exact key with
  | some p => some p
  | none => if key.typeArgs.isEmpty then none else exact { key with typeArgs := [] }

/-- Whether a plan asks for something the compile-time deriver cannot express.

    `derive_mutual` forces `specimen.multiOutput`, under which a premise produces **everything** it can
    and only the genuinely unproducible variables — under a function application, mixed with a bound
    variable beneath one constructor, or nonlinear — fall out to `InstVars`. The deriver never *elects* to
    generate a producible variable unconstrained.

    So a plan carrying an `inst` of a variable the constructor could have produced is unpinnable: there is
    no premise order that reproduces it. Such plans can still be measured here, and doing so was
    informative — 0 of 63 elective insts on Cedar beat their baseline, which is agreement with the
    deriver's rule rather than a discovery about it — but they cannot be shipped, so a search that spends
    its budget on them is measuring something unusable. `plansOf` flags them for that reason.

    `none` means the plan is expressible; `some vars` names the offending variables. Forced insts (the
    ones `repair` inserts to make an ordering lower at all) are not offending: the deriver inserts the
    same ones for the same reasons. -/
def unpinnableInsts (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (plan : Plan) :
    Option (List Name) :=
  let declared : Plan := (List.range c.hypotheses.length).map PlanStep.use
  let forced := match repair rel key c declared with
    | .ok (repaired, _) => Plan.instVars repaired
    | .error _ => []
  let elective := (Plan.instVars plan).filter (fun v => !forced.contains v)
  if elective.isEmpty then none else some elective

/-- The premise orders a book pins, in the form the compile-time deriver takes
    (`DeriveSchedules.PinnedOrders`): indices into the constructor's premises in **declaration** order.

    Plans carrying elective `inst`s are dropped rather than truncated, because a premise order alone
    cannot reproduce them (see `unpinnableInsts`) and silently pinning the order without the `inst` would
    transfer a *different* schedule than the one measured. `dropped` names them so a caller can report
    what did not survive. -/
def toPinnedOrders (b : PlanBook) (specs : List RelSpec) :
    List (SpecKey × Name × List Nat) × List (SpecKey × Name × List Name) :=
  b.entries.foldl (fun (kept, dropped) (key, ctorName, plan) =>
    match specs.find? (fun r => r.inductiveName == key.inductiveName) with
    | none => (kept, dropped)
    | some rel =>
      match rel.ctors.find? (fun c => c.ctorName == ctorName) with
      | none => (kept, dropped)
      | some c =>
        match unpinnableInsts rel key c plan with
        | some vars => (kept, dropped ++ [(key, ctorName, vars)])
        | none =>
          let order := plan.filterMap (fun st => match st with | .use i => some i | .inst _ => none)
          (kept ++ [(key, ctorName, order)], dropped)) ([], [])

/-- The pinned orders a book implies, as Lean source to paste above a `derive_mutual`.

    `toPinnedOrders` returns values; this returns text, because the deriver is reached from a different
    process than the tuning run. The emitted table installs itself with `PinnedOrders.install`, and
    names constructors and inductives with `` `` `` quotation so that a pin naming something that no
    longer exists fails at *compile* time rather than silently not matching.

    Three things do not make it into the table, each reported as a comment so nothing vanishes quietly:
    plans with elective `inst`s (`toPinnedOrders`' `dropped`), and modes keyed at type arguments — a
    polymorphic instantiation has no compiled counterpart to match, since every key the compile-time
    pipeline mints has `typeArgs := []`. -/
def toPinnedOrdersSource (b : PlanBook) (specs : List RelSpec)
    (defName : String := "tunedPinnedOrders") : String :=
  let (kept, dropped) := b.toPinnedOrders specs
  let srtLit := fun (srt : DeriveSort) => match srt with
    | .Generator => "Schedules.DeriveSort.Generator"
    | .Enumerator => "Schedules.DeriveSort.Enumerator"
    | .Checker => "Schedules.DeriveSort.Checker"
    | .Theorem => "Schedules.DeriveSort.Theorem"
  let (polymorphic, mono) := kept.partition (fun (k, _, _) => !k.typeArgs.isEmpty)
  let entry := fun ((k, ctorName, order) : SpecKey × Name × List Nat) =>
    let outsLit := "[" ++ ", ".intercalate (k.outputIndices.map toString) ++ "]"
    let orderLit := "[" ++ ", ".intercalate (order.map toString) ++ "]"
    -- Indentation is load-bearing, not cosmetic: a structure instance's fields are column-sensitive,
    -- so an extra space before `{` puts it past its own continuation lines and the whole thing stops
    -- parsing with "unexpected identifier; expected '}'". Entries are joined with ",\n   " so that
    -- `{` lands in the same column for the first entry (after "  [") and every later one.
    "({ inductiveName := ``" ++ toString k.inductiveName ++ ", outputIndices := " ++ outsLit
      ++ ",\n      deriveSort := " ++ srtLit k.deriveSort ++ " },\n    ``"
      ++ toString ctorName ++ ", " ++ orderLit ++ ")"
  let notes :=
    dropped.map (fun (k, c, vars) =>
      "-- not pinned (elective insts " ++ toString vars ++ "): " ++ toString k.inductiveName
        ++ " as " ++ srtLit k.deriveSort ++ " · " ++ toString c)
    ++ polymorphic.map (fun (k, c, _) =>
      "-- not pinned (mode is keyed at type arguments " ++ toString k.typeArgs
        ++ ", which no compiled mode carries): " ++ toString c)
  if mono.isEmpty then
    "\n".intercalate (notes ++ ["-- " ++ defName ++ ": nothing pinnable in this book."])
  else
    "\n".intercalate
      (notes
       ++ [ "/-- Generated from a tuned `PlanBook` by `PlanBook.toPinnedOrdersSource`. -/"
          , "def " ++ defName ++ " : Schedules.PinnedOrders :="
          , "  [" ++ ",\n   ".intercalate (mono.map entry) ++ "]"
          , ""
          , "run_cmd Schedules.PinnedOrders.install " ++ defName ])

/-- Replaces (or adds) the plan for one constructor of one mode. -/
def set (b : PlanBook) (key : SpecKey) (ctorName : Name) (plan : Plan) : PlanBook :=
  { entries := (key, ctorName, plan) ::
      b.entries.filter (fun e => !(e.1 == key && e.2.1 == ctorName)) }

/-- How many constructors the book pins. -/
def size (b : PlanBook) : Nat := b.entries.length

/-- A book from premise orders in declaration-index form — the compile-time deriver's own choices, read
    off `Schedules.chosenOrdersRef` after a `derive_mutual`.

    This is the starting point for learning: begin from what branch and bound settled on, measure where
    it fails, and perturb only there, so that every entry the learned book ends up differing on is a
    place where dynamic measurement beat the static estimate. Takes plain tuples so `Interp` keeps its
    independence from the deriver. -/
def ofOrders (orders : List (SpecKey × Name × List Nat)) : PlanBook :=
  orders.foldl (fun b (k, c, o) => b.set k c (o.map PlanStep.use)) {}

/-- Books, for every constructor of `key`, the plan with the fewest `Check` steps — the book worth
    emitting when the goal is compile *time* rather than output quality.

    Pinned constructors skip the search and, with it, the speculative dependency derivation that the
    compile-time profile put at ~60% of search self-time, so fewer modes get minted at all.

    **No time saving is quoted here, deliberately.** The figures this docstring used to carry (a Cedar
    derivation "92.3s → 56.2s at coverage parity") are withdrawn. They were measured while every pin for a
    constructor with a non-linear conclusion had the wrong length — the interpreter has no premise for a
    non-linearity equality, the deriver does — and `deriveBestInductiveSchedule` swallowed the resulting
    error and **dropped the constructor**, so `HasType.var*` and their siblings were simply missing from the
    "pinned" generator. `searchBestScheduleM` now translates between the two bases and reports an
    unusable pin with `logError` instead. Re-measure before quoting a saving.

    **Pass a generous `limit`.** The default 24 never enumerates the one ordering that stops `iteAnyBool`
    demoting `Lub` (see below): only 16 of its 7! orderings are reached, and all 16 keep `Lub` late, while
    `limit := 400` reaches 283 viable plans, several with no check at all. Emitting a pin table is offline
    and one-off — `limit := 200` across both of Cedar's `HasType` modes and all 152 constructors cost 3.4s —
    so there is no reason to economise here, unlike in `deriveModeIn`, which runs on every closure build.

    **Fewest checks, not first-that-lowers, is what makes it free.** `deriveMode`'s `.head?` demoted a
    premise on two of `HasType`'s 76 constructors — `set` and `iteAnyBool` — and those two are where the
    fan-out is. (The coverage loss once measured for it came from the same runs as the withdrawn timings
    above, so it is not quoted; the schedules themselves were inspected directly.) For `set`, `.head?`
    produced element and list independently and then
    *checked* `AllLub`, which is generate-and-test: the survivors are the sets whose element types happened
    to agree. Fewest-checks instead produces `xs, tyList` from `HasTypeList` and `ty` from `AllLub`, so the
    types are built rather than filtered.

    `iteAnyBool` still carries a check at the default `limit`, but *not* because no ordering avoids one:
    raising the bound to 400 enumerates 283 viable plans, several with zero checks, shaped the same way
    (one branch, then `Lub` producing the other branch's type, then that branch generated to fit). At
    `limit := 24` only 16 orderings are reached and every one of them keeps `Lub` late. So a `Check` that
    survives every plan is evidence about the **enumeration bound**, not about the constructor — worth
    remembering before concluding a demotion is forced.

    Constructors with no viable plan are skipped rather than reported: they have no order to pin, and the
    deriver is no worse off searching for one. -/
def ofInterpDefaults (rel : RelSpec) (key : SpecKey) (limit : Nat := 24) : PlanBook :=
  -- Fewest `Check` steps wins, ties going to enumeration order (which is what `deriveMode` would have
  -- taken). A `Check` is a premise the plan gave up on *producing*, so the schedule generates its
  -- outputs freely and tests them afterwards — and the survivors of that test are the easy cases.
  -- Measured on Cedar: `.head?` demoted a premise on exactly two of `HasType`'s 76 constructors, `set`
  -- and `iteAnyBool`, but those two are where the fan-out is, and pinning them cost seven `set→…`
  -- constructor pairs. For `set` the search produces the element types from `AllLub` first and generates
  -- elements *for* them, where `.head?` produced element and list independently and checked `AllLub`
  -- afterwards.
  let checksOf := fun (sched : Schedule) =>
    (sched.1.filter (fun st => match st with | .Check _ _ => true | _ => false)).length
  let best := fun (ps : List (Plan × Schedule)) =>
    ps.foldl (fun acc ps' =>
      match acc with
      | none => some ps'
      | some cur => if checksOf ps'.2 < checksOf cur.2 then some ps' else some cur) none
  rel.ctors.foldl (fun b c =>
    match best (viablePlans rel key c limit) with
    | some (p, _) => b.set key c.ctorName p
    | none => b) {}

/-! ### Where a learned book departs from its start

    Learning starts from the deriver's own choice (`ofOrders` over `Schedules.chosenOrdersRef`) so that
    its *result* can be read as a list of disagreements with branch and bound: every entry below is a
    constructor where measurement overruled the static estimate. That list is the thing to inspect, and
    the thing to pin — pinning the whole learned book would also pin every constructor learning never
    touched, which only freezes the deriver's current choice for no measured reason. -/

/-- One constructor on which a learned book departs from the book it started from. -/
structure Change where
  /-- The mode. -/
  key : SpecKey
  /-- The constructor. -/
  ctorName : Name
  /-- The start book's plan, or `none` when it had no entry — the constructor started from the
      interpreter's default (`RelSpec.deriveModeIn`). -/
  start : Option Plan
  /-- The learned book's plan, or `none` when it has no entry. Learning only ever `set`s, so this is
      `none` only for books built some other way. -/
  learned : Option Plan
  deriving Repr, BEq, Inhabited

/-- Every constructor where `learned` differs from `start`, ordered by mode and constructor name so the
    report does not depend on the order entries were set in.

    Two plans that differ as lists but `repair` to the **same schedule** are not a change. They are not
    hypothetical: `ofOrders` records a bare premise order, while a plan that came out of `viablePlans`
    carries the forced `inst`s `repair` would have inserted anyway, so the same schedule can arrive
    spelled two ways — and reporting that as "dynamic analysis beat static" would be false. When either
    side fails to lower, or `specs` has no spec for the constructor, the plans are compared as written. -/
def diff (specs : List RelSpec) (start learned : PlanBook) : List Change :=
  let pairs := (learned.entries ++ start.entries).foldl (fun acc (k, cn, _) =>
    if acc.any (fun (k', cn') => k' == k && cn' == cn) then acc else acc ++ [(k, cn)])
    ([] : List (SpecKey × Name))
  let lowered := fun (k : SpecKey) (cn : Name) (p : Plan) =>
    (specs.find? (fun r => r.inductiveName == k.inductiveName)).bind (fun rel =>
      (rel.ctors.find? (fun c => c.ctorName == cn)).bind (fun c =>
        match repair rel k c p with
        | .ok (_, sched) => some sched
        | .error _ => none))
  let changes := pairs.filterMap (fun (k, cn) =>
    let a := start.find? k cn
    let b := learned.find? k cn
    let change : Change := { key := k, ctorName := cn, start := a, learned := b }
    if a == b then none
    else match a, b with
      | some pa, some pb =>
        match lowered k cn pa, lowered k cn pb with
        | some sa, some sb => if sa == sb then none else some change
        | _, _ => some change
      | _, _ => some change)
  changes.mergeSort (fun x y =>
    let kx := renderSpecKey x.key
    let ky := renderSpecKey y.key
    kx < ky || (kx == ky && toString x.ctorName ≤ toString y.ctorName))

/-- A plan as premise indices, `[2, 0, 1]`, with a generated variable written `x←`. The indices are what
    a pin table holds; `ppPlan` alongside says what they mean. -/
def renderIndices (plan : Plan) : String :=
  "[" ++ ", ".intercalate (plan.map (fun st => match st with
    | .use i => toString i
    | .inst v => s!"{v}←")) ++ "]"

/-- The diff as text: per constructor, the start order and the learned plan, each as indices and as the
    premises they name.

    A learned plan carrying an elective `inst` is flagged, because it is a measured improvement that no
    premise order can transfer (`unpinnableInsts`): it belongs in the report and cannot go in the pin
    table. -/
def renderDiff (specs : List RelSpec) (changes : List Change) : String :=
  if changes.isEmpty then "[plan-diff] the learned book agrees with the start book everywhere"
  else
    let lookup := fun (k : SpecKey) (cn : Name) =>
      (specs.find? (fun r => r.inductiveName == k.inductiveName)).bind (fun rel =>
        (rel.ctors.find? (fun c => c.ctorName == cn)).map (fun c => (rel, c)))
    let side := fun (label : String) (ch : Change) (p? : Option Plan) =>
      match p? with
      | none => s!"    {label} (no entry: the interpreter's default)"
      | some p =>
        match lookup ch.key ch.ctorName with
        | some (_, c) => s!"    {label} {renderIndices p}  {ppPlan c p}"
        | none => s!"    {label} {renderIndices p}  (no spec for this constructor)"
    let pinNote := fun (ch : Change) =>
      match ch.learned, lookup ch.key ch.ctorName with
      | some p, some (rel, c) =>
        match unpinnableInsts rel ch.key c p with
        | some vars => s!"\n    ! not pinnable: elective inst of {vars}"
        | none => ""
      | _, _ => ""
    let one := fun (ch : Change) =>
      s!"  {renderSpecKey ch.key} · {ch.ctorName}\n{side "start  " ch ch.start}\n\
        {side "learned" ch ch.learned}{pinNote ch}"
    s!"[plan-diff] {changes.length} constructor(s) where the learned book departs from the start \
      book:\n" ++ "\n".intercalate (changes.map one)

end PlanBook

/-- `RelSpec.deriveModeIn`, but taking a constructor's plan from `book` when the book names one.

    A booked plan is `repair`ed rather than trusted blindly, so a plan carried over from a different
    mode — where a variable that is now an input used to need generating — still lowers. -/
def RelSpec.deriveModeWith (rel : RelSpec) (env : InterpEnv) (key : SpecKey) (book : PlanBook)
    (limit : Nat := 24) (recFnName : Option Name := none) (derivable : List Name := []) :
    Except String RelSchedule :=
  let self := recFnName.getD rel.recFnName
  rel.deriveModeBy key (recFnName := recFnName) (choose := fun rel' c =>
    match book.find? key c.ctorName with
    | some plan =>
      -- The *repaired* plan is what was lowered, and so what provenance must name; the booked bare order
      -- can be missing the `inst`s repair inserted.
      match repairLowered rel' key c plan with
      | .ok (plan', low) => .ok (low.schedule, some (CtorProvenance.ofLowered c plan' low))
      | .error e =>
        .error s!"[interp] the booked plan for '{c.ctorName}' at {renderSpecKey key} does not \
          lower: {e.message}"
    | none =>
      let viable := viablePlansLowered rel' key c limit
      match (viable.find? (fun (_, l) => env.scheduleResolvable self derivable l.schedule)).orElse
          (fun _ => viable.head?) with
      | some (plan', low) => .ok (low.schedule, some (CtorProvenance.ofLowered c plan' low))
      | none =>
        let reason :=
          match (plansOf rel' key c limit).head? with
          | some (_, .error e) => e.message
          | _ => "no plan enumerated"
        .error s!"[interp] no viable schedule for '{c.ctorName}' at {renderSpecKey key}: {reason}")

/-- `InterpEnv.deriveClosure`, honouring a `PlanBook`.

    The book is what makes a closure-wide search possible: change one constructor's plan, rebuild the
    whole closure from it, and the modes that the change newly requires are brought up automatically.
    A plan that mints a new mode therefore costs nothing extra to try. -/
def InterpEnv.deriveClosureWith (env : InterpEnv) (specs : List RelSpec) (roots : List SpecKey)
    (book : PlanBook) (limit : Nat := 24) (fuel : Nat := 64)
    (deriveCheckers : Bool := false) : Except String InterpEnv := do
  let derivable := specs.map RelSpec.inductiveName
  -- A checker or enumerator root is built out of `Check` steps, so its closure cannot be found without
  -- following them.
  let deriveCheckers := deriveCheckers || roots.any (fun k => k.deriveSort != .Generator)
  let mut e := env
  -- Paired with the type arguments the asking call site supplied; see `RelSpec.instantiate`.
  let mut queue : List (SpecKey × List (Nat × ConstructorExpr)) := roots.map (·, [])
  -- Every mode ever queued. A relation's `depKeys` reports one entry per `SuchThat` step across every
  -- constructor, so a 76-constructor relation enqueues its own modes dozens of times over; without
  -- this the duplicates dominate, and `fuel` is spent on them rather than on derivations.
  let mut seen : Std.HashSet SpecKey := ∅
  let mut instantiatedAt : List (SpecKey × List (Nat × ConstructorExpr)) := []
  let mut budget := fuel
  while !queue.isEmpty do
    let (key, typeArgs) := queue.headD (default, [])
    queue := queue.tailD []
    if seen.contains key then
      match instantiatedAt.find? (fun p => p.1 == key) with
      | some (_, prior) =>
        if prior != typeArgs then
          throw s!"[interp] {renderSpecKey key} is needed at two different instantiations — \
            {prior.map (fun p => ppConstructorExpr p.2)} and {typeArgs.map (fun p => ppConstructorExpr p.2)}. One schedule cannot \
            serve both, and `SpecKey` does not carry the instantiation, so the modes cannot be told \
            apart. Split the relation, or extend `SpecKey` with its type arguments."
      | none => pure ()
      continue
    seen := seen.insert key
    if (e.relations[key]?).isSome || (e.producers[key]?).isSome then
      continue
    match specs.find? (fun r => r.inductiveName == key.inductiveName) with
    | none => continue
    | some rel₀ =>
      -- Fuel counts *derivations*, not queue pops, so the bound means what it says.
      if budget == 0 then
        throw s!"[interp] mode closure did not settle within {fuel} derivations; still wanted \
          {(queue.filter (fun (k, _) => !seen.contains k)).map (fun (k, _) => renderSpecKey k)}"
      budget := budget - 1
      let rel := rel₀.instantiate typeArgs
      instantiatedAt := instantiatedAt ++ [(key, typeArgs)]
      let derived ← rel.deriveModeWith e key book limit (recFnName := e.freshRecFnName rel key)
        (derivable := derivable)
      e := e.addRelation derived
      queue := queue ++ (derived.depKeysTyped deriveCheckers).filter (fun (k, _) => !seen.contains k)
  return e.linkMutualCalls specs

/-- The plan a constructor actually ended up with, recovered so a search can mutate it: the book's
    entry if there is one, otherwise the declared premise order repaired. -/
def PlanBook.planFor (b : PlanBook) (rel : RelSpec) (key : SpecKey) (c : CtorSpec) : Plan :=
  match b.find? key c.ctorName with
  | some p => p
  | none =>
    match (viablePlans rel key c).head? with
    | some (p, _) => p
    | none => (List.range c.hypotheses.length).map PlanStep.use

/-! ## Reporting -/

/-- A plan sweep as text: the schedule each ordering lowers to, or why it cannot. -/
def renderPlans (c : CtorSpec) (results : List (Plan × Except PlanError Schedule)) : String :=
  let one := fun (i : Nat) (p : Plan) (r : Except PlanError Schedule) =>
    let head := s!"#{i + 1}  {ppPlan c p}"
    match r with
    | .ok (steps, _) => s!"{head}\n{ppScheduleSteps steps}"
    | .error e => s!"{head}\n    ✗ {e.message}"
  let lines := results.zipIdx.map (fun ((p, r), i) => one i p r)
  s!"[interp] {c.ctorName}: {results.length} ordering(s)\n" ++ "\n\n".intercalate lines

end Specimen.Interp
