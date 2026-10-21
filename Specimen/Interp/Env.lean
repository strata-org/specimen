import Specimen.Interp.Value
import Specimen.Schedules
import Specimen.GeneratorCombinators
import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.EnumeratorCombinators

/-!
# The interpreter environment

A schedule is not self-contained: its steps refer to other relations (`Source.NonRec`), to
unconstrained generators for base types, to checkers, and to Lean functions. The compile-time
pipeline resolves all of those by elaboration and typeclass synthesis. The interpreter resolves
them by lookup in an `InterpEnv`, which is ordinary data you build at runtime.

An `InterpEnv` has two kinds of entries:

* **Relations you want to interpret** (`relations`): a `RelSchedule` per spec — the runtime
  counterpart of `Schedules.InductiveSchedule`. These are the schedules you are experimenting
  with; swap steps around, rebuild the map, re-run. No recompilation.
* **Leaves** (`arbitrary`, `producers`, `checkers`, `funcs`): everything the schedules bottom out
  at. Register these once. `Specimen.Interp.Bridge` lifts existing `Arbitrary`/`DecOpt` instances
  and ordinary Lean functions into these tables, so you can reuse whatever is already derived or
  hand-written.
-/

open Lean Plausible Schedules

namespace Specimen.Interp

/-- Weight assigned to a constructor's branch of the backtracking combinator.

    Deliberately the same shape as `Scoring.CtorWeightFn` (`abbrev`s are transparent), so the
    weight functions the real pipeline uses — `Scoring.defaultCtorWeight`,
    `Scoring.balancedCtorWeight`, and any you registered yourself — can be passed straight into
    an `InterpEnv`. Arguments, in order: constructor name, the spec's output indices, derive sort,
    score badness (per mille), whether the constructor is recursive, the current size, the number
    of base and recursive constructors, and the number of size-consuming calls in this
    constructor's schedule. -/
abbrev CtorWeightFn :=
  Name → List Nat → DeriveSort → Nat → Bool → Nat → Nat → Nat → Nat → Nat

/-- Replica of `Scoring.balancedCtorWeight`, the pipeline's default. Kept here so the interpreter
    does not have to depend on the (compile-time-only) scoring and schedule-search machinery;
    pass `Scoring.balancedCtorWeight` explicitly if you prefer to depend on the real one. -/
def balancedCtorWeight (_ctorName : Name) (_outputIndices : List Nat) (_deriveSort : DeriveSort)
    (scoreBadness : Nat) (isRec : Bool) (size : Nat) (_numBase numRec : Nat)
    (_numRecCalls : Nat) : Nat :=
  let quality :=
    if scoreBadness < 250 then 4
    else if scoreBadness < 500 then 3
    else if scoreBadness < 750 then 2
    else 1
  if isRec then
    if size == 0 then 0 else max 1 (size / max 1 numRec) * quality
  else quality * 4

/-- Replica of `Scoring.sizeProportionalCtorWeight` (the QuickChick strategy). -/
def sizeProportionalCtorWeight (_ctorName : Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (isRec : Bool) (size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  if isRec then size + 1 else 1

/-- Replica of `Scoring.flatCtorWeight`: every constructor is equally likely. -/
def flatCtorWeight (_ctorName : Name) (_outputIndices : List Nat) (_deriveSort : DeriveSort)
    (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat) (_numBase _numRec : Nat)
    (_numRecCalls : Nat) : Nat := 1

/-- One decision in a plan: schedule a premise, or generate a variable out of thin air.

    A plan must `use` every premise exactly once — a premise left out is a proof obligation left
    unmet, not an optimisation. `inst` steps are optional and are what let an ordering work that
    would otherwise be rejected: generating `x` unconstrained turns `Between lo x hi` from a producer
    into a check. -/
inductive PlanStep where
  /-- Schedule premise number `hypIdx` (an index into `CtorSpec.hypotheses`) next. -/
  | use (hypIdx : Nat)
  /-- Generate the variable `v` with an unconstrained generator next. -/
  | inst (v : Name)
  deriving Repr, BEq, Inhabited

/-- An ordering of a constructor's premises, interleaved with unconstrained generations. -/
abbrev Plan := List PlanStep

/-- Which plan a derived constructor schedule came from, and which plan step emitted each of its steps.

    Recorded **at the moment of lowering**, not reconstructed afterwards. Reconstructing it — re-lowering
    `PlanBook.planFor` — gets a different plan in three ordinary situations: a booked bare order that
    lowering *repaired* (every `PlanBook.ofOrders` entry with a forced `inst`); an unbooked constructor,
    whose installed plan is the first *resolvable* one rather than the first viable one; and an
    instantiated polymorphic mode, lowered from `RelSpec.instantiate`d spec. Blame attribution then either
    names the wrong premise or none, and the target is dropped. -/
structure CtorProvenance where
  ctorName : Name
  /-- The plan that was lowered — after `repair`, so including any `inst`s it inserted. -/
  plan : Plan
  /-- One entry per step of the installed schedule: the plan step that emitted it, `none` for the
      conclusion prologue. Stays aligned through `linkMutualCalls`, which rewrites steps one for one. -/
  origins : List (Option PlanStep)
  deriving Repr, Inhabited

/-- A relation's full derivation plan, at runtime: the interpreter's counterpart of
    `Schedules.InductiveSchedule` (which additionally carries compile-time-only search
    statistics). `RelSchedule.ofInductiveSchedule` converts one.

    `baseSchedules` are the non-recursive constructors' schedules (used at every size, and the
    only ones used at size 0); `recSchedules` are the recursive ones (used when size > 0). This
    split is what the emitted `match size with | 0 => … | size' + 1 => …` does. -/
structure RelSchedule where
  /-- Which relation, at which output mode, for which producer. -/
  key : SpecKey
  /-- The relation's argument names, in argument order — including the output positions. Inputs
      are bound to these names (at the positions *not* in `key.outputIndices`) when a schedule
      starts running. -/
  argNames : List Name
  /-- The name `Source.Rec`/`Source.MutRec` steps use to refer to this relation. -/
  recFnName : Name
  /-- Per-constructor schedules for the non-recursive constructors. -/
  baseSchedules : List (Name × Schedule)
  /-- Per-constructor schedules for the recursive constructors. -/
  recSchedules : List (Name × Schedule)
  /-- Per-constructor score badness in per mille (0 = best), as fed to the weight function.
      Constructors absent from this list score 0. -/
  badness : List (Name × Nat) := []
  /-- For derived schedules, where each constructor's schedule came from (`CtorProvenance`). Empty for a
      hand-registered or compiled schedule, which had no plan. -/
  provenance : List CtorProvenance := []
  /-- Positions in `argNames` that are type or instance arguments, and so carry no runtime value.
      The interpreter is untyped, so it neither consumes nor produces values at these positions:
      callers pass one `Val` per *value-level* input and get one back per value-level output.
      Empty for the usual case of a relation with no `Sort`-typed or class arguments.

      Honouring that is the *caller's* job, and it has to be done by position: `addRelation` records
      these per relation (`InterpEnv.typeArgIndicesOf`) so every call site can drop them with
      `valueArgsAt` before evaluating anything. See there for the dictionary that dropping by kind let
      through. -/
  typeArgIndices : List Nat := []

namespace RelSchedule

/-- Badness (per mille) recorded for a constructor; `0` if none was recorded. -/
def badnessOf (rel : RelSchedule) (ctorName : Name) : Nat :=
  (rel.badness.find? (fun p => p.1 == ctorName)).elim 0 Prod.snd

/-- Every constructor schedule, base ones first (the order the emitted backtracking list uses). -/
def allSchedules (rel : RelSchedule) : List (Name × Schedule) :=
  rel.baseSchedules ++ rel.recSchedules

/-- Value-level argument positions: every position except the type and instance arguments. -/
def valuePositions (rel : RelSchedule) : List Nat :=
  (List.range rel.argNames.length).filter (fun i => !rel.typeArgIndices.contains i)

/-- Value-level *output* positions, ascending — the order results are returned in. -/
def outputPositions (rel : RelSchedule) : List Nat :=
  rel.valuePositions.filter (fun i => rel.key.outputIndices.contains i)

/-- Value-level *input* positions, ascending — the order inputs must be supplied in. -/
def inputPositions (rel : RelSchedule) : List Nat :=
  rel.valuePositions.filter (fun i => !rel.key.outputIndices.contains i)

/-- The argument names at the input positions, in order. -/
def inputNames (rel : RelSchedule) : List Name :=
  rel.inputPositions.filterMap (fun i => rel.argNames[i]?)

/-- The constructor's own dispatch, read off the front of its schedule: the leading `Match` steps whose
    scrutinee is an *input*, as `(input index, pattern)`.

    At a mode where an argument is an input, each constructor's conclusion pins that argument to a
    shape — Cedar's `litInt` to `.int`, `varContext` to `.record ctx` — and the schedule opens by
    matching it. `backtrack` therefore finds the constructor that can produce a requested type by
    *entering about ten of them and letting each reject at its own first step*. Measured on Cedar's
    `HasType[0,4]`, `varContext` and `varAction` fail 1000‰ of the time and are entered ~94 times per 40
    root samples; ~30% of all absorbed failures across the run die in such a prologue.

    The scan stops at the first step that is not an input `Match`, because a later `Match` may scrutinise
    something an earlier producing step bound, and that cannot be evaluated before the branch runs.
    `schedulePrologue` emits every input `Match` before any of its equality checks for exactly this
    reason: a check in between would end the scan early. -/
def inputGuard (rel : RelSchedule) (steps : List ScheduleStep) : List (Nat × Pattern) :=
  let names := rel.inputNames
  let rec go (ss : List ScheduleStep) (acc : List (Nat × Pattern)) : List (Nat × Pattern) :=
    match ss with
    | .Match _ scrutinee pattern :: rest =>
      match names.findIdx? (fun n => n == scrutinee) with
      | some i => go rest (acc ++ [(i, pattern)])
      | none => acc
    | _ => acc
  go steps []

/-- Whether the inputs *could* satisfy a guard.

    Deliberately permissive: matched against empty bindings, so a pattern variable the real match would
    check against an already-bound variable binds instead. That only ever makes the guard say "possible"
    when the real match would refuse, never the reverse — so `false` genuinely implies the branch would
    have thrown at that step, which is what makes skipping it sound. Agreement *within* one pattern is
    still checked (`matchPattern` compares a repeat against the binding it made a moment earlier), and
    that is sound for the same reason: more bindings only ever add constraints. -/
def guardPasses (g : List (Nat × Pattern)) (inputs : List Val) : Bool :=
  g.all (fun (i, pattern) =>
    match inputs[i]? with
    | some v => (matchPattern pattern v ∅).isSome
    | none => true)

/-- `inputGuard` and `guardPasses` fused, with the input-name list supplied by the caller so it is
    computed once per entry to the mode rather than once per constructor.

    Short-circuits: the scan stops at the first step that is not an input `Match` (a later `Match` may
    scrutinise a variable a producing step bound, which cannot be evaluated before the branch runs), and
    returns `false` the moment a pattern cannot match. -/
def guardPassesWith (inNames : List Name) (steps : List ScheduleStep) (inputs : List Val) : Bool :=
  let rec go (ss : List ScheduleStep) : Bool :=
    match ss with
    | .Match _ scrutinee pattern :: rest =>
      match inNames.findIdx? (fun n => n == scrutinee) with
      | none => true
      | some i =>
        match inputs[i]? with
        | none => go rest
        | some v => if (matchPattern pattern v ∅).isSome then go rest else false
    | _ => true
  go steps

/-- Buckets the constructor schedules the way the emitted code does: a *base* constructor whose
    schedule contains a mutual-recursive call still consumes fuel, so it is treated as recursive
    (it moves into the recursive bucket and counts towards `numRec` in the weight function).
    Returns `(nonRecursive, recursive)`. -/
def bucketedSchedules (rel : RelSchedule) :
    List (Name × Schedule) × List (Name × Schedule) :=
  let (mutualBase, plainBase) :=
    rel.baseSchedules.partition (fun (_, (steps, _)) => scheduleUsesMutualCall steps)
  (plainBase, mutualBase ++ rel.recSchedules)

/-- `countSizeConsumingCalls` for one constructor.

    Named rather than inlined because this is the single hottest call in the interpreter:
    `interpRelSchedule` builds its whole `backtrack` list eagerly, so on Cedar's 76-constructor
    `HasType` this runs 76 times per entry to the mode, at every level of the recursion, whether or
    not any branch is tried. It is ~36% of a 130us entry.

    **Memoising it is a measured loss, so do not try again.** Caching per constructor in a
    `Std.HashMap Name Nat` (populated at `addRelation`) took the entry from 130us to 160us: hashing a
    long `Lean.Name` like `CedarGen.Relational.Lean.HasType.litInt` costs more than walking the three
    or four steps this counts. Caching `bucketedSchedules` alongside it sped that term up 16x in
    isolation (5201ns -> 330ns) yet moved the entry total by 1%, i.e. nothing. An earlier version using
    `getD` was worse still (210us), because `getD`'s default argument is evaluated eagerly — it did the
    work it meant to cache *and* the lookup.

    The lesson is that the cost is 76 small computations, and replacing each with a lookup of
    comparable cost cannot win. To actually remove it you have to hoist the whole loop — precompute
    one weight array per (mode, size) at install time — which needs the weight-staleness problem
    solved, since `withWeightBook` and `probeRecAt` both replace `weightFn` at runtime. -/
def numRecCallsOf (rel : RelSchedule) (_ctorName : Name) (steps : List ScheduleStep) : Nat :=
  countSizeConsumingCalls rel.key.inductiveName steps
/-- The same relation with only the named **recursive** constructors kept; every base constructor stays.

    For auditing whether each rule is *productive*. Weights can only make an unproductive rule rarer;
    they cannot make it work. But a rule's productivity is hard to see in the full generator, because
    `backtrack` silently substitutes another rule whenever one fails — so a rule that never succeeds is
    invisible in the aggregate.

    Keeping all the base cases and exactly one recursive rule isolates it: the base cases are what let
    recursion terminate, so the rule gets a fair chance, and anything the sample builds beyond base-case
    size had to come from that rule. `keep := []` gives the base-only reference to compare against.

    Bucketing follows `bucketedSchedules`: a *base* constructor that makes a mutual call still consumes
    size, so it counts as recursive here and is filtered with the rest. -/
def keepOnlyRec (rel : RelSchedule) (keep : List Name) : RelSchedule :=
  let (mutualBase, plainBase) :=
    rel.baseSchedules.partition (fun (_, (steps, _)) => scheduleUsesMutualCall steps)
  { rel with
    baseSchedules := plainBase ++ mutualBase.filter (fun (c, _) => keep.contains c)
    recSchedules := rel.recSchedules.filter (fun (c, _) => keep.contains c) }

/-- Converts a schedule derived at compile time into its runtime counterpart, so you can capture
    exactly what the derivation chose and then perturb it. -/
def ofInductiveSchedule (indSched : InductiveSchedule) (badness : List (Name × Nat) := [])
    (typeArgIndices : List Nat := []) : RelSchedule where
  key := indSched.key
  argNames := indSched.argNames
  recFnName := indSched.recFnName
  baseSchedules := indSched.baseSchedules
  recSchedules := indSched.recSchedules
  badness := badness
  typeArgIndices := typeArgIndices

/-- Replaces one constructor's schedule (in whichever bucket it lives), leaving the rest alone.
    The workhorse for "try this constructor a different way". -/
def withCtorSchedule (rel : RelSchedule) (ctorName : Name) (sched : Schedule) : RelSchedule :=
  let upd := List.map (fun (n, s) => if n == ctorName then (n, sched) else (n, s))
  -- The replacement did not come from the recorded plan, so its provenance no longer describes it.
  { rel with baseSchedules := upd rel.baseSchedules, recSchedules := upd rel.recSchedules,
             provenance := rel.provenance.filter (·.ctorName != ctorName) }

/-- Where a constructor's installed schedule came from, if it was derived. -/
def provenanceOf? (rel : RelSchedule) (ctorName : Name) : Option CtorProvenance :=
  rel.provenance.find? (·.ctorName == ctorName)

/-- The schedule currently used for a constructor, if it has one. -/
def ctorSchedule? (rel : RelSchedule) (ctorName : Name) : Option Schedule :=
  (rel.allSchedules.find? (fun p => p.1 == ctorName)).map Prod.snd

end RelSchedule

/-- An unconstrained producer for a base type, as the interpreter sees it: a `Gen` of untyped
    values. (The emitted code calls `Arbitrary.arbitrary`, which likewise takes no explicit size —
    it reads the size from the `Gen` monad.) -/
abbrev ValGen := Gen Val

/-- A constrained producer supplied as a leaf, taking `initSize`, `size`, and the relation's input
    arguments (in argument order, outputs omitted), and producing one value per output position
    (in ascending output-index order).

    Type and instance positions are dropped by position when some mode of the relation is interpreted
    (`InterpEnv.typeArgIndicesOf`) and only by kind otherwise, so a dictionary can still arrive: read
    the inputs from the end, as the leaf checkers do. -/
abbrev ValProducer := Nat → Nat → List Val → Gen (List Val)

/-- A checker supplied as a leaf, taking fuel and the relation's *value-level* arguments (type and
    instance arguments dropped — see `Specimen.Interp.valueArgs`). -/
abbrev ValChecker := Nat → List Val → Except GenError Bool

/-- An *enumerator* for a base type, as the interpreter sees it: every value of the type, lazily, at a
    size. `ExceptT` because an enumeration can run out of fuel partway.

    Enumerators are what checkers are built on. A checker for `∃ x, R a x` has to try candidate `x`s,
    and `convertDeriveSortToProducerSort` maps `Checker` to `Enumerator` for exactly that reason — so
    interpreting checkers is impossible without interpreting enumerators first. -/
abbrev ValEnum := ExceptT GenError Enumerator Val

/-- A constrained enumerator supplied as a leaf, taking `initSize`, `size`, and the relation's
    value-level inputs, and enumerating one tuple per solution. Stands in for an
    `EnumSizedSuchThat` instance. -/
abbrev ValEnumProducer := Nat → Nat → List Val → ExceptT GenError Enumerator (List Val)

/-- How a constructor divides its size budget among its recursive calls. -/
inductive SplitPolicy
  /-- One quotient `size'/k` to every call — what the emitted code does today. -/
  | equal
  /-- A composition of `size'` into `k` parts, drawn uniformly over compositions. -/
  | starsAndBars
  deriving Repr, BEq, Inhabited

/-- Everything the interpreter needs to run a schedule: the schedules under experiment, plus
    interpretations for every leaf they bottom out at. Build one with `∅`-style record syntax and
    the `add*` helpers, or with `InterpEnv.ofRelations`. -/
structure InterpEnv where
  /-- Schedules to interpret, keyed by spec. -/
  relations : Std.HashMap SpecKey RelSchedule := ∅
  /-- Maps a relation's `recFnName` to its key, so `Source.Rec`/`Source.MutRec` steps (which name
      the recursive function, not the relation) can be resolved. Maintained by `addRelation`. -/
  byFn : Std.HashMap Name SpecKey := ∅
  /-- Each interpreted relation's type and instance positions (`RelSchedule.typeArgIndices`), by
      relation name, for the call sites that must drop them (`typeArgIndicesOf`). Maintained by
      `addRelation`, which records only non-empty lists, so a monomorphic development leaves it empty.

      Keyed by name rather than read off the callee's `RelSchedule` because the positions belong to the
      inductive's signature, not to a mode: every mode, sort and instantiation of a relation shares them.
      One lookup therefore serves a producer call, a check, and a leaf answering a mode nothing
      interprets, and it needs no callee key resolved first. -/
  typeArgIndicesByRel : Std.HashMap Name (List Nat) := ∅
  /-- Unconstrained producers, keyed by the *head* name of the type being produced (`Nat`,
      `List`, …). Convenient, but every instantiation of a polymorphic type shares one key. -/
  arbitrary : Std.HashMap Name ValGen := ∅
  /-- Unconstrained producers keyed by the type's rendered form (`"List Nat"`), consulted before
      `arbitrary`. Use this to distinguish instantiations of a polymorphic type; `InterpEnv.check`
      reports the exact string to register under. -/
  arbitraryAt : Std.HashMap String ValGen := ∅
  /-- Constrained producers for specs we do not have a schedule for, keyed by spec. -/
  producers : Std.HashMap SpecKey ValProducer := ∅
  /-- Checkers for relations we do not interpret, keyed by relation name. Consulted only after an
      interpreted `Checker`-sort schedule, so registering one is an override, not a requirement. -/
  checkers : Std.HashMap Name ValChecker := ∅
  /-- Unconstrained enumerators, keyed by the *head* name of the type enumerated. The enumerator
      counterpart of `arbitrary`. -/
  enums : Std.HashMap Name ValEnum := ∅
  /-- Unconstrained enumerators keyed by the type's rendered form, consulted before `enums`. -/
  enumsAt : Std.HashMap String ValEnum := ∅
  /-- Constrained enumerators for specs we do not interpret, keyed by spec. -/
  enumProducers : Std.HashMap SpecKey ValEnumProducer := ∅
  /-- Interpretations of the Lean functions appearing in `FuncApp` position. -/
  funcs : FuncTable := ∅
  /-- Weight function for the backtracking combinator; defaults to the pipeline's default. -/
  weightFn : CtorWeightFn := balancedCtorWeight
  /-- How a constructor's size budget is divided among its recursive calls.

  `.equal` is what the emitted code does (`MExp.lean:558-560`): one quotient `size'/k` handed to every
  recursive call, identical for all of them. `.starsAndBars` draws a composition of `size'` into `k`
  parts uniformly, so a call can get more than its share and unbalanced shapes become reachable without
  inflating the total. See `Specimen/Interp/Gen.lean`'s `drawSplit`. -/
  splitPolicy : SplitPolicy := .equal
  /-- Record *why* a mode's attempt failed when every constructor was refused on its inputs alone, so blame
      can go up to the caller that chose those inputs (`Interp.Blame`). Changes no draw and no outcome —
      only which definitive error a wholly-refused mode throws — and costs a dataflow pass per failing
      branch, so it is off unless a measurement asks for it. -/
  attributeNoApply : Bool := false
  /-- Per-constructor **floor** for `.starsAndBars`, in per-mille of the equal share: each recursive call
  is first guaranteed `floor/1000 · size'/k`, and only the remainder is split at random. `0` (the default,
  and any constructor absent from the map) is plain stars-and-bars; `1000` is the equal split with its
  remainder placed at random. Ignored under `.equal`.

  This is the tuned knob, not a computed minimum: a static minimum size is almost always 0 (any base case
  makes it so) while a call can still starve on the inputs it actually receives, so the floor is learned
  against discards instead. -/
  splitFloor : Std.HashMap Name Nat := ∅
  /-- Per-constructor, per-**premise** minimum sizes: `(premise index, size)` pairs. A recursive call
  emitted by a listed premise is guaranteed that size first, as far as the budget reaches, and the rest
  is split by `splitPolicy` as usual. Absent constructors and premises get no minimum.

  `splitFloor` treats every call of a constructor alike, which cannot say that one operand needs more
  than another. Cedar's `binaryAppContains` is the case in point: its set operand needs size ≥ 2 (a set
  literal and an element) while the other operand can be a literal at size 0, so under an even split the
  set operand starves whenever the constructor is entered below size 5 — about 80% of its attempts. -/
  premiseFloor : Std.HashMap Name (List (Nat × Nat)) := ∅
  /-- Termination fuel, matching the `specimen.fuel` option used by the derived code. -/
  fuel : Nat := 10000
  /-- Whether to test each constructor's `inputGuard` before entering its branch, skipping the ones
      whose first step provably cannot match the inputs.

      Off by default because it is **distribution-preserving but not seed-preserving**: removing a
      certainly-failing branch leaves the conditional distribution over *successful* branches exactly as
      it was — `backtrack` would have retried past it anyway — but it changes which `Gen.choose` draws
      happen, so the same seed no longer yields the same value. That breaks the paired comparisons the
      tuning loops rely on, so it must be opted into rather than silently altering every measurement. -/
  dispatchInputs : Bool := false

namespace InterpEnv

/-- Registers a relation's schedule, keeping the `recFnName` index and the per-relation type positions
    in sync. -/
def addRelation (env : InterpEnv) (rel : RelSchedule) : InterpEnv :=
  { env with
    relations := env.relations.insert rel.key rel
    byFn := env.byFn.insert rel.recFnName rel.key
    typeArgIndicesByRel :=
      if rel.typeArgIndices.isEmpty then env.typeArgIndicesByRel
      else env.typeArgIndicesByRel.insert rel.key.inductiveName rel.typeArgIndices }

/-- An environment holding just these relations (leaves still need registering). -/
def ofRelations (rels : List RelSchedule) : InterpEnv :=
  rels.foldl addRelation {}

/-- Registers an unconstrained producer for every type whose head is `tyName`. -/
def addArbitrary (env : InterpEnv) (tyName : Name) (g : ValGen) : InterpEnv :=
  { env with arbitrary := env.arbitrary.insert tyName g }

/-- Registers an unconstrained producer for one specific type, named by its rendered form
    (e.g. `"List Nat"`). Takes precedence over `addArbitrary` for that exact type. -/
def addArbitraryAt (env : InterpEnv) (renderedTy : String) (g : ValGen) : InterpEnv :=
  { env with arbitraryAt := env.arbitraryAt.insert renderedTy g }

/-- The unconstrained producer for the type an `Unconstrained` step names: the precise
    `arbitraryAt` entry if there is one, otherwise the head-name entry. -/
def lookupArbitrary (env : InterpEnv) (hyp : HypothesisExpr) : Option ValGen :=
  match env.arbitraryAt[ppHypothesisExpr hyp]? with
  | some g => some g
  | none => env.arbitrary[hyp.1]?

/-- Registers a constrained producer for a spec the interpreter should *not* interpret. -/
def addProducer (env : InterpEnv) (key : SpecKey) (p : ValProducer) : InterpEnv :=
  { env with producers := env.producers.insert key p }

/-- Registers a checker for the relation named `relName`. -/
def addChecker (env : InterpEnv) (relName : Name) (c : ValChecker) : InterpEnv :=
  { env with checkers := env.checkers.insert relName c }

/-- Registers an enumerator for every type whose head is `tyName`. -/
def addEnum (env : InterpEnv) (tyName : Name) (e : ValEnum) : InterpEnv :=
  { env with enums := env.enums.insert tyName e }

/-- Registers an enumerator for one specific type, named by its rendered form. -/
def addEnumAt (env : InterpEnv) (renderedTy : String) (e : ValEnum) : InterpEnv :=
  { env with enumsAt := env.enumsAt.insert renderedTy e }

/-- Registers a constrained enumerator for a spec the interpreter should not interpret. -/
def addEnumProducer (env : InterpEnv) (key : SpecKey) (e : ValEnumProducer) : InterpEnv :=
  { env with enumProducers := env.enumProducers.insert key e }

/-- The enumerator for the type an `Unconstrained` step names, precise entry first. -/
def lookupEnum (env : InterpEnv) (hyp : HypothesisExpr) : Option ValEnum :=
  match env.enumsAt[ppHypothesisExpr hyp]? with
  | some e => some e
  | none => env.enums[hyp.1]?

/-- Registers an interpretation for a function appearing in `FuncApp` position. -/
def addFunc (env : InterpEnv) (fnName : Name) (f : List Val → Except String Val) : InterpEnv :=
  { env with funcs := env.funcs.insert fnName f }

/-- The spec a `Source.Rec`/`Source.MutRec` function name refers to. -/
def keyOfFn? (env : InterpEnv) (fnName : Name) : Option SpecKey :=
  env.byFn[fnName]?

/-- The argument positions of `relName` that carry no runtime value, as its interpreted modes recorded
    them; `[]` when none did, which leaves `valueArgsAt` dropping by kind alone — the right fallback for
    a relation only leaves answer, since leaves read their arguments from the end.

    The emptiness test comes first so that a development with no polymorphic relation pays nothing per
    step for this. -/
def typeArgIndicesOf (env : InterpEnv) (relName : Name) : List Nat :=
  if env.typeArgIndicesByRel.isEmpty then []
  else
    match env.typeArgIndicesByRel[relName]? with
    | some idxs => idxs
    | none => []

/-- Replaces one relation's schedule wholesale. -/
def withRelation (env : InterpEnv) (rel : RelSchedule) : InterpEnv :=
  env.addRelation rel

/-- Replaces one constructor's schedule within one relation, if both exist. Returns `none` when
    the spec is not registered, so a typo in an experiment script is not silently ignored. -/
def withCtorSchedule (env : InterpEnv) (key : SpecKey) (ctorName : Name) (sched : Schedule) :
    Option InterpEnv :=
  match env.relations[key]? with
  | none => none
  | some rel => some (env.addRelation (rel.withCtorSchedule ctorName sched))

end InterpEnv

/-- Restricts **every mode** of `relName` to the named recursive constructors, keeping all base ones.

    Applied per mode rather than to one, because a relation's recursion runs through several of its own
    modes: leaving `HasType[3,4]` unrestricted while restricting `HasType[0,3,4]` would let the rule under
    audit recurse through a mode that still has all 76 alternatives available. Sibling *relations* are
    left alone, so the surrounding machinery still works and what is isolated is this relation's rules. -/
def InterpEnv.isolateRec (env : InterpEnv) (relName : Name) (keep : List Name) : InterpEnv :=
  { env with relations := env.relations.fold (fun acc key rel =>
      acc.insert key (if key.inductiveName == relName then rel.keepOnlyRec keep else rel)) ∅ }

/-- Restricts **one mode** to the named recursive constructors, leaving every other mode intact.

    The honest way to ask "is this rule productive". Restricting the whole relation (`isolateRec`) also
    removes the rules a rule *depends on*: measured on Cedar, `HasType`'s base cases cannot even build a
    `bool` expression, so base-plus-one-rule produced **nothing at all** for 61 of 67 rules — which says
    the rule set is highly interdependent, not that the rules are useless.

    Restricting only the mode invoked at the root asks the question that has an answer: *forced to use
    rule R at the top, with the rest of the generator available underneath, does the generator succeed —
    and what does it build?* -/
def InterpEnv.isolateRecAt (env : InterpEnv) (key : SpecKey) (keep : List Name) : InterpEnv :=
  match env.relations[key]? with
  | none => env
  | some rel => { env with relations := env.relations.insert key (rel.keepOnlyRec keep) }

/-- Adds a **probe** mode: the named rules only at the entry point, the *full* generator underneath.

    This is what isolating a rule actually requires. `isolateRecAt` is not enough, because a rule's own
    recursive call (`⟳ aux_hasType …`) resolves through `byFn` back to the mode being restricted — so the
    sub-generation is restricted too, and every rule that needs a sub-expression it cannot build itself
    reports zero successes. Measured on Cedar that was 61 of 67 rules, identically to the whole-relation
    restriction, which is the tell that the restriction was leaking downwards.

    The probe is registered under a fresh key and a fresh `recFnName`, but its schedules are copied
    unchanged — so the `recFnName` their steps *name* is still the original's, and `byFn` still resolves
    that to the unrestricted mode. Entry is restricted; recursion is not.

    Returns the probe's key, which is what to sample. -/
def InterpEnv.probeRecAt (env : InterpEnv) (key : SpecKey) (keep : List Name)
    (boost : Nat := 1) : InterpEnv × SpecKey :=
  match env.relations[key]? with
  | none => (env, key)
  | some rel =>
    let probeKey := { key with typeArgs := key.typeArgs ++ ["probe"] }
    let probe := { rel.keepOnlyRec keep with
                   key := probeKey
                   recFnName := rel.recFnName.appendAfter "_probe" }
    -- `boost` multiplies the kept constructors' weights, because restricting the *set* of
    -- constructors is not the same as making the survivor run. Measured on Cedar's `unaryAppIsTrue`,
    -- the probe used the rule in 6 of 60 samples and answered the rest from the base cases — so
    -- ~90% of the measurement described constructors the plan under test does not touch. That
    -- dilutes an effect rather than hiding it (orderings still measured 3.3–4.5x apart), but it
    -- understates every magnitude, and with coverage as the target an unfired rule contributes no
    -- k-paths at all. `1` leaves the weights alone, which is the previous behaviour.
    let base := env.weightFn
    let weightFn : CtorWeightFn := fun ctor outIdxs sort badness isRec size' numBase numRec numRecCalls =>
      let w := base ctor outIdxs sort badness isRec size' numBase numRec numRecCalls
      if boost > 1 && keep.contains ctor then w * boost else w
    -- Inserted directly rather than via `addRelation`: registering the fresh `recFnName` in `byFn` is
    -- unnecessary (nothing calls it) and inserting the *original* name would redirect real self-calls.
    ({ env with relations := env.relations.insert probeKey probe,
                weightFn := weightFn }, probeKey)

/-- Relations the interpreter handles structurally rather than by table lookup: equality and
    disequality, mirroring the built-in `DecOpt`/`ArbitrarySizedSuchThat` instances that the
    compile-time pipeline relies on for these. -/
def builtinRelations : List Name := [``Eq, ``Ne]

/-- The type-level arguments a premise applies its relation to, **with their argument positions**.

    Positions rather than a bare list, because the list is not contiguous: a type position whose argument
    reified as a `Hole` — the *caller* is polymorphic there too — carries nothing to substitute and is
    left out. `RelSpec.instantiate` aligns these positions against the callee's conclusion directly. -/
def typeArgsOf (hyp : HypothesisExpr) : List (Nat × ConstructorExpr) :=
  hyp.2.zipIdx.filterMap fun (a, i) =>
    match a with
    | .TyCtor .. => some (i, a)
    | _ => none

/-- Those arguments rendered, which is what `SpecKey.typeArgs` records. The position is part of the
    rendering so two instantiations that differ only in *which* parameter is concrete stay distinct. -/
def renderedTypeArgs (hyp : HypothesisExpr) : List String :=
  (typeArgsOf hyp).map fun (i, a) => s!"{i}:{ppConstructorExpr a}"

/-- Renders a `SpecKey` compactly, e.g. `BST[1,2] as Generator`, with the instantiation when there is
    one. Used throughout diagnostics. -/
def renderSpecKey (key : SpecKey) : String :=
  let sort :=
    match key.deriveSort with
    | .Generator => "Generator"
    | .Enumerator => "Enumerator"
    | .Checker => "Checker"
    | .Theorem => "Theorem"
  let idxs := ",".intercalate (key.outputIndices.map toString)
  -- The instantiation, when there is one: two modes of a polymorphic relation are different generators
  -- and every report has to be able to tell them apart.
  let tys := if key.typeArgs.isEmpty then "" else "@(" ++ ", ".intercalate key.typeArgs ++ ")"
  s!"{key.inductiveName}[{idxs}]{tys} as {sort}"

end Specimen.Interp
