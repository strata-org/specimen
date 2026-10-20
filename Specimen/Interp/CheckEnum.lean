import Specimen.Interp.Gen

/-!
# Interpreting checker and enumerator schedules

`Specimen.Interp.Gen` interprets generators. That covers one of the three sorts a schedule can have,
and on a real relation family it is not enough: a reordering that demotes a premise to a `Check` needs
a *checker* for that relation, and Cedar's `HasType` closure asks for 25 of them. Registering those by
hand defeats the point — the same completeness argument that motivated scheduling at runtime applies to
the other two sorts.

## Why the two sorts are one module

They are mutually recursive, and not incidentally. A checker for `∃ x, R a x` cannot decide anything
without trying candidate `x`s, so it *enumerates* them —
`DeriveSchedules.convertDeriveSortToProducerSort` maps `Checker` to `Enumerator` for exactly that
reason. An enumerator in turn contains `Check` steps, which call checkers. So checker → enumerator →
checker, and splitting them across modules would need a forward reference.

## The three monads, and what "failure" means in each

The interesting part is that failure means something different in each sort, and the emitted code says
so precisely. Getting this backwards would silently convert refutations into "don't know", which is the
difference between a checker that decides and one that never does.

| | Generator | Enumerator | Checker |
| --- | --- | --- | --- |
| monad | `Gen` | `ExceptT GenError Enumerator` | `Except GenError Bool` |
| alternatives | `backtrack` (weighted) | `enumerate` — concatenation, **unweighted** | `DecOpt.checkerBacktrack` |
| failed `Check`/`Match` | `throw genericFailure` | `throw genericFailure` (`MExp.lean:296,326`) | **`.ok false`** (`MExp.lean:298`) |
| size handed to sub-producers | `sizeExpr` | `sizeExpr` | **`initSize`** always (`MExp.lean:354`) |

Weights simply do not apply below the generator: `EnumeratorCombinators.enumerate` is
`enumerateAll`, which concatenates its alternatives and consults no weight function. So
`InterpEnv.weightFn`, per-constructor badness, and the size-shaping half of
`Specimen.Interp.Learn` are generator-only by construction, not by omission.

## Refutation versus ignorance

`EnumeratorCombinators.lazyListBacktrackOpt` is where the distinction is enforced, and it turns on the
*kind* of error in the enumeration:

```lean
| .error e =>
  let poisoned := if isInconclusiveError e then true else anyNone
  lazyListBacktrackOpt xs.get f poisoned
```

An out-of-fuel error poisons the result, so the enclosing checker answers "don't know". Any *other*
error — a `genericFailure` from a failed check, or one of this interpreter's
`[interp:reject:<step>]` labels — is simply skipped, and if no candidate succeeds the checker
answers `.ok false`. That is what lets a definite refutation stay definite, and it means discard
attribution composes with checker semantics for free.
-/

open Lean Plausible Schedules GeneratorCombinators EnumeratorCombinators

namespace Specimen.Interp

/-- Whether an error means "inconclusive" for the purposes of enumeration.

    Only exhaustion counts. A failed check, a non-matching pattern, and an `[interp]`
    misconfiguration are all *definite* about the branch they killed, so they must not poison a
    checker's verdict into "don't know". An exhausted retry loop
    (`"Gen.runUntil: Out of attempts"`) determined nothing, so it *does* count: omitting it reports an
    exhausted loop as a definite refutation.

    Shared with `EnumeratorCombinators.isInconclusiveError` and the generator path, so all three
    producer sorts classify errors identically. -/
def isEnumInconclusive : GenError → Bool := Gen.GenError.isInconclusive

/-- Folds a checker's verdicts, mirroring `DecOpt.andOpt`: the first non-`true` answer wins, so an
    inconclusive premise makes the whole conjunction inconclusive rather than false. -/
def andVerdict (a b : Except GenError Bool) : Except GenError Bool :=
  match a with
  | .ok true => b
  | _ => a

/-- Walks an enumeration, applying `f` to each value, exactly as
    `EnumeratorCombinators.lazyListBacktrackOpt` does — including the error discrimination that keeps a
    refutation definite. Reimplemented rather than called so the traversal can be shared by both
    entry points below and stay visibly aligned with the table in this module's docstring. -/
partial def backtrackEnum {α : Type} (l : LazyList (Except GenError α))
    (f : α → Except GenError Bool) (anyInconclusive : Bool) : Except GenError Bool :=
  match l with
  | .lnil =>
    if anyInconclusive then .error (.genError "Specimen: out of fuel (termination limit reached)")
    else .ok false
  | .lcons hd tl =>
    match hd with
    | .ok x =>
      match f x with
      | .ok true => .ok true
      | .ok false => backtrackEnum tl.get f anyInconclusive
      -- Misconfiguration is not a verdict on this candidate; pass it on (see `checkerBacktrackInterp`).
      | .error e => if isInterpError e then .error e
        -- The candidate itself was inconclusive, so the negative answer is not trustworthy.
        else backtrackEnum tl.get f true
    | .error e =>
      if isInterpError e then .error e
      else backtrackEnum tl.get f (if isEnumInconclusive e then true else anyInconclusive)

/-- Fails an enumeration definitively: a one-element enumeration holding a non-inconclusive error, so
    `backtrackEnum` skips the branch without poisoning the verdict. This is what the emitted code's
    `throw Gen.genericFailure` amounts to in `ExceptT GenError Enumerator`. -/
def enumReject {α : Type} (e : GenError) : ExceptT GenError Enumerator α :=
  fun _ => LazyList.lcons (.error e) ⟨fun _ => .lnil⟩

/-- An enumeration of exactly one value. -/
def enumPure {α : Type} (a : α) : ExceptT GenError Enumerator α :=
  fun _ => LazyList.lcons (.ok a) ⟨fun _ => .lnil⟩

/-- `DecOpt.checkerBacktrack`, except that interpreter misconfiguration is returned as it is.

    `checkerBacktrack` reads *any* error from a constructor as "inconclusive" and, at the end, replaces
    it with its own generic message. For an emitted checker that is right. For the interpreter it turned
    an internal failure — a leaf that cannot read its arguments, an arity mismatch — into an honest-looking
    "cannot decide", and lost the message that said what was wrong. Otherwise identical, and separate so
    that emitted checkers, which share `checkerBacktrack`, are untouched. -/
def checkerBacktrackInterp (checkers : List (Unit → Except GenError Bool)) : Except GenError Bool :=
  go checkers false
where
  go : List (Unit → Except GenError Bool) → Bool → Except GenError Bool
    | c :: cs, anyErr =>
      match c () with
      | .ok true => .ok true
      | .ok false => go cs anyErr
      | .error e => if isInterpError e then .error e else go cs true
    | [], anyErr => if anyErr then .error (.genError "DecOpt.checkerBacktrack failure.") else .ok false

mutual

-- ## Enumerators

/-- Enumerates every solution of a spec at `(fuel, initSize, size)` on its value-level inputs.

    Prefers an interpreted `Enumerator`-sort schedule, then a registered `ValEnumProducer` leaf. -/
partial def interpEnumRel (env : InterpEnv) (key : SpecKey) (fuel initSize size : Nat)
    (inputs : List Val) : ExceptT GenError Enumerator (List Val) :=
  match env.relations[key]? with
  | some rel =>
    if rel.key.deriveSort == .Enumerator then
      interpEnumRelSchedule env rel fuel initSize size inputs
    else
      enumReject (interpError s!"{renderSpecKey key} is registered as a \
        {repr rel.key.deriveSort}, not an Enumerator")
  | none =>
    match env.enumProducers[key]? with
    | some p => p initSize size inputs
    | none =>
      enumReject (interpError s!"no enumerator registered for {renderSpecKey key} (add an \
        `Enumerator`-sort schedule with `InterpEnv.addRelation`, or a leaf with \
        `InterpEnv.addEnumProducer`)")

/-- The body of an emitted `aux_enum`: match on fuel, then on size, then concatenate the constructors
    admissible at that size.

    Unweighted, unlike the generator: `EnumeratorCombinators.enumerate` is plain concatenation, so an
    enumerator visits every constructor and no weight function is consulted. -/
partial def interpEnumRelSchedule (env : InterpEnv) (rel : RelSchedule) (fuel initSize size : Nat)
    (inputs : List Val) : ExceptT GenError Enumerator (List Val) :=
  match fuel with
  | 0 => enumReject Gen.outOfFuelError
  | fuel' + 1 =>
    let (baseScheds, recScheds) := rel.bucketedSchedules
    let branch := fun (size' : Nat) (p : Name × Schedule) =>
      runEnumCtor env rel fuel' initSize size' inputs p.2
    -- At size 0 a relation with recursive constructors gets a final out-of-fuel branch, exactly as the
    -- emitted code does (`baseProducersWithFailsafe` in `DeriveConstrainedProducer.lean`): the budget
    -- ran out before those constructors could be tried, so what is missing is *undetermined*, not absent.
    let failsafe : List (ExceptT GenError Enumerator (List Val)) :=
      if recScheds.isEmpty then [] else [enumReject Gen.outOfFuelError]
    match size with
    | 0 => enumerate (baseScheds.map (branch 0) ++ failsafe)
    | size' + 1 => enumerate (baseScheds.map (branch size') ++ recScheds.map (branch size'))

/-- Runs one constructor's schedule as an enumeration: bind inputs, split the size budget, walk. -/
partial def runEnumCtor (env : InterpEnv) (rel : RelSchedule) (fuel' initSize size' : Nat)
    (inputs : List Val) (sched : Schedule) : ExceptT GenError Enumerator (List Val) :=
  let (steps, sort) := sched
  let numRecCalls := countSizeConsumingCalls rel.key.inductiveName steps
  let sizeExpr := if numRecCalls ≤ 1 then size' else size' / numRecCalls
  match rel.bindInputs inputs with
  | .error e => enumReject (interpError e)
  | .ok bindings => runEnumSteps env rel fuel' initSize sizeExpr bindings steps sort

/-- Executes the remaining steps of an enumerator schedule, then the epilogue.

    A failed `Check` or a non-matching `Match` becomes `enumReject Gen.genericFailure`, matching the
    emitted `throw Gen.genericFailure` — definite about this branch, and so skipped rather than
    poisoning any enclosing checker. -/
partial def runEnumSteps (env : InterpEnv) (rel : RelSchedule) (fuel' initSize sizeExpr : Nat)
    (bindings : ValEnv) (steps : List ScheduleStep) (sort : ScheduleSort) :
    ExceptT GenError Enumerator (List Val) :=
  match steps with
  | [] =>
    match sort with
    | .ProducerSchedule _ outputs =>
      match outputs.mapM (evalConstructorExpr env.funcs bindings) with
      | .ok vals => enumPure vals
      | .error e => enumReject (interpError e)
    | .CheckerSchedule => enumPure []
    | .TheoremSchedule .. =>
      enumReject (interpError "theorem schedule reached in enumerator position")
  | step :: rest =>
    let continueWith := fun (bindings' : ValEnv) =>
      runEnumSteps env rel fuel' initSize sizeExpr bindings' rest sort
    match step with
    | .Unconstrained v src _ =>
      match src with
      | .NonRec hyp =>
        match env.lookupEnum hyp with
        | some e => bind e (fun val => continueWith (bindings.insert v val))
        | none =>
          enumReject (interpError s!"no enumerator registered for type \
            `{ppHypothesisExpr hyp}` (needed to enumerate '{v}'; register one with \
            `InterpEnv.addEnum {hyp.1}`)")
      | .Rec f args | .MutRec f args =>
        bind (interpEnumCall env f args fuel' initSize sizeExpr bindings)
          (fun outs => continueWith (bindings.insert v (collapseOutputs outs)))
    | .SuchThat varsTys src _ =>
      let vars := varsTys.map Prod.fst
      match src with
      | .NonRec hypExpr =>
        bind (interpEnumConstrained env rel hypExpr vars initSize sizeExpr bindings)
          (fun outs =>
            match bindVars (outs.map Prod.fst) (outs.map Prod.snd) bindings with
            | .ok bindings' => continueWith bindings'
            | .error e => enumReject (interpError e))
      | .Rec f args | .MutRec f args =>
        bind (interpEnumCall env f args fuel' initSize sizeExpr bindings)
          (fun outs =>
            match bindVars vars outs bindings with
            | .ok bindings' => continueWith bindings'
            | .error e => enumReject (interpError e))
    | .Check src polarity =>
      match checkSourceIn env rel.key fuel' initSize sizeExpr bindings src with
      | .error e => enumReject (interpError e)
      | .ok verdict =>
        match (if polarity then verdict else DecOpt.negOpt verdict) with
        | .ok true => continueWith bindings
        -- Definite refutation and inconclusive are both `throw` here, but with *different* errors, so
        -- the enclosing checker can still tell them apart.
        | .ok false => enumReject Gen.genericFailure
        | .error e => enumReject e
    | .Match _ scrutinee pattern =>
      match bindings[scrutinee]? with
      | none =>
        enumReject (interpError s!"match scrutinee '{scrutinee}' is unbound at this point")
      | some v =>
        match matchPattern pattern v bindings with
        | some bindings' => continueWith bindings'
        | none => enumReject Gen.genericFailure

/-- A recursive or mutual enumerator call: threads the decremented fuel and the split size. -/
partial def interpEnumCall (env : InterpEnv) (f : Name) (args : List ConstructorExpr)
    (fuel' initSize sizeExpr : Nat) (bindings : ValEnv) :
    ExceptT GenError Enumerator (List Val) :=
  match env.keyOfFn? f with
  | none =>
    enumReject (interpError s!"no relation registered under the enumerator function name '{f}'")
  | some key =>
    match (valueArgs args).mapM (evalConstructorExpr env.funcs bindings) with
    | .error e => enumReject (interpError e)
    | .ok vals => interpEnumRel env key fuel' initSize sizeExpr vals

/-- A constrained enumerator for a premise about another spec (or another mode of this one), i.e. the
    emitted `EnumSizedSuchThat.enumSizedST`. -/
partial def interpEnumConstrained (env : InterpEnv) (rel : RelSchedule) (hypExpr : HypothesisExpr)
    (vars : List Name) (initSize sizeExpr : Nat) (bindings : ValEnv) :
    ExceptT GenError Enumerator (List (Name × Val)) :=
  let (relName, args) := hypExpr
  match splitHypothesis env.funcs bindings vars args (env.typeArgIndicesOf relName) with
  | .error e => enumReject (interpError e)
  | .ok (outputs, inputs) =>
    if relName == ``Eq then
      match outputs, lastArgs 1 inputs with
      | [(_, u)], [v] => enumPure [(u, v)]
      | _, _ =>
        enumReject (interpError s!"cannot solve `{ppHypothesisExpr hypExpr}` for {vars}: the \
          built-in equality enumerator needs exactly one unknown side and one known side")
    else
      let s := if relName == rel.key.inductiveName then sizeExpr else initSize
      -- See the note in `Gen.interpConstrained`: the instantiation is part of the key.
      let key : SpecKey :=
        { inductiveName := relName, outputIndices := outputs.map Prod.fst,
          deriveSort := .Enumerator, typeArgs := renderedTypeArgs hypExpr }
      bind (interpEnumRel env key env.fuel s s inputs) (fun vals =>
        if vals.length != outputs.length then
          enumReject (interpError s!"{renderSpecKey key} returned {vals.length} value(s) but \
            `{ppHypothesisExpr hypExpr}` expects {outputs.length}")
        else enumPure ((outputs.map Prod.snd).zip vals))

-- ## Checkers

/-- Decides a spec at `(fuel, size)` on *all* of its arguments — a checker mode has no outputs.

    Prefers an interpreted `Checker`-sort schedule, then a registered `ValChecker` leaf, so a
    hand-registered checker is an override rather than a requirement. -/
partial def interpChecker (env : InterpEnv) (key : SpecKey) (fuel size : Nat) (inputs : List Val)
    (initSize : Nat := size) : Except GenError Bool :=
  match env.relations[key]? with
  | some rel =>
    if rel.key.deriveSort == .Checker then interpCheckerSchedule env rel fuel initSize size inputs
    else .error (interpError s!"{renderSpecKey key} is registered as a \
      {repr rel.key.deriveSort}, not a Checker")
  | none =>
    match env.checkers[key.inductiveName]? with
    | some c => c size inputs
    | none =>
      .error (interpError s!"no checker registered for {renderSpecKey key} (add a `Checker`-sort \
        schedule with `InterpEnv.addRelation`, or a leaf with `InterpEnv.addChecker`)")

/-- The body of an emitted `aux_dec`: `checkerBacktrack` over the constructors admissible at this
    size. Any constructor answering `true` decides it; all answering `false` refutes it; an
    inconclusive one makes the whole thing inconclusive. -/
partial def interpCheckerSchedule (env : InterpEnv) (rel : RelSchedule) (fuel initSize size : Nat)
    (inputs : List Val) : Except GenError Bool :=
  match fuel with
  | 0 => .error Gen.outOfFuelError
  | fuel' + 1 =>
    let (baseScheds, recScheds) := rel.bucketedSchedules
    let branch := fun (size' : Nat) (p : Name × Schedule) =>
      -- `initSize` is the *original* budget, passed through unchanged as the emitted `aux_dec` does on
      -- every recursive call. Passing the current `size` instead shrinks the budget of delegated checks
      -- and enumerations at every level of recursion, and a check that runs out reads as a definite
      -- `false` rather than as inconclusive.
      fun (_ : Unit) => runCheckCtor env rel fuel' initSize size' inputs p.2
    -- The emitted checker's size-0 failsafe (`baseProducersWithFailsafe`): with recursive constructors
    -- still untried, "no base case matched" means *inconclusive*, not `false`. Without it this answered a
    -- definite `false` whenever the budget was smaller than the input — measured on Cedar's
    -- `MapNotContainsKey`: 54 of 532 cases wrongly `false` (a key absent from a map longer than the budget).
    let failsafe : List (Unit → Except GenError Bool) :=
      if recScheds.isEmpty then [] else [fun _ => .error Gen.outOfFuelError]
    match size with
    | 0 => checkerBacktrackInterp (baseScheds.map (branch 0) ++ failsafe)
    | size' + 1 =>
      checkerBacktrackInterp (baseScheds.map (branch size') ++ recScheds.map (branch size'))

/-- Runs one constructor's checker schedule. -/
partial def runCheckCtor (env : InterpEnv) (rel : RelSchedule) (fuel' initSize size' : Nat)
    (inputs : List Val) (sched : Schedule) : Except GenError Bool :=
  let (steps, sort) := sched
  let numRecCalls := countSizeConsumingCalls rel.key.inductiveName steps
  let sizeExpr := if numRecCalls ≤ 1 then size' else size' / numRecCalls
  match rel.bindInputs inputs with
  | .error e => .error (interpError e)
  | .ok bindings => runCheckSteps env rel fuel' initSize sizeExpr bindings steps sort

/-- Executes the remaining steps of a checker schedule.

    Two departures from the other sorts, both taken from the emitted code. A non-matching `Match` is
    `.ok false` rather than a throw (`MExp.lean:298`): a checker that fails to destructure has
    *refuted* this constructor, and saying "don't know" instead would make it useless. And a step that
    needs candidates enumerates them at **`initSize`**, not at the split budget (`MExp.lean:354`) — a
    checker's own size bounds its recursion, not the breadth of the search it does at each level. -/
partial def runCheckSteps (env : InterpEnv) (rel : RelSchedule) (fuel' initSize sizeExpr : Nat)
    (bindings : ValEnv) (steps : List ScheduleStep) (sort : ScheduleSort) :
    Except GenError Bool :=
  match steps with
  | [] =>
    match sort with
    -- A checker's conclusion needs nothing evaluated: reaching it *is* the proof.
    | .CheckerSchedule => .ok true
    | .ProducerSchedule .. => .ok true
    | .TheoremSchedule .. =>
      .error (interpError "theorem schedule reached in checker position")
  | step :: rest =>
    let continueWith := fun (bindings' : ValEnv) =>
      runCheckSteps env rel fuel' initSize sizeExpr bindings' rest sort
    match step with
    | .Unconstrained v src _ =>
      match src with
      | .NonRec hyp =>
        match env.lookupEnum hyp with
        | some e =>
          backtrackEnum (e initSize) (fun val => continueWith (bindings.insert v val)) false
        | none =>
          .error (interpError s!"no enumerator registered for type `{ppHypothesisExpr hyp}` \
            (needed to enumerate '{v}' while checking; register one with \
            `InterpEnv.addEnum {hyp.1}`)")
      | .Rec f args | .MutRec f args =>
        backtrackEnum ((interpEnumCall env f args fuel' initSize sizeExpr bindings) initSize)
          (fun outs => continueWith (bindings.insert v (collapseOutputs outs))) false
    | .SuchThat varsTys src _ =>
      let vars := varsTys.map Prod.fst
      let onOuts := fun (outs : List (Name × Val)) =>
        match bindVars (outs.map Prod.fst) (outs.map Prod.snd) bindings with
        | .ok bindings' => continueWith bindings'
        | .error e => .error (interpError e)
      match src with
      | .NonRec hypExpr =>
        backtrackEnum
          ((interpEnumConstrained env rel hypExpr vars initSize sizeExpr bindings) initSize)
          onOuts false
      | .Rec f args | .MutRec f args =>
        backtrackEnum ((interpEnumCall env f args fuel' initSize sizeExpr bindings) initSize)
          (fun outs =>
            match bindVars vars outs bindings with
            | .ok bindings' => continueWith bindings'
            | .error e => .error (interpError e)) false
    | .Check src polarity =>
      match checkSourceIn env rel.key fuel' initSize sizeExpr bindings src with
      | .error e => .error (interpError e)
      | .ok verdict =>
        andVerdict (if polarity then verdict else DecOpt.negOpt verdict) (continueWith bindings)
    | .Match _ scrutinee pattern =>
      match bindings[scrutinee]? with
      | none =>
        .error (interpError s!"match scrutinee '{scrutinee}' is unbound at this point")
      | some v =>
        match matchPattern pattern v bindings with
        | some bindings' => continueWith bindings'
        -- Refuted, not unknown.
        | none => .ok false

-- ## The shared `Check` step

/-- Interprets a `Check` step's source, for any sort of schedule.

    Generalises `checkSource`: where that consults only `InterpEnv.checkers`, this prefers an
    *interpreted* `Checker`-sort schedule for the relation. That is the whole point of this module —
    it is what stops a reordering that demotes a premise from requiring a hand-written checker.

    `Eq` and `Ne` stay structural, mirroring the built-in `[Decidable P] → DecOpt P` instance. A
    same-inductive dependency shares the split size budget; anything else gets the full `initSize`. -/
partial def checkSourceIn (env : InterpEnv) (key : SpecKey) (fuel' initSize sizeExpr : Nat)
    (bindings : ValEnv) (src : Source) : Except String (Except GenError Bool) :=
  match src with
  | .NonRec (relName, args) => do
    -- By the relation's positions, not only by kind: the interpreted checker preferred below binds one
    -- input per value position, so a surviving dictionary would be one too many (see `valueArgsAt`).
    let vals ← evalHypothesisArgs env.funcs bindings args (env.typeArgIndicesOf relName)
    if relName == ``Eq then
      match lastArgs 2 vals with
      | [a, b] => return .ok (a == b)
      | _ => .error s!"`Eq` check expected 2 value arguments, got {vals.length}"
    else if relName == ``Ne then
      match lastArgs 2 vals with
      | [a, b] => return .ok (!(a == b))
      | _ => .error s!"`Ne` check expected 2 value arguments, got {vals.length}"
    else
      let fuel := if relName == key.inductiveName then sizeExpr else initSize
      let checkKey : SpecKey :=
        { inductiveName := relName, outputIndices := [], deriveSort := .Checker,
          typeArgs := renderedTypeArgs (relName, args) }
      if (env.relations[checkKey]?).isSome then
        return interpChecker env checkKey env.fuel fuel vals
      else
        match env.checkers[relName]? with
        | some c => return c fuel vals
        | none =>
          .error s!"no checker for '{relName}' (needed to check \
            `{ppHypothesisExpr (relName, args)}`; derive a `Checker`-sort schedule for it, or \
            register a leaf with `InterpEnv.addChecker`)"
  | .Rec f args | .MutRec f args => do
    let vals ← (valueArgs args).mapM (evalConstructorExpr env.funcs bindings)
    -- A recursive check: the callee is this relation's own checker.
    match env.keyOfFn? f with
    | some k =>
      if k.deriveSort == .Checker then return interpChecker env k fuel' sizeExpr vals initSize
      else match env.checkers[f]? with
        | some c => return c sizeExpr vals
        | none => .error s!"'{f}' names a {repr k.deriveSort}, not a checker"
    | none =>
      match env.checkers[f]? with
      | some c => return c sizeExpr vals
      | none =>
        .error s!"step checks via '{f}', which names no registered checker; derive a \
          `Checker`-sort schedule or register a leaf with `InterpEnv.addChecker`"

end

/-- Enumerates a spec at the requested size, mirroring the emitted entry point
    `fun size => aux_enum <specimen.fuel> size size`. -/
def InterpEnv.enumerateSpec (env : InterpEnv) (key : SpecKey) (size : Nat)
    (inputs : List Val := []) : ExceptT GenError Enumerator (List Val) :=
  interpEnumRel env key env.fuel size size inputs

/-- Enumerates a spec into a list, capped at `limit` solutions. Errors in the enumeration are dropped;
    use `enumerateSpec` directly to see them. -/
def InterpEnv.enumerateList (env : InterpEnv) (key : SpecKey) (size : Nat)
    (inputs : List Val := []) (limit : Nat := 20) : List (List Val) :=
  let rec take (n : Nat) (l : LazyList (Except GenError (List Val))) : List (List Val) :=
    match n, l with
    | 0, _ => []
    | _, .lnil => []
    | n' + 1, .lcons hd tl =>
      match hd with
      | .ok v => v :: take n' tl.get
      | .error _ => take n' tl.get
  take limit ((env.enumerateSpec key size inputs) size)

/-- How much of an enumeration a consumer would have to walk, and what it found there.

    This is the cost a *checker* pays. `EnumeratorCombinators.enumeratingOpt` iterates the enumeration
    applying the check to each element, so a step whose sub-enumerator emits a thousand candidates
    before one satisfies costs a thousand check evaluations. Density does not see this at all — an
    enumerator that always produces is `Total` whether it produces one value or ten thousand — so
    measuring it is the only way the tuner can tell a cheap step from a ruinous one. -/
structure EnumCost where
  /-- Elements walked, capped at the caller's limit. -/
  walked : Nat := 0
  /-- Of those, how many were solutions rather than pruned branches. -/
  solutions : Nat := 0
  /-- Elements that were inconclusive (out of fuel), which poison a checker's verdict. -/
  inconclusive : Nat := 0
  /-- Whether the cap was hit, so `walked` is a floor rather than the true length. -/
  truncated : Bool := false
  deriving Repr, Inhabited

/-- Walks an enumeration and reports what it costs, without deciding anything.

    `limit` bounds the walk: an enumeration can be unbounded, and the useful question is usually
    "is this step cheap or expensive", which a cap answers. `truncated` says when the answer is a
    lower bound. -/
def enumCostOf {α : Type} (l : LazyList (Except GenError α)) (limit : Nat := 1000) : EnumCost :=
  let rec go (n : Nat) (l : LazyList (Except GenError α)) (acc : EnumCost) : EnumCost :=
    match n, l with
    | 0, .lnil => acc
    | 0, _ => { acc with truncated := true }
    | _, .lnil => acc
    | n' + 1, .lcons hd tl =>
      let acc := { acc with walked := acc.walked + 1 }
      let acc := match hd with
        | .ok _ => { acc with solutions := acc.solutions + 1 }
        | .error e =>
          if isEnumInconclusive e then { acc with inconclusive := acc.inconclusive + 1 } else acc
      go n' tl.get acc
  go limit l {}

/-- What walking a spec's enumeration costs at a size — the branching factor a checker pays per step
    that consults it. -/
def InterpEnv.enumCost (env : InterpEnv) (key : SpecKey) (size : Nat) (inputs : List Val := [])
    (limit : Nat := 1000) : EnumCost :=
  enumCostOf ((env.enumerateSpec key size inputs) size) limit

/-- A one-line rendering. -/
def EnumCost.renderLine (c : EnumCost) : String :=
  s!"walked {c.walked}{if c.truncated then "+" else ""} · {c.solutions} solution(s) ·     {c.inconclusive} inconclusive"

/-- The measured width of every registered leaf enumerator at a size: `(type head, elements)`.

    This closes the one input the static width model cannot derive. A `ValEnum` is a function, so its
    cardinality is discoverable only by walking it — but walking every *leaf* once is cheap, and leaves
    are exactly where the recursion bottoms out. Feed the result to
    `Specimen.Interp.EnumWidthModel.leaves` and the estimate needs no hand-supplied numbers.

    Only `enums` is calibrated, not `enumsAt`: the latter is keyed by a rendered type string while the
    width model is keyed by type head, so a precise entry has no place to go. That is a real gap for a
    polymorphic type with several registered instantiations, and it errs the safe way — an uncalibrated
    head falls back to `defaultLeafWidth`. -/
def InterpEnv.calibrateLeafWidths (env : InterpEnv) (size : Nat) (limit : Nat := 1000) :
    List (Name × Nat) :=
  env.enums.toList.map (fun (tyHead, e) => (tyHead, (enumCostOf (e size) limit).walked))

/-- Decides a spec at the requested size, mirroring the emitted `DecOpt.decOpt`. -/
def InterpEnv.decide (env : InterpEnv) (key : SpecKey) (size : Nat) (inputs : List Val := []) :
    Except GenError Bool :=
  interpChecker env key env.fuel size inputs

/-! ## Making interpreted checkers visible to generator schedules

    An asymmetry worth closing rather than documenting: `CheckEnum.checkSourceIn` prefers an
    *interpreted* `Checker` mode over a registered leaf, but `Gen.checkSource` — the one a **generator**
    schedule's `Check` step goes through — consults only `env.checkers`, the leaf table. `Gen` cannot do
    better on its own: `interpChecker` lives here, and this module imports `Gen`, so the dependency only
    runs one way.

    So publish them. For every derived `Checker` mode, install a leaf under the relation's name that runs
    the interpreted schedule. A leaf already registered by hand wins, since it was chosen deliberately.

    Apply this after `deriveClosure`/`deriveClosureWith`: without it, a generator whose plan demotes a
    premise reports "no checker registered" for a relation whose checker is sitting in the closure —
    8 pairs of Cedar's `HasType[0,4]` closure did exactly that.

    **Published twice: under the relation's name and under the mode's function name.** A `Check` on a
    premise of a *different* relation names it (`Source.NonRec`), but a check on the same relation, or on
    a mutual sibling, names the checker mode's recursive function (`Source.Rec`/`.MutRec`, e.g.
    `aux_hasTypeRecord_`), and `Gen.checkSource` looks that up by function name. Publishing only the
    relation name left those unresolved: `InterpEnv.check` said "resolved" (it goes through
    `env.relations`), while at run time every such check died on "no checker for `aux_…`" — which
    `backtrack` absorbed as a discard until `backtrackInterp` stopped doing so. On Cedar that was 5–7 of
    every 120 root samples, across `HasType.record`, `callExt`, `hasAttr*`/`getAttr*` and
    `MapNotContainsKey.skip`. -/
def InterpEnv.publishInterpretedCheckers (env : InterpEnv) : InterpEnv :=
  env.relations.toList.foldl (fun e (key, rel) =>
    if key.deriveSort != .Checker then e
    else
      let leaf : ValChecker := fun fuel vals => interpChecker env key env.fuel fuel vals
      let e := if e.checkers.contains key.inductiveName then e else e.addChecker key.inductiveName leaf
      if e.checkers.contains rel.recFnName then e else e.addChecker rel.recFnName leaf)
    env

end Specimen.Interp
