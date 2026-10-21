import Specimen.Interp.Preschedule

/-!
# When are two schedules the same generator?

`Interp.FromCompiled` starts learning from the deriver's settled premise orders. That is only a faithful
start if the interpreter lowers each order to the schedule the deriver emitted, and that is a claim about
*two different programs*: one run by `Interp.Gen` over untyped `Val`s, one emitted by `MExp` and
elaborated as typed Lean. So "the same" has to mean "behaves the same", and the comparator that checks it
has to be **sound**. It may call two equivalent schedules different, but it must never call two different
ones the same.

Four things a comparator must therefore not do, each of which equates schedules that generate different
things. They are what the readings below are built to avoid, and they are easy to reach for, because each
one makes agreement look higher:

* **Rename the inputs.** The caller binds a mode's inputs *by argument position*, so they are free
  variables of the schedule, not binders. Renaming them independently on each side equates
  `match a ~ x :: xs; match b ~ y :: ys; [z] ← P x ys` with the same schedule with `a` and `b` swapped,
  even though the swapped one passes the other input's head to `P`. Hence the Pin rule below.
* **Skip the epilogue.** Cedar's `Lub.ext` returns `.ext xty`. The interpreter binds `xty` from
  argument 0 and the deriver binds it from argument 1, and they agree only because both check
  `xty = xty'`. A comparator that stops at the steps calls them equal with that check deleted from
  either side.
* **Erase type-level arguments.** At a call to a polymorphic relation the `TyCtor`s are the
  instantiation (`renderedTypeArgs`, `SpecKey.typeArgs`), and an `Unconstrained` step's type is what
  `lookupArbitrary` looks up. Erase them and `x ← List Nat` equals `x ← List String`.
* **Trust the spelling.** Both sides spell Cedar's
  `MapNotContainsKey Attr (Qualified CedarType) instDecidableEqString a vrty` identically, so any
  syntactic comparator calls the two calls equal, whatever each side then does with the dictionary
  argument. In the compiled code instance synthesis fills it; the interpreter drops it by position
  (`typeArgIndicesOf`), and the reading below drops it the same way. Passing it on as a *value*
  instead, to a callee whose inputs exclude that position, leaves `bindVars` failing and `backtrack`
  swallowing the failure, so the call can never succeed and a spelling-based comparison still reports
  agreement.

## How the comparator works

First, each side is **read by its own evaluator** into one small value-level language (`NSched`).
The interpreter's steps are read exactly as `Gen.runSteps` reads them: constructor arguments by *kind*
(`valueArgs`); relation arguments by kind *and* by the relation's recorded type/instance positions
(`Side.typeIdxOf`, which must be `InterpEnv.typeArgIndicesOf` — the same positions `splitHypothesis` and
`evalHypothesisArgs` drop); `typeArgsOf`; `lastArgs 2`; and `matchPattern`'s binding and exact arity.
The compiled steps are read as Lean's typing reads them: constructor parameters and relation
type/instance positions are dropped by *position*. Where the two evaluators treat the same syntax
differently, the readings differ, and that is the point. The dictionary above becomes an extra input on
one side only.

Then only rewrites that preserve an `NSched`'s meaning are applied, the same way to both sides, and the
results are compared with `==`. That makes soundness a local property of each rule:

| Rule | What it does | Why it cannot hide a difference |
| --- | --- | --- |
| Pin | an input becomes `NVar.input pos` and a type parameter `NVar.tyParam pos`, taken from each side's own `argNames` | both sides bind inputs by position (`bindInputs`, the mode's lambda), never by spelling |
| Scope | each binding occurrence gets a fresh slot, and a read resolves to the latest binding of its name | `HashMap.insert` and Lean shadowing both make the latest binding win for later reads |
| Params | a compiled `Ctor` or pattern drops the arguments at the inductive's parameter positions; the interpreter's keeps its `valueArgs` | Lean's typing fixes the parameters, and a `Val` holds exactly its `valueArgs`. If the two drop different things, the readings differ |
| Call | a producer call is `(relation, output positions, type arguments by position, value inputs)`. Compiled inputs skip the callee's sort and class positions; interpreter inputs are what `splitHypothesis` passes | this is exactly what each side passes, and the callee is identified the way that side identifies it |
| Self | `Rec f` becomes `self` when `f` is that side's own `recFnName` | each side emits `Rec` only for the mode's own let-rec or `RelSchedule` |
| Runs | within a maximal run of `Match`/`Check` steps, matches are placed greedily by a key over already-pinned variables, then the checks are sorted | a run is a pure conjunction: it draws no randomness, allocates no size, and every failure is the same definitive rejection on both sides (`rejectAt`, `genericFailure`) |
| EqSubst | a run's `x = y` checks between variables merge those variables into classes. Later reads, and the run's other checks, read the class minimum, and the merging checks become a canonical star | a passing structural `Val.beq`, or a lawful `decide (x = y)`, means the two values are identical |
| EqSym | `Eq`/`Ne` arguments are sorted | both equalities are symmetric |
| Epilogue | the returned outputs are read and compared too, after EqSubst | the outputs are what the generator returns |

Two readings are conventions rather than consequences of the rules above, and the verdict on real Cedar
modes turns on them:

* a polymorphic mode is read at its instantiation (`SpecKey.typeArgs`), because as lowered without one it
  cannot run at all;
* an instance argument in a trailing position is dropped, the way `typeArgIndicesOf` drops it. Read
  strictly instead, Cedar's `hasAttrRecordNotFound` calls come out different from their compiled
  counterparts.

`SpecimenTest/Interp/ScheduleEquivTest.lean` is where the rules are exercised, and
`DeriverChoice.agreement` is what runs the comparison over a whole closure.

**Not certified here**, and needing a separate check:

* constructor weights: `RelSchedule.badness` is empty in an interpreted closure;
* `dispatchInputs`: its guard depends on the order of a leading run;
* checker and enumerator sorts: in a checker, `andOptList` makes the order of checks observable;
* the environment: that every leaf the interpreter calls behaves like the instance the compiled code calls
  (`Interp.Correspondence`), and that every callee mode's schedules agree as well. The latter is why a
  round trip has to compare every mode of the closure, not only the root (`DeriverChoice.agreement`).

The interpreter reading repeats `Gen.splitHypothesis`, `checkSource` and `interpCall` by hand. If those
change, `readSuchThat`, `readCheck` and `readRecCall` must change with them.
-/

open Lean Meta Schedules

namespace Specimen.Interp.ScheduleEquiv

/-! ## What the readings need to know about constructors and relations -/

/-- A constructor, as far as reading an application of it goes. -/
structure CtorShape where
  /-- The inductive's parameters. A `Ctor` spelled with all its arguments carries these first. That
      spelling comes from the reifier `exprToConstructorExpr` and from `allExplicit` patterns. Lean's
      typing fixes the parameters. -/
  numParams : Nat
  /-- One entry per field, in order: whether the field is explicit, and whether it carries a runtime value,
      i.e. its type is neither a sort nor a class. A `Val` has an argument for exactly the value fields. -/
  fields : List (Bool × Bool)
  deriving Repr, Inhabited

namespace CtorShape

def valueCount (s : CtorShape) : Nat := (s.fields.filter (·.2)).length

def explicitCount (s : CtorShape) : Nat := (s.fields.filter (·.1)).length

end CtorShape

/-- A relation's argument positions, split the way a call treats them. Kept as two lists where
    `Extract.extractTypeArgIndices` has one, because a call instantiates a sort position but passes
    nothing at a class position. -/
structure RelShape where
  arity : Nat
  /-- `Sort`-typed positions. A call instantiates them. -/
  sortPositions : List Nat
  /-- Instance positions. Instance synthesis fills them, so compiled code passes nothing there. -/
  classPositions : List Nat
  deriving Repr, Inhabited

def RelShape.typePositions (s : RelShape) : List Nat := s.sortPositions ++ s.classPositions

/-- The shape of every constructor and relation two schedules mention. `Shapes.build` reads these from
    the environment once, so the comparison itself is pure. -/
structure Shapes where
  ctors : Std.HashMap Name CtorShape := {}
  rels : Std.HashMap Name RelShape := {}

/-- The shape of `c`, or `none` if `c` is not a constructor. -/
def ctorShapeOf? (c : Name) : MetaM (Option CtorShape) := do
  match (← getEnv).find? c with
  | some (.ctorInfo info) =>
    forallTelescopeReducing info.type fun args _ => do
      let mut fields : List (Bool × Bool) := []
      for i in [info.numParams:args.size] do
        let a := args[i]!
        let ty ← inferType a
        let carries := !(ty.isSort || (← isClass? ty).isSome)
        let explicit := (← a.fvarId!.getDecl).binderInfo.isExplicit
        fields := fields ++ [(explicit, carries)]
      return some { numParams := info.numParams, fields := fields }
  | _ => return none

/-- The shape of `n`, read off its type, so a class method such as `LE.le` works as well as an
    inductive. `BST`'s `Between` checks `LE.le` with a `Nat` and an `instLENat`. -/
def relShapeOf? (n : Name) : MetaM (Option RelShape) := do
  match (← getEnv).find? n with
  | some info =>
    forallTelescopeReducing info.type fun args _ => do
      let mut sorts : List Nat := []
      let mut classes : List Nat := []
      for i in [0:args.size] do
        let ty ← inferType args[i]!
        if ty.isSort then sorts := sorts ++ [i]
        else if (← isClass? ty).isSome then classes := classes ++ [i]
      return some { arity := args.size, sortPositions := sorts, classPositions := classes }
  | none => return none

/-- Reads the shapes of the given constructors and relations. A name that is neither is skipped, and a
    reading that needs it later reports the missing shape. -/
def Shapes.build (ctors rels : List Name) : MetaM Shapes := do
  let mut s : Shapes := {}
  for c in ctors.eraseDups do
    match ← ctorShapeOf? c with
    | some sh => s := { s with ctors := s.ctors.insert c sh }
    | none => pure ()
  for r in rels.eraseDups do
    match ← relShapeOf? r with
    | some sh => s := { s with rels := s.rels.insert r sh }
    | none => pure ()
  return s

partial def exprCtors : ConstructorExpr → List Name
  | .Ctor c args => c :: args.flatMap exprCtors
  | .TyCtor _ args | .FuncApp _ args => args.flatMap exprCtors
  | _ => []

partial def patCtors : _root_.Pattern → List Name
  | .CtorPattern c ps => c :: ps.flatMap patCtors
  | _ => []

/-- The constructors and relations a schedule mentions, for `Shapes.build`. -/
def scheduleMentions (s : Schedule) : List Name × List Name :=
  let ofArgs := fun (args : List ConstructorExpr) => args.flatMap exprCtors
  let step := fun (st : Schedules.ScheduleStep) =>
    match st with
    | .Unconstrained _ (.NonRec _) _ => (([] : List Name), ([] : List Name))
    | .Unconstrained _ (.Rec _ args) _ | .Unconstrained _ (.MutRec _ args) _ => (ofArgs args, [])
    | .SuchThat _ (.NonRec (r, args)) _ | .Check (.NonRec (r, args)) _ => (ofArgs args, [r])
    | .SuchThat _ (.Rec _ args) _ | .SuchThat _ (.MutRec _ args) _
    | .Check (.Rec _ args) _ | .Check (.MutRec _ args) _ => (ofArgs args, [])
    | .Match _ _ p => (patCtors p, [])
  let outs := match s.2 with
    | .ProducerSchedule _ es => es.flatMap exprCtors
    | _ => []
  let parts := s.1.map step
  (parts.flatMap (·.1) ++ outs, parts.flatMap (·.2))

/-- The constructors and relations a set of specs mentions: everything an interpreted schedule
    lowered from them can mention. A negated premise contributes the relation under its `Not`, which
    is what the lowering checks. -/
def specMentions (specs : List RelSpec) : List Name × List Name :=
  let ctorsOf := fun (c : CtorSpec) =>
    c.conclusionArgs.flatMap exprCtors ++ c.hypotheses.flatMap (fun h => h.2.flatMap exprCtors)
  let relsOf := fun (c : CtorSpec) =>
    c.hypotheses.flatMap (fun h => [h.1, (peelNot h).1.1])
  (specs.flatMap (fun r => r.ctors.flatMap ctorsOf),
   specs.map (·.inductiveName) ++ specs.flatMap (fun r => r.ctors.flatMap relsOf))

/-! ## The common language -/

/-- A variable, independent of how either side spells it. -/
inductive NVar where
  /-- The mode's value input at argument position `pos`. -/
  | input (pos : Nat)
  /-- The relation's type or instance argument at position `pos`, while it is still a parameter. -/
  | tyParam (pos : Nat)
  /-- A binding occurrence. The reading numbers these first, and they are renumbered in canonical
      order. -/
  | bound (idx : Nat)
  /-- A name nothing binds: a global constant, which the interpreter resolves through `funcs`. -/
  | global (n : Name)
  deriving BEq, Repr, Inhabited

/-- A value-level expression, or a type where a type is expected. -/
inductive NExpr where
  | var (v : NVar)
  /-- A constructor applied to its **value** fields, which is what a `Val.ctor` holds. -/
  | ctor (c : Name) (args : List NExpr)
  | lit (l : Literal)
  /-- A function application, with its arguments as reified, types included. Both sides reify a premise
      with the same `exprToHypothesisExpr`, so comparing the whole application is complete in practice
      and sound on both sides. -/
  | fn (f : Name) (args : List NExpr)
  /-- A named type former applied to arguments. This covers a `TyCtor`, and also a nullary `FuncApp` or
      an unbound `Unknown` in a type position, since `Cedar.Spec.Attr` reifies as either. -/
  | ty (head : Name) (args : List NExpr)
  /-- A `Hole`: an argument left to the elaborator, which carries no value. -/
  | inferred
  | sort
  deriving BEq, Repr, Inhabited

inductive NPat where
  | bind (idx : Nat)
  | wild
  | lit (l : Literal)
  | ctor (c : Name) (ps : List NPat)
  /-- Matches no well-formed value. This is an interpreter pattern whose arity is not its constructor's
      value arity, and `matchPattern` rejects such a pattern on every input. -/
  | never
  deriving BEq, Repr, Inhabited

/-- What a call or a check runs. -/
inductive NTarget where
  /-- The mode being derived. -/
  | self
  /-- A function named directly: a mutual sibling, or a `Rec` that is not this side's own. Sibling
      names agree once the compiled schedule has been through `rewriteMutualCalls` against the closure's
      own sibling table. -/
  | fn (name : Name)
  /-- A mode of a relation: its output positions, and its instantiation by position. -/
  | rel (rel : Name) (outputs : List Nat) (typeArgs : List (Nat × NExpr))
  /-- Built-in structural equality (`Eq`/`Ne`), either as a check or as the `x = e` producer. -/
  | eq
  deriving BEq, Repr, Inhabited

inductive NStep where
  /-- Generate an unconstrained value of a type, and bind it. -/
  | gen (idx : Nat) (ty : NExpr) (sort : ProducerSort)
  /-- Call a producer on `inputs` and bind its outputs, ascending by output position, to `binds`. With
      `tupled`, all the outputs are bound to one variable as a tuple, which is what an `Unconstrained`
      step over a `Rec` does. -/
  | call (target : NTarget) (inputs : List NExpr) (binds : List Nat) (tupled : Bool)
      (sort : ProducerSort)
  | check (target : NTarget) (args : List NExpr) (polarity : Bool)
  | destruct (scrutinee : NVar) (pat : NPat)
  deriving BEq, Repr

/-- A schedule read into the common language: its steps, and what it returns, ascending by output
    position. -/
structure NSched where
  steps : List NStep
  outputs : List NExpr
  sort : ProducerSort
  deriving BEq, Repr

/-! ## Reading one side -/

/-- Whose evaluator a schedule is read with. -/
inductive Reading where
  /-- `Interp.Gen.runSteps`, over untyped `Val`s. -/
  | interp
  /-- The code `MExp` emits for the schedule, as typed Lean. -/
  | compiled
  deriving BEq, Repr, Inhabited

/-- One side of a comparison: everything its evaluator consults besides the steps. -/
structure Side where
  reading : Reading
  /-- The mode's relation. -/
  rel : Name
  /-- One name per argument position: `RelSchedule.argNames` for the interpreter,
      `InductiveSchedule.argNames` for the deriver. Inputs are pinned through these, never by spelling
      and never by the order they are first used in. -/
  argNames : List Name
  outputIndices : List Nat
  /-- The name this side's own recursive calls use: `RelSchedule.recFnName` or
      `InductiveSchedule.recFnName`. -/
  selfFn : Name
  /-- What each `MutRec` function name calls: `(function, relation, output positions)`. Only the
      compiled reading needs this, to know which of the call's arguments sit at type positions. -/
  siblings : List (Name × Name × List Nat) := []
  /-- The mode's instantiation by position, for a side whose code still names its type parameters. That
      is the compiled side, which elaboration instantiates. The interpreter's closure is already
      instantiated (`RelSpec.instantiate`), so this is empty there. -/
  inst : List (Nat × ConstructorExpr) := []
  /-- Interpreter only: the callees `(relation, output positions)` that are answered by a **leaf** reading
      its arguments from the end, which is `Bridge`'s convention (e.g. `mapNotContainsKeyCheck`'s
      `lastArgs 2`). For those, a leading dictionary is harmless, so only the trailing arguments are read.
      An empty list is the strict reading, which is right for an interpreted callee, whose `bindInputs`
      needs the exact arity. -/
  trailingLeaves : List (Name × List Nat) := []
  /-- Interpreter only: the argument positions of each relation that `Gen` drops as carrying no value —
      `InterpEnv.typeArgIndicesOf`, which `splitHypothesis` and `evalHypothesisArgs` consult. Reading the
      interpreter without it falls back to a by-kind rule that passes an instance dictionary as a value,
      which is not what `Gen` does. Pass `env.typeArgIndicesOf`; the default (`[]` everywhere) is exact
      only for an environment with no polymorphic relation. -/
  typeIdxOf : Name → List Nat := fun _ => []

structure ReadState where
  /-- What each name currently denotes, most recent binding first. -/
  scope : List (Name × NVar) := []
  next : Nat := 0

abbrev ReadM := StateT ReadState (Except String)

def lookupName (n : Name) : ReadM NVar := do
  match (← get).scope.find? (·.1 == n) with
  | some (_, v) => return v
  | none => return .global n

def bindName (n : Name) : ReadM Nat := do
  let s ← get
  set { s with scope := (n, NVar.bound s.next) :: s.scope, next := s.next + 1 }
  return s.next

def relShape (sh : Shapes) (r : Name) : ReadM RelShape :=
  match sh.rels[r]? with
  | some s => pure s
  | none => throw s!"no shape for relation `{r}` (collect it with `Shapes.build`)"

/-- A type, read the same way by both sides. Each looks a type up by what it denotes. The interpreter's
    `lookupArbitrary` uses the type's rendering, in which a `TyCtor` and a nullary `FuncApp` print alike,
    and Lean uses elaboration. So the reified *tag* is dropped, but never the name or the arguments. -/
partial def readType (side : Side) : ConstructorExpr → ReadM NExpr
  | .TyCtor c args | .Ctor c args => do
    return .ty c (← args.mapM (readType side))
  | .FuncApp f args =>
    if args.isEmpty then pure (.ty f [])
    else do return .fn f (← args.mapM (readType side))
  | .Unknown u => do
    match ← lookupName u with
    | .tyParam i =>
      match side.inst.find? (·.1 == i) with
      | some (_, t) => readType side t
      | none => return .var (.tyParam i)
    -- Kept distinct from `TyCtor n []`: an unbound name that happens to spell a type is not certainly
    -- that type (it can be a variable the reading failed to scope). Merging them could call two
    -- different schedules the same; keeping them apart can only cost a "differ".
    | v => return .var v
  | .Lit l => pure (.lit l)
  | .Hole => pure .inferred
  | .CSort _ => pure .sort

/-- An `Unconstrained` step's type. The head is a type parameter when the relation is polymorphic
    (`k' ← a_6` on the compiled side). -/
def readHypType (side : Side) (hyp : HypothesisExpr) : ReadM NExpr := do
  match ← lookupName hyp.1 with
  | .tyParam _ =>
    if hyp.2.isEmpty then readType side (.Unknown hyp.1)
    else throw s!"a type parameter applied to arguments: {ppHypothesisExpr hyp}"
  | _ => return .ty hyp.1 (← hyp.2.mapM (readType side))

/-- `Val.mkCtor`'s normalisation: `Nat.zero` is the literal `0`, and `Nat.succ` of a literal is the next
    literal. -/
def natNorm (c : Name) (args : List NExpr) : NExpr :=
  match c, args with
  | ``Nat.zero, [] => .lit (.natVal 0)
  | ``Nat.succ, [.lit (.natVal n)] => .lit (.natVal (n + 1))
  | _, _ => .ctor c args

/-- The compiled reading of a constructor application's arguments: its value fields.

    Two spellings reach here, and they are told apart by arity. The reifier (`exprToConstructorExpr`,
    used for premises) keeps every argument, parameters first. Unification ranges (`convertToCtorExpr`,
    used for the returned outputs) have already dropped every argument whose type is a sort or a class.
    The two arities differ whenever the distinction matters, i.e. whenever a parameter or a type-level
    field exists. Otherwise the two readings are the same list. -/
def compiledValueArgs (sh : Shapes) (c : Name) (args : List ConstructorExpr) :
    ReadM (List ConstructorExpr) := do
  let some s := sh.ctors[c]? | throw s!"no shape for constructor `{c}`"
  if args.length == s.numParams + s.fields.length then
    return ((args.drop s.numParams).zip s.fields).filterMap (fun (a, (_, carries)) =>
      if carries then some a else none)
  else if args.length == s.valueCount then return args
  else throw s!"`{c}` applied to {args.length} argument(s); it has {s.numParams} parameter(s) and \
    {s.fields.length} field(s), {s.valueCount} of them values"

/-- A value, read by `side`'s evaluator.

    * `Ctor`: the interpreter keeps `valueArgs`, i.e. whatever is not *syntactically* type-level, so a
      dictionary, or an abbreviation reified as a `FuncApp`, survives into the `Val`. The compiled code
      has exactly the value fields. Reading each side by its own rule is what lets a disagreement show.
    * `FuncApp`: both sides read the arguments as reified; see `NExpr.fn`.
    * `Nat.zero`/`Nat.succ` on a literal is the literal, as `Val.mkCtor` makes it. -/
partial def readVal (sh : Shapes) (side : Side) : ConstructorExpr → ReadM NExpr
  | .Unknown u => do return .var (← lookupName u)
  | .Lit l => pure (.lit l)
  | .Ctor c args => do
    let fields ← match side.reading with
      | .interp => pure (valueArgs args)
      | .compiled => compiledValueArgs sh c args
    return natNorm c (← fields.mapM (readVal sh side))
  | .TyCtor c args => readType side (.TyCtor c args)
  | .FuncApp f args => do
    return .fn f (← args.mapM (fun a => if isTypeLevel a then readType side a else readVal sh side a))
  | .CSort _ => pure .sort
  | .Hole => pure .inferred

/-- The names a pattern binds, in the preorder in which `matchPattern`'s left fold inserts them. -/
partial def patBinders : _root_.Pattern → List Name
  | .UnknownPattern u => if u == `_ then [] else [u]
  | .CtorPattern _ ps => ps.flatMap patBinders
  | .LitPattern _ => []

partial def NPat.hasNever : NPat → Bool
  | .never => true
  | .ctor _ ps => ps.any NPat.hasNever
  | _ => false

private partial def interpPatGo (sh : Shapes) (winners : List Nat) :
    _root_.Pattern → StateT Nat ReadM NPat
  | .UnknownPattern u => do
    if u == `_ then return .wild
    let i ← getThe Nat
    modifyThe Nat (· + 1)
    if winners.contains i then return .bind (← bindName u) else return .wild
  | .LitPattern l => pure (.lit l)
  | .CtorPattern c ps => do
    let qs ← ps.mapM (interpPatGo sh winners)
    match sh.ctors[c]? with
    | some s => return (if ps.length == s.valueCount then .ctor c qs else .never)
    | none => throw s!"no shape for constructor `{c}`"

/-- The interpreter's reading of a pattern, which is exactly `matchPattern`.

    Binding is `HashMap.insert` in a left-to-right fold. So when a name is repeated inside one pattern,
    only its **last** occurrence binds, and the earlier ones constrain nothing and read as wildcards. That
    is what happens with Cedar's `binaryAppEqLitSame` at every mode where the expression is an input:
    `binaryApp eq (lit p) (lit p)` accepts `lit 1 == lit 2`. A sub-pattern whose arity is not its
    constructor's value arity can never match, because `matchPattern` compares lengths, so it makes the
    whole pattern `never`. -/
def readPatInterp (sh : Shapes) (p : _root_.Pattern) : ReadM NPat := do
  let occ := patBinders p
  let winners := (occ.zipIdx.filter (fun (n, i) => !(occ.drop (i + 1)).contains n)).map (·.2)
  let q ← (interpPatGo sh winners p).run' 0
  return (if q.hasNever then .never else q)

/-- Lines a pattern that omits implicit arguments up with the constructor's fields. An omitted field
    becomes `none`. -/
def alignExplicit : List (Bool × Bool) → List _root_.Pattern → List (Option _root_.Pattern)
  | [], _ => []
  | (true, _) :: fs, p :: ps => some p :: alignExplicit fs ps
  | (true, _) :: fs, [] => none :: alignExplicit fs []
  | (false, _) :: fs, ps => none :: alignExplicit fs ps

/-- The compiled reading of a pattern, which is Lean's `match`.

    An `allExplicit` pattern (`@C params fields`) spells out the parameters. The scrutinee's type fixes
    them, so they are dropped. An `allowImplicit` pattern (`C fields`) omits the implicit arguments, and an
    omitted implicit *value* field matches anything. The two are told apart by arity, as in
    `compiledValueArgs`. A field that carries no value is dropped, because Lean cannot match on a type and
    a `Val` has nothing in that position. -/
partial def readPatCompiled (sh : Shapes) : _root_.Pattern → ReadM NPat
  | .UnknownPattern u => do
    if u == `_ then return .wild
    return .bind (← bindName u)
  | .LitPattern l => pure (.lit l)
  | .CtorPattern c ps => do
    let some s := sh.ctors[c]? | throw s!"no shape for constructor `{c}`"
    let perField : List (Option _root_.Pattern) ←
      if ps.length == s.numParams + s.fields.length then pure ((ps.drop s.numParams).map some)
      else if ps.length == s.explicitCount then pure (alignExplicit s.fields ps)
      else throw s!"pattern `{c}` has {ps.length} sub-pattern(s); it has {s.numParams} parameter(s) \
        and {s.fields.length} field(s), {s.explicitCount} explicit"
    let qs ← (perField.zip s.fields).filterMapM (fun (q, (_, carries)) => do
      if !carries then return none
      match q with
      | some p => return some (← readPatCompiled sh p)
      | none => return some NPat.wild)
    return .ctor c qs

/-- The compiled reading of a call's arguments, which are aligned with `positions` (the callee's
    non-output positions). The callee's sort and class positions are dropped. For a self-call, the type
    argument at each sort position must be the mode's own. Anything else is recursion at a different
    instantiation, which the interpreter's `sameMode` cannot see, since it ignores type arguments. That
    case is outside what this comparator certifies. -/
def compiledCallInputs (sh : Shapes) (side : Side) (rel : Name) (positions : List Nat)
    (args : List ConstructorExpr) (isSelf : Bool) : ReadM (List NExpr) := do
  let s ← relShape sh rel
  if positions.length != args.length then
    throw s!"call to `{rel}` passes {args.length} argument(s) for {positions.length} position(s)"
  let mut out : List NExpr := []
  for (a, i) in args.zip positions do
    if s.classPositions.contains i then continue
    if s.sortPositions.contains i then
      if isSelf then
        let t ← readType side a
        let own ← readType side (.Unknown (side.argNames.getD i Name.anonymous))
        unless t == own || t == .inferred do
          throw s!"self-call at a different instantiation: position {i} is {repr t}, the mode's is \
            {repr own}"
      continue
    out := out ++ [← readVal sh side a]
  return out

/-- `Rec`/`MutRec`: which function is called, and on what. Both sides bind the results in the listed order
    to the callee's outputs, ascending (`bindVars`, and the emitted tuple pattern). -/
def readRecCall (sh : Shapes) (side : Side) (isMut : Bool) (f : Name) (args : List ConstructorExpr)
    (checker : Bool) : ReadM (NTarget × List NExpr) := do
  let isSelf := !isMut && f == side.selfFn
  let target : NTarget := if isSelf then .self else .fn f
  match side.reading with
  | .interp => return (target, ← (valueArgs args).mapM (readVal sh side))
  | .compiled =>
    let (callee, outs) ←
      if isSelf then pure (side.rel, if checker then [] else side.outputIndices)
      else
        match side.siblings.find? (·.1 == f) with
        | some (_, r, o) => pure (r, o)
        | none => throw s!"`{f}` is neither this mode's own function nor a sibling the closure links"
    let s ← relShape sh callee
    let positions := (List.range s.arity).filter (fun i => !outs.contains i)
    return (target, ← compiledCallInputs sh side callee positions args isSelf)

/-- The positions a producer call outputs, found the way `Gen.splitHypothesis` finds them: each output
    variable at its first mention, ascending. -/
def interpOutputs (vars : List Name) (args : List ConstructorExpr) : List (Nat × Name) :=
  let found := args.zipIdx.filterMap (fun (a, i) =>
    match a with
    | .Unknown u => if vars.contains u then some (i, u) else none
    | _ => (varsInConstructorExpr a |>.find? (vars.contains ·)).map (fun u => (i, u)))
  found.foldl (fun acc (i, u) => if acc.any (·.2 == u) then acc else acc ++ [(i, u)])
    ([] : List (Nat × Name))

/-- A relation's type arguments as the compiled code states them: whatever sits at a sort position, unless
    it is a `Hole`. The interpreter records nothing there either (`typeArgsOf` keeps only `TyCtor`s). -/
def compiledTypeArgs (side : Side) (s : RelShape) (args : List ConstructorExpr) :
    ReadM (List (Nat × NExpr)) :=
  s.sortPositions.filterMapM (fun i => do
    match args[i]? with
    | some ConstructorExpr.Hole | none => return none
    | some a => return some (i, ← readType side a))

/-- A `SuchThat` over another relation or mode.

    Interpreter: `splitHypothesis` passes as inputs the positions that are neither outputs nor
    *syntactically* type-level (`isTypeLevel`), and `interpConstrained` keys the callee by
    `typeArgsOf`. Compiled: the positions that are neither outputs nor the callee's sort or class
    positions, with the sort positions as the instantiation. The inputs are read before the outputs are
    bound, as each side evaluates them. -/
def readSuchThat (sh : Shapes) (side : Side) (outs : List Name) (hyp : HypothesisExpr)
    (ps : ProducerSort) : ReadM NStep := do
  let (r, args) := hyp
  match side.reading with
  | .interp =>
    let outputs := interpOutputs outs args
    let missing := outs.filter (fun v => !outputs.any (·.2 == v))
    unless missing.isEmpty do
      throw s!"interpreter: {missing} produced by `{r}` but not among its arguments"
    for (i, u) in outputs do
      unless args[i]? == some (.Unknown u) do
        throw s!"interpreter: output `{u}` of `{r}` sits under a constructor or function (a delegated \
          producer), which this comparator does not model"
    -- Exactly `splitHypothesis`'s selection: not an output, not at one of the relation's recorded
    -- type/instance positions, not syntactically type-level.
    let typeIdx := side.typeIdxOf r
    let rawInputs := args.zipIdx.filterMap (fun (a, i) =>
      if outputs.any (·.1 == i) || typeIdx.contains i || isTypeLevel a then none else some a)
    if r == ``Eq then
      match outputs, lastArgs 1 rawInputs with
      | [(_, u)], [e] =>
        let e' ← readVal sh side e
        return .call .eq [e'] [← bindName u] false ps
      | _, _ => throw "interpreter: the `Eq` producer needs one unknown side and one known side"
    else
      let positions := outputs.map (·.1)
      let s ← relShape sh r
      let rawInputs :=
        if side.trailingLeaves.contains (r, positions) then
          lastArgs (s.arity - positions.length - s.typePositions.length) rawInputs
        else rawInputs
      let inputs ← rawInputs.mapM (readVal sh side)
      let typeArgs ← (typeArgsOf hyp).mapM (fun (i, a) => do return (i, ← readType side a))
      let binds ← outputs.mapM (fun (_, u) => bindName u)
      return .call (.rel r positions typeArgs) inputs binds false ps
  | .compiled =>
    if r == ``Eq then
      let sides := if args.length == 3 then args.drop 1 else args
      match outs, sides with
      | [u], [l, rhs] =>
        let isL := l == .Unknown u
        let isR := rhs == .Unknown u
        unless isL != isR do
          throw s!"compiled: the `Eq` producer for `{u}` must have it alone on exactly one side"
        let e' ← readVal sh side (if isL then rhs else l)
        return .call .eq [e'] [← bindName u] false ps
      | _, _ => throw "compiled: the `Eq` producer needs one unknown side and one known side"
    else
      let s ← relShape sh r
      let mut placed : List (Nat × Name) := []
      for u in outs do
        match args.zipIdx.filter (fun (a, _) => (varsInConstructorExpr a).contains u) with
        | [(.Unknown u', i)] =>
          if u' == u then placed := placed ++ [(i, u)]
          else throw s!"compiled: output `{u}` of `{r}` is not a bare argument"
        | _ => throw s!"compiled: output `{u}` of `{r}` is not a single bare argument"
      let placedSorted := placed.mergeSort (fun a b => a.1 ≤ b.1)
      let positions := placedSorted.map (·.1)
      let typeArgs ← compiledTypeArgs side s args
      let rawInputs := args.zipIdx.filterMap (fun (a, i) =>
        if positions.contains i || s.typePositions.contains i then none else some a)
      let inputs ← rawInputs.mapM (readVal sh side)
      let binds ← placedSorted.mapM (fun (_, u) => bindName u)
      return .call (.rel r positions typeArgs) inputs binds false ps

/-- A `Check`. `Eq`/`Ne` compare two values structurally on both sides. The interpreter uses the last two
    value arguments (`checkSource`'s `lastArgs 2`), and Lean uses `@Eq α a b`. A check of `Ne` is a check
    of `Eq` with the polarity flipped. Any other relation is a checker call, whose arguments are read as
    in `readSuchThat`. -/
def readCheck (sh : Shapes) (side : Side) (src : Schedules.Source) (pol : Bool) : ReadM NStep := do
  match src with
  | .NonRec (r, args) =>
    if r == ``Eq || r == ``Ne then
      let pol' := if r == ``Ne then !pol else pol
      let two ← match side.reading with
        | .interp => do
          -- `checkSource`: `evalHypothesisArgs` (= `valueArgsAt` at the relation's positions), then
          -- `lastArgs 2`.
          let vs := valueArgsAt (side.typeIdxOf r) args
          if vs.length < 2 then
            throw s!"interpreter: `{r}` check with {vs.length} value argument(s)"
          pure (lastArgs 2 vs)
        | .compiled => do
          if args.length == 3 then pure (args.drop 1)
          else if args.length == 2 then pure args
          else throw s!"compiled: `{r}` with {args.length} argument(s)"
      return .check .eq (← two.mapM (readVal sh side)) pol'
    else
      let s ← relShape sh r
      match side.reading with
      | .interp =>
        let vs := valueArgsAt (side.typeIdxOf r) args
        let vs :=
          if side.trailingLeaves.contains (r, []) then lastArgs (s.arity - s.typePositions.length) vs
          else vs
        let typeArgs ← (typeArgsOf (r, args)).mapM (fun (i, a) => do return (i, ← readType side a))
        return .check (.rel r [] typeArgs) (← vs.mapM (readVal sh side)) pol
      | .compiled =>
        let typeArgs ← compiledTypeArgs side s args
        let vs := args.zipIdx.filterMap (fun (a, i) =>
          if s.typePositions.contains i then none else some a)
        return .check (.rel r [] typeArgs) (← vs.mapM (readVal sh side)) pol
  | .Rec f args => do
    let (t, ins) ← readRecCall sh side false f args true
    return .check t ins pol
  | .MutRec f args => do
    let (t, ins) ← readRecCall sh side true f args true
    return .check t ins pol

/-- `readStep` without the fail-closed guard. -/
def readStepCore (sh : Shapes) (side : Side) : Schedules.ScheduleStep → ReadM NStep
  | .Unconstrained v (.NonRec ty) ps => do
    let t ← readHypType side ty
    return .gen (← bindName v) t ps
  | .Unconstrained v (.Rec f args) ps => do
    let (t, ins) ← readRecCall sh side false f args false
    return .call t ins [← bindName v] true ps
  | .Unconstrained v (.MutRec f args) ps => do
    let (t, ins) ← readRecCall sh side true f args false
    return .call t ins [← bindName v] true ps
  | .SuchThat outs (.NonRec hyp) ps => readSuchThat sh side (outs.map (·.1)) hyp ps
  | .SuchThat outs (.Rec f args) ps => do
    let (t, ins) ← readRecCall sh side false f args false
    return .call t ins (← outs.mapM (fun o => bindName o.1)) false ps
  | .SuchThat outs (.MutRec f args) ps => do
    let (t, ins) ← readRecCall sh side true f args false
    return .call t ins (← outs.mapM (fun o => bindName o.1)) false ps
  | .Check src pol => readCheck sh side src pol
  | .Match _ scrutinee p => do
    let s ← lookupName scrutinee
    let q ← match side.reading with
      | .interp => readPatInterp sh p
      | .compiled => do
        -- Lean rejects a repeated pattern variable, so a successful derivation never emits one.
        let bs := patBinders p
        unless bs.length == bs.eraseDups.length do
          throw s!"compiled: non-linear pattern {ppPattern p}"
        readPatCompiled sh p
    return .destruct s q

def readStep (sh : Shapes) (side : Side) (step : Schedules.ScheduleStep) : ReadM NStep := do
  -- Fail closed on what this comparator does not model. An enumerator sub-producer inside a generator
  -- schedule walks candidates with its own failure handling, which has not been checked against the
  -- emitted code.
  match step with
  | .Unconstrained _ _ .Enumerator | .SuchThat _ _ .Enumerator =>
    throw "an enumerator sub-producer inside a generator schedule is not modelled"
  | _ => pure ()
  readStepCore sh side step

/-- The scope a schedule starts in: each input position's name pinned to its position, and each type or
    instance position's name to its parameter. -/
def initialScope (sh : Shapes) (side : Side) : Except String ReadState := do
  let some s := sh.rels[side.rel]? | throw s!"no shape for relation `{side.rel}`"
  unless side.argNames.length == s.arity do
    throw s!"{side.argNames.length} argument name(s) for `{side.rel}`, which takes {s.arity}"
  let scope := side.argNames.zipIdx.filterMap (fun (n, i) =>
    if s.typePositions.contains i then some (n, NVar.tyParam i)
    else if side.outputIndices.contains i then none
    else some (n, NVar.input i))
  return { scope := scope }

/-- Reads a generator schedule with `side`'s evaluator: the steps, and then the returned outputs in the
    final scope.
    The interpreter returns its outputs in ascending position order. The deriver returns them in
    `outputIndices` order, so they are sorted into position order too. -/
def readSchedule (sh : Shapes) (side : Side) (sched : Schedule) : Except String NSched := do
  let st ← initialScope sh side
  let go : ReadM NSched := do
    let steps ← sched.1.mapM (readStep sh side)
    match sched.2 with
    | .ProducerSchedule .Generator outs =>
      unless outs.length == side.outputIndices.length do
        throw s!"the schedule returns {outs.length} output(s) for a mode with {side.outputIndices.length}"
      let outs' ← outs.mapM (readVal sh side)
      let outs' := match side.reading with
        | .interp => outs'
        | .compiled => ((side.outputIndices.zip outs').mergeSort (fun a b => a.1 ≤ b.1)).map (·.2)
      return { steps := steps, outputs := outs', sort := .Generator }
    | _ => throw "only generator schedules are certified: in a checker the order of checks is observable, \
        and the enumerator interpreter's failure handling has not been checked against the emitted code"
  go.run' st

/-! ## Canonical form -/

structure CanonState where
  /-- The reading's binder numbers, mapped to canonical ones in the order they are placed. -/
  ren : Std.HashMap Nat Nat := {}
  next : Nat := 0
  /-- EqSubst: a variable mapped to the least member of its equality class. -/
  rep : List (NVar × NVar) := []

instance : Inhabited CanonState := ⟨{}⟩

namespace CanonState

def var (st : CanonState) (v : NVar) : NVar :=
  let v' : NVar := match v with
    | .bound k => (st.ren[k]?).elim (NVar.global `«unplaced») NVar.bound
    | other => other
  match st.rep.find? (·.1 == v') with
  | some (_, r) => r
  | none => v'

partial def expr (st : CanonState) : NExpr → NExpr
  | .var v => .var (st.var v)
  | .ctor c xs => .ctor c (xs.map (expr st))
  | .fn f xs => .fn f (xs.map (expr st))
  | .ty h xs => .ty h (xs.map (expr st))
  | e => e

def target (st : CanonState) : NTarget → NTarget
  | .rel r outs tas => .rel r outs (tas.map (fun (i, t) => (i, expr st t)))
  | t => t

def assign (st : CanonState) (ks : List Nat) : CanonState :=
  ks.foldl (fun s k => { s with ren := s.ren.insert k s.next, next := s.next + 1 }) st

partial def pat (st : CanonState) : NPat → NPat
  | .bind k => .bind (st.ren.getD k k)
  | .ctor c ps => .ctor c (ps.map (pat st))
  | p => p

end CanonState

partial def NPat.binders : NPat → List Nat
  | .bind k => [k]
  | .ctor _ ps => ps.flatMap NPat.binders
  | _ => []

def NStep.binders : NStep → List Nat
  | .gen k _ _ => [k]
  | .call _ _ bs _ _ => bs
  | .check .. => []
  | .destruct _ p => p.binders

/-- A step with its reads resolved through `st` and its binders numbered next. -/
def place (st : CanonState) (s : NStep) : CanonState × NStep :=
  let st' := st.assign s.binders
  let s' : NStep := match s with
    | .gen k t ps => .gen (st'.ren.getD k k) (st.expr t) ps
    | .call tg ins bs tup ps =>
      .call (st.target tg) (ins.map st.expr) (bs.map (fun k => st'.ren.getD k k)) tup ps
    | .check tg xs pol => .check (st.target tg) (xs.map st.expr) pol
    | .destruct v p => .destruct (st.var v) (st'.pat p)
  (st', s')

partial def NPat.blank : NPat → NPat
  | .bind _ => .bind 0
  | .ctor c ps => .ctor c (ps.map NPat.blank)
  | p => p

/-- The key a ready `Match` is placed by. It depends only on its scrutinee, which is already pinned or
    placed, and on the shape of its pattern with the binders blanked out. So it is invariant under
    renaming, and two matches on different inputs never tie. -/
def destructKey (st : CanonState) : NStep → String
  | .destruct v p => reprStr (st.var v) ++ " ~ " ++ reprStr p.blank
  | s => reprStr s

def mergeable : NVar → Bool
  | .input _ | .bound _ => true
  | _ => false

/-- A check `x = y` between two variables, which EqSubst merges. -/
def eqEdge? : NStep → Option (NVar × NVar)
  | .check .eq [.var a, .var b] true => if mergeable a && mergeable b then some (a, b) else none
  | _ => none

/-- Inputs first, by position, then type parameters, then binders in canonical order. -/
def NVar.before (a b : NVar) : Bool :=
  let rank : NVar → Nat × Nat := fun
    | .input p => (0, p)
    | .tyParam p => (1, p)
    | .bound i => (2, i)
    | .global _ => (3, 0)
  let (x, y) := rank a
  let (x', y') := rank b
  x < x' || (x == x' && y < y')

def mergeClasses (edges : List (NVar × NVar)) : List (List NVar) :=
  edges.foldl (fun cls (a, b) =>
    let (touched, rest) := cls.partition (fun c => c.contains a || c.contains b)
    (touched.flatten ++ [a, b]).eraseDups :: rest) []

def classMin (c : List NVar) : NVar :=
  c.foldl (fun m v => if v.before m then v else m) (c.headD (.global `_))

/-- EqSym: `Eq` arguments in a fixed order. -/
def symEq : NStep → NStep
  | .check .eq [a, b] pol =>
    if compare (reprStr a) (reprStr b) == .gt then .check .eq [b, a] pol else .check .eq [a, b] pol
  | s => s

/-- `x = x` on a variable passes on both sides: `Val.beq` is reflexive, `decide (x = x)` is true, and
    reading a bound variable cannot fail. -/
def trivialEq : NStep → Bool
  | .check .eq [.var a, .var b] true =>
    -- Only for variables that certainly denote one value: a pinned input or a bound slot. A type
    -- parameter or an unresolved global is not a runtime value, so `x = x` on one says nothing.
    a == b && (match a with | .input _ | .bound _ => true | _ => false)
  | _ => false

/-- One maximal run of `Match`/`Check` steps, in canonical order.

    The matches come first. Each is placed once its scrutinee is placed, least `destructKey` first, so the
    ties that left each side in its own order no longer happen. Then EqSubst runs over the run's
    variable-to-variable equalities, and the checks follow in sorted order. All of this is sound because
    the run is a pure conjunction. -/
def canonRun (st₀ : CanonState) (run : List NStep) : CanonState × List NStep := Id.run do
  let mut st := st₀
  let mut out : List NStep := []
  let mut pending := run.filter (fun s => match s with | .destruct .. => true | _ => false)
  let checks := run.filter (fun s => match s with | .check .. => true | _ => false)
  for _ in [0:pending.length] do
    let binding := pending.flatMap NStep.binders
    let ready := pending.filter (fun s => match s with
      | .destruct (.bound k) _ => !binding.contains k
      | _ => true)
    let best := ready.foldl (fun (b : Option NStep) s => match b with
      | none => some s
      | some c => if compare (destructKey st s) (destructKey st c) == .lt then some s else some c) none
    match best with
    | none => break
    | some s =>
      let (st', s') := place st s
      st := st'
      out := out ++ [s']
      pending := pending.erase s
  -- Anything never ready (impossible for a well-scoped schedule) keeps its order.
  for s in pending do
    let (st', s') := place st s
    st := st'
    out := out ++ [s']
  let pre := checks.map (fun s => (s, eqEdge? (place st s).2))
  let classes := mergeClasses (pre.filterMap (·.2))
  let mut star : List NStep := []
  for c in classes do
    let r := classMin c
    for m in c do
      if m != r then
        st := { st with rep := (st.rep.map (fun (a, b) => (a, if b == m then r else b))) ++ [(m, r)] }
        star := star ++ [symEq (.check .eq [.var r, .var m] true)]
  let others := ((pre.filter (·.2.isNone)).map (fun (s, _) => symEq (place st s).2)).filter
    (fun s => !trivialEq s)
  let checks' := (star ++ others).mergeSort (fun a b => compare (reprStr a) (reprStr b) != .gt)
  return (st, out ++ checks')

def isPassive : NStep → Bool
  | .check .. | .destruct .. => true
  | _ => false

/-- The steps split into maximal passive runs and single producers, in order. -/
def segments (steps : List NStep) : List (List NStep) :=
  steps.foldl (fun acc s =>
    match acc.getLast? with
    | some last =>
      if isPassive s && last.all isPassive then acc.dropLast ++ [last ++ [s]] else acc ++ [[s]]
    | none => [[s]]) []

/-- The canonical form. Producers never move, runs are canonicalised, and EqSubst reaches every later
    read, including the returned outputs. -/
def canon (s : NSched) : NSched := Id.run do
  let mut st : CanonState := {}
  let mut out : List NStep := []
  for seg in segments s.steps do
    if seg.all isPassive then
      let (st', seg') := canonRun st seg
      st := st'
      out := out ++ seg'
    else
      for x in seg do
        let (st', x') := place st x
        st := st'
        out := out ++ [x']
  return { steps := out, outputs := s.outputs.map st.expr, sort := s.sort }

/-! ## Comparing -/

/-- The outcome of comparing one constructor's two schedules. -/
inductive Verdict where
  /-- Equal after reading and canonicalising: the same generator, under the rules above. -/
  | same
  /-- Different, with the kind and location of the first difference. The rules are incomplete, so this
      does not prove the two are inequivalent, but it never counts as agreement. -/
  | differ (kind : String) (detail : String)
  /-- One side falls outside what the readings model: a nested producer output, a compiled non-linear
      pattern, recursion at another instantiation, or a missing shape. This never counts as agreement
      either. -/
  | outside (why : String)
  deriving Repr, BEq, Inhabited

def diffKind : NStep → NStep → String
  | .call t₁ i₁ _ _ _, .call t₂ i₂ _ _ _ =>
    if t₁ != t₂ then "call: callee" else if i₁ != i₂ then "call: inputs" else "call: bindings or sort"
  | .check t₁ a₁ _, .check t₂ a₂ _ =>
    if t₁ != t₂ then "check: relation" else if a₁ != a₂ then "check: arguments" else "check: polarity"
  | .destruct v₁ _, .destruct v₂ _ => if v₁ != v₂ then "match: scrutinee" else "match: pattern"
  | .gen _ t₁ _, .gen _ t₂ _ => if t₁ != t₂ then "unconstrained: type" else "unconstrained: sort"
  | _, _ => "step kind"

def firstDifference (a b : NSched) : String × String := Id.run do
  for ((x, y), i) in (a.steps.zip b.steps).zipIdx do
    if x != y then
      return (diffKind x y, s!"step {i}: interpreter {reprStr x} | compiled {reprStr y}")
  if a.steps.length != b.steps.length then
    return ("length", s!"{a.steps.length} step(s) against {b.steps.length}")
  if a.outputs != b.outputs then
    return ("returns", s!"interpreter returns {reprStr a.outputs} | compiled {reprStr b.outputs}")
  return ("producer sort", s!"interpreter {reprStr a.sort} | compiled {reprStr b.sort}")

/-- A schedule read with `side`'s evaluator and put in canonical form. Useful for looking at why two
    schedules differ. -/
def normalize (sh : Shapes) (side : Side) (sched : Schedule) : Except String NSched :=
  canon <$> readSchedule sh side sched

/-- Compares an interpreter schedule with a compiled one. `.same` means the two generate the same
    thing, under the rules in the module docstring. -/
def compareSchedules (sh : Shapes) (interpSide compiledSide : Side) (interp compiled : Schedule) :
    Verdict :=
  match readSchedule sh interpSide interp, readSchedule sh compiledSide compiled with
  | .error e, _ => .outside s!"interpreter side: {e}"
  | _, .error e => .outside s!"compiled side: {e}"
  | .ok a, .ok b =>
    let a := canon a
    let b := canon b
    if a == b then .same
    else
      let (k, d) := firstDifference a b
      .differ k d

end Specimen.Interp.ScheduleEquiv
