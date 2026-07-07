import Specimen.UnificationMonad
import Specimen.Utils
import Specimen.Score

open Lean


namespace Schedules
----------------------------------------------
-- Type definitions
----------------------------------------------

/-- A `HypothesisExpr` is a datatype representing a hypothesis for a
    constructor of an inductive relation, consisting of a constructor name
    applied to some list of arguments, each of which are `ConstructorExpr`s -/
abbrev HypothesisExpr := Name × List ConstructorExpr

/-- `ToExpr` instance for `HypothesisExpr`
    (for converting `HypothesisExpr`s to Lean `Expr`s) -/
instance : ToExpr HypothesisExpr where
  toExpr (hypExpr : HypothesisExpr) : Expr :=
    let (ctorName, ctorArgs) := hypExpr
    mkAppN (mkConst ctorName) (toExpr <$> ctorArgs.toArray)
  toTypeExpr := mkConst ``Expr

local instance [Ord α][Ord β]: Ord (α × β) := lexOrd

/-- A source is the thing we wish to check/generate/enumerate -/
inductive Source
  | NonRec : HypothesisExpr → Source
  | Rec : Name → List ConstructorExpr → Source
  | MutRec : Name → List ConstructorExpr → Source
  deriving Repr, BEq

/-- Producers are either enumerators or generators -/
inductive ProducerSort
  | Enumerator
  | Generator
  deriving Repr, BEq, Ord

/-- The sort of function we are deriving based on an inductive relation:
    determines whether we are deriving a (constrained) generator, enumerator or a checker.

    Note: the `Theorem` constructor is used in the artifact of "Testing Theorems, Fully Automatically"
    for automatically testing whether a theorem holds (we replicate it here for completeness). -/
inductive DeriveSort
  | Generator
  | Enumerator
  | Checker
  | Theorem
  deriving Repr, BEq, Ord, Hashable, Inhabited

/-- Determines if a `DeriveSort` corresponds to a producer
    (only generators & enumerators are considered producers) -/
def DeriveSort.isProducer : DeriveSort → Bool
  | .Generator | .Enumerator => true
  | .Checker | .Theorem => false

/-- The type of schedule we wish to derive -/
inductive ScheduleSort
  /-- tuple of produced outputs from conclusion of constructor -/
  | ProducerSchedule (producerSort : ProducerSort) (conclusion : List ConstructorExpr)

  /-- checkers need not bother with conclusion of constructor,
      only hypotheses need be checked and conclusion of constructor follows-/
  | CheckerSchedule

  /-- In a `TheoremSchedule`, we check the `conclusion` of the theorem, and take in a `Bool`
      which is true if we need to find a checker by identifying the `DecOpt` instance,
      and false otherwise (we're currently dealing with a function that returns `Option Bool`) -/
  | TheoremSchedule (conclusion : HypothesisExpr) (typeClassUsed : Bool)

  deriving Repr, BEq

inductive Explicit where | allExplicit | allowImplicit deriving Repr, BEq, Ord

/-- A single step in a generator schedule -/
inductive ScheduleStep
  /-- Unconstrained generation -/
  | Unconstrained : Name → Source → ProducerSort → ScheduleStep

  /-- Generate a value such that a predicate is satisfied -/
  | SuchThat : List (Name × Option ConstructorExpr) → Source → ProducerSort → ScheduleStep

  /-- Check whether some proposition holds
     (the bool is the desired truth value of the proposition we're checking) -/
  | Check : Source → Bool → ScheduleStep

  /-- Used when you decompose a constructor constrained arg into a
    fresh variable followed by a pattern match -/
  | Match : Explicit → Name → Pattern → ScheduleStep
  deriving Repr, BEq

/-- Pretty-print a ConstructorExpr in readable form -/
partial def ppConstructorExpr : ConstructorExpr → String
  | .Unknown name => name.toString
  | .Hole => "_"
  | .Lit (.natVal n) => toString n
  | .Lit (.strVal s) => s!"\"{s}\""
  | .CSort _ => "Sort"
  | .Ctor ``Prod.mk [_, _, a, b] => s!"({ppConstructorExpr a}, {ppConstructorExpr b})"
  | .Ctor ``Prod.mk [a, b] => s!"({ppConstructorExpr a}, {ppConstructorExpr b})"
  | .Ctor ``List.nil _ => "[]"
  | .Ctor ``List.cons [_, h, t] => s!"{ppConstructorExpr h} :: {ppConstructorExpr t}"
  | .Ctor ``List.cons [h, t] => s!"{ppConstructorExpr h} :: {ppConstructorExpr t}"
  | .Ctor ``Bool.true [] => "true"
  | .Ctor ``Bool.false [] => "false"
  | .Ctor name args =>
    let shortName := name.componentsRev.head?.getD name |>.toString
    if args.isEmpty then shortName else s!"{shortName} {" ".intercalate (args.map ppConstructorExpr)}"
  | .TyCtor name args =>
    let shortName := name.componentsRev.head?.getD name |>.toString
    if args.isEmpty then shortName else s!"{shortName} {" ".intercalate (args.map ppConstructorExpr)}"
  | .FuncApp name args =>
    let shortName := name.componentsRev.head?.getD name |>.toString
    if args.isEmpty then shortName else s!"({shortName} {" ".intercalate (args.map ppConstructorExpr)})"

/-- Pretty-print a HypothesisExpr -/
def ppHypothesisExpr (hyp : HypothesisExpr) : String :=
  let (name, args) := hyp
  if name == ``Eq then
    match args with
    | [_, lhs, rhs] => s!"{ppConstructorExpr lhs} = {ppConstructorExpr rhs}"
    | [lhs, rhs] => s!"{ppConstructorExpr lhs} = {ppConstructorExpr rhs}"
    | _ => s!"Eq {" ".intercalate (args.map ppConstructorExpr)}"
  else
    let shortName := name.componentsRev.head?.getD name |>.toString
    if args.isEmpty then shortName else s!"{shortName} {" ".intercalate (args.map ppConstructorExpr)}"

/-- Stringifier for `Source` -/
def ppSource source := match source with
  | Source.Rec name ctrArgs =>
    let shortName := name.componentsRev.head?.getD name |>.toString
    s!"{shortName} {" ".intercalate (ctrArgs.map ppConstructorExpr)}"
  | Source.MutRec name ctrArgs =>
    let shortName := name.componentsRev.head?.getD name |>.toString
    s!"⟳ {shortName} {" ".intercalate (ctrArgs.map ppConstructorExpr)}"
  | Source.NonRec hyp => ppHypothesisExpr hyp

def ppPattern pat := ppConstructorExpr (constructorExprOfPattern pat)

/-- Stringifier for `step` -/
def ppStep step := match step with
    | ScheduleStep.Unconstrained name src _ => s!"{name} ← {ppSource src}"
    | .SuchThat vars src _ =>
      let varNames := vars.map (fun (n : Name × Option ConstructorExpr) => ToString.toString n.1)
      s!"[{", ".intercalate varNames}] ← {ppSource src}"
    | .Check src true => s!"check {ppSource src}"
    | .Check src false => s!"check ¬({ppSource src})"
    | .Match _ name pattern => s!"match {name} with {ppPattern pattern}"

/-- Stringifier for lists of steps (without conclusion). -/
def ppScheduleSteps (steps : List ScheduleStep) := "do\n    " ++ String.intercalate "\n    " (ppStep <$> steps)

/-- Quality score for a generator schedule. Lower is better (ordered lexicographically).
    A schedule with fewer checks is preferred; among equal check counts, shorter is better;
    among equal lengths, fewer unconstrained (arbitrary) bindings is better. -/
structure ScheduleScore where
  checks : Nat
  length : Nat
  unconstrained : Nat
  deriving Ord, Repr

def scheduleStepsScore (schedule : List ScheduleStep) : ScheduleScore :=
  Id.run do
    let mut checks := 0
    let mut length := 0
    let mut unconstrained := 0
    for step in schedule do
      length := length + 1
      match step with
      | .Check .. => checks := checks + 1
      | .Unconstrained .. => unconstrained := unconstrained + 1
      | _ => ()
    ⟨checks, length, unconstrained⟩

instance : LT ScheduleScore := ltOfOrd

def scheduleLT (a b : List ScheduleStep) := scheduleStepsScore a < scheduleStepsScore b

/-- A schedule is a pair consisting of an ordered list of `ScheduleStep`s,
    and the sort of schedule we're dealing with (the latter is the "conclusion" of the schedule) -/
abbrev Schedule := List ScheduleStep × ScheduleSort

/-- Stringifier for a full schedule (steps + conclusion). -/
def ppSchedule (schedule : Schedule) : String :=
  let (steps, sort) := schedule
  let stepsStr := String.intercalate "\n    " (ppStep <$> steps)
  let conclusionStr := match sort with
    | .ProducerSchedule _ conclusion =>
      let outputStr := match conclusion with
        | [e] => ppConstructorExpr e
        | es => s!"({String.intercalate ", " (es.map ppConstructorExpr)})"
      s!"\n    return {outputStr}"
    | .CheckerSchedule => s!"\n    return ok"
    | .TheoremSchedule hyp _ => s!"\n    check_conclusion {ppHypothesisExpr hyp}"
  s!"do\n    {stepsStr}{conclusionStr}"

/-- Each `ScheduleStep` is associated with a `Density`, which represents a failure mode of a generator -/
inductive Density
  /-- Invokes a call to a checker -/
  | Checking

  /-- A call to `ArbitrarySuchThat`, followed by a pattern-match on the generated value
      (this happens when we want the output of the generator to have a certain shape) -/
  | Backtracking

  /-- a call to `ArbitrarySuchThat` ??? -/
  | Partial

  /-- Unconstrained generation, i.e. calls to `arbitrary` -/
  | Total
  deriving Repr, BEq

/-- Converts a `HypothesisExpr` to a `TSyntax term` -/
def hypothesisExprToTSyntaxTerm (hypExpr : HypothesisExpr) : MetaM (TSyntax `term) := do
  let (ctorName, ctorArgs) := hypExpr
  if ctorName = `sort then `(Sort _) else
  let ctorArgTerms ← ctorArgs.toArray.mapM constructorExprToTSyntaxTerm
  `($(mkIdent ctorName) $ctorArgTerms:term*)

mutual

/-- Converts an `Expr` to a `ConstructorExpr` ("classifying" the `Expr`: deciding
    which `ConstructorExpr` variant — variable, constructor, type constructor,
    function application, literal, etc. — corresponds to it). -/
partial def exprToConstructorExpr (e : Expr) : MetaM ConstructorExpr := do
  match e with
  | .fvar id =>
    let localDecl ← FVarId.getDecl id
    return ConstructorExpr.Unknown localDecl.userName
  | .const name _ =>
    -- Check if this is a constructor
    let env ← getEnv
    if env.isConstructor name then
      return ConstructorExpr.Ctor name []
    else if (← isInductive name) then
      return .TyCtor name []
    else
      return .FuncApp name []
  | .app .. => do
    -- Classify the application head, then its arguments. We process arguments
    -- positionally (rather than via the application spine) so we can consult
    -- each argument's binder info: an argument in an implicit or
    -- instance-implicit position that cannot itself be classified (e.g. the
    -- `GetElem?` validity lambda `fun as i => i < as.length`) is replaced by a
    -- hole, since it is inferable from the explicit arguments. Arguments in
    -- explicit positions must still classify, as before.
    let headExpr ← exprToConstructorExpr e.getAppFn
    let argExprs ← classifyAppArgs e
    match headExpr with
    | .TyCtor name args => return .TyCtor name (args ++ argExprs)
    | .Ctor name args => return .Ctor name (args ++ argExprs)
    | .FuncApp name args => return .FuncApp name (args ++ argExprs)
    | .Unknown name =>
      throwError m!"exprToConstructorExpr: We do not support higher order application of {name} in Expr {e}"
    | .Lit _ =>
      throwError m!"exprToConstructorExpr: String and Nat Literals cannot be applied as functions, see: {e.getAppFn} in {e}"
    | .CSort _lvl =>
      throwError m!"exprToConstructorExpr: String and Nat Literals cannot be applied as functions, see: {e.getAppFn} in {e}"
    | .Hole =>
      -- Unreachable: `exprToConstructorExpr` never yields a hole for an
      -- application head (holes only arise for implicit/instance *arguments*
      -- in `classifyAppArgs`). A hole applied as a function is nonsensical.
      throwError m!"exprToConstructorExpr: a hole cannot be applied as a function, see: {e.getAppFn} in {e}"
  | .lit l => return .Lit l
  | .sort lvl => return .CSort lvl
  | .lam .. =>
    -- Check if this lambda is a typeclass instance (e.g., eta-expanded DecidableEq).
    -- If so, treat it as an opaque constant — it will be resolved by typeclass
    -- synthesis in the generated code. Otherwise, reject it.
    let ty ← Meta.inferType e
    let headTy := ty.getForallBody
    if headTy.isApp then
      let className := headTy.getAppFn.constName!
      if Lean.isClass (← getEnv) className then
        return .FuncApp (← Core.mkFreshUserName `inst) []
    throwError m!"exprToConstructorExpr can only handle free variables, constants, and applications. Attempted to convert: {e}"
  | _ =>
    -- For other expression types (literals, lambdas, etc.), generate a placeholder name
    throwError m!"exprToConstructorExpr can only handle free variables, constants, and applications. Attempted to convert: {e}"

/-- Classifies the arguments of an application `e`, one per argument position.

    An argument in an implicit or instance-implicit position that fails to
    classify is replaced by a `.Hole` instead of raising — such arguments are
    always re-inferable from the explicit ones. Arguments in explicit positions
    are classified normally and a failure there is a genuine error (propagated). -/
partial def classifyAppArgs (e : Expr) : MetaM (List ConstructorExpr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let fnType ← Meta.inferType fn
  Meta.forallBoundedTelescope fnType args.size fun bvars _ => do
    let mut result := #[]
    for h : i in [:args.size] do
      let isExplicit ←
        if h' : i < bvars.size then
          pure (← bvars[i].fvarId!.getDecl).binderInfo.isExplicit
        else
          pure true  -- over-application: extra args are explicit
      if isExplicit then
        result := result.push (← exprToConstructorExpr args[i]!)
      else
        -- Implicit/instance position: try to classify, fall back to a hole.
        let ce ← try exprToConstructorExpr args[i]! catch _ => pure .Hole
        result := result.push ce
    return result.toList

end

/-- Converts an `Expr` to a `HypothesisExpr` if it is a variable or application of type constructor or function to constructor expressions else throws.
  We also pass in the current constructor name, as a poor person's location info.
 -/
def exprToHypothesisExpr (ctor : Name) (e : Expr) : MetaM HypothesisExpr := do
  trace[plausible.deriving.arbitrary] m!"Converting {e} to Hypexpr"
  let e ← Lean.Meta.withTransparency .reducible <| Meta.whnf e
  trace[plausible.deriving.arbitrary] m!"Converting {e} to Hypexpr after whnf"
  if e.isApp || e.isConst then
    let (ctorName, args) := e.getAppFnArgs
    let env ← getEnv
    if env.isConstructor ctorName then throwError m!"exprToHypothesisExpr: In constructor {ctor}\nExpr {e} cannot have head term {ctorName} which is a constructor. Must be a function or inductive"
    let constructorArgs ← args.mapM exprToConstructorExpr
    return (ctorName, constructorArgs.toList)
  else if e.isFVar then
    let name ← e.fvarId!.getUserName
    return (name, [])
  else match e with
  | .sort _lvl => return (`sort, [])
  | .proj structName idx expr =>
    -- Structure field projections (e.g., T.Meta) — convert to application form
    let env ← getEnv
    let some info := getStructureInfo? env structName | throwError m!"exprToHypothesisExpr: {structName} is not a structure"
    let fieldName := structName ++ info.fieldNames[idx]!
    let constructorArg ← exprToConstructorExpr expr
    return (fieldName, [constructorArg])
  | _ => throwError m!"exprToHypothesisExpr: In constructor {ctor} Expression\n{e}\nmust be of the form C a1 a2 ... an when used as hypothesis"

/-- Helper function called by `updateSource`, which updates variables in a hypothesis `hyp`
    with the result of unification (provided via the `UnifyM` monad) -/
def updateNonRecSource (k : UnknownMap) (hyp : HypothesisExpr) : UnifyM Source := do
  let (ctorName, args) := hyp
  let updatedName ← UnifyM.findCanonicalUnknown k ctorName
  let updatedArgs ← List.mapM (UnifyM.updateConstructorArg k) args
  return .NonRec (updatedName, updatedArgs)

/-- Updates a `Source` with the result of unification as contained in the `UnknownMap` -/
def updateSource (k : UnknownMap) (src : Source) : UnifyM Source := do
  match src with
  | .NonRec hyp => do
    updateNonRecSource k hyp
  | .Rec r tys => do
    let updatedTys ← List.mapM (UnifyM.updateConstructorArg k) tys
    return .Rec r updatedTys
  | .MutRec r tys => do
    let updatedTys ← List.mapM (UnifyM.updateConstructorArg k) tys
    return .MutRec r updatedTys

/-- Updates a list of `ScheduleSteps` with the result of unification -/
def updateScheduleSteps (scheduleSteps : List ScheduleStep) : UnifyM (List ScheduleStep) := do
  UnifyM.withConstraints $ fun k => scheduleSteps.mapM (fun step =>
    match step with
    | .Match e u p => do
      let updatedScrutinee ← UnifyM.findCanonicalUnknown k u
      let updatedPattern ← UnifyM.updatePattern k p
      return .Match e updatedScrutinee updatedPattern
    | .Unconstrained u src producerSort => do
      let updatedUnknown ← UnifyM.findCanonicalUnknown k u
      let updatedSrc ← updateSource k src
      return .Unconstrained updatedUnknown updatedSrc producerSort
    | .SuchThat unknownsAndTypes src dst => do
      let updatedUnknownsAndTypes ← unknownsAndTypes.mapM (fun (u, ty) => do
        let u' ← UnifyM.findCanonicalUnknown k u
        let ty' ← ty.mapM <| UnifyM.updateConstructorArg k
        return (u', ty'))
      let updatedSource ← updateSource k src
      return .SuchThat updatedUnknownsAndTypes updatedSource dst
    | .Check src polarity => do
      let updatedSrc ← updateSource k src
      return .Check updatedSrc polarity)

/-- Takes the `patterns` and `equalities` fields from `UnifyState` (which are created after
    the conclusion of a constructor has been unified with the top-level arguments to the inductive relation),
    converts them to the appropriate `ScheduleStep`s, and prepends them to the `currentSchedule`.

    - The intuition for prepending these newly-created steps to the existing schedule is that we want to
      make sure all the equalities & pattern-matches needed for the conclusion hold before
      processing the rest of the schedule. -/
def addConclusionPatternsAndEqualitiesToSchedule (patterns : List (Unknown × Pattern)) (equalities : Std.HashSet (Unknown × Unknown)) (currentSchedule : Schedule) : Schedule :=
  let (existingScheduleSteps, scheduleSort) := currentSchedule
  let matchSteps := (Function.uncurry (ScheduleStep.Match .allowImplicit)) <$> patterns
  -- We should never have an equality here. Assertion after unification should handle that though.
  let equalityCheckSteps := (fun (u1, u2) => ScheduleStep.Check (Source.NonRec (``Eq, [.Unknown u1, .Unknown u2])) true) <$> equalities.toList
  (matchSteps ++ equalityCheckSteps ++ existingScheduleSteps, scheduleSort)

/-- Extracts all variable names from a ConstructorExpr (looks inside constructors) -/
partial def varsInConstructorExpr : ConstructorExpr → List Name
  | .Unknown u => [u]
  | .Ctor _ args | .FuncApp _ args | .TyCtor _ args => args.flatMap varsInConstructorExpr
  | .Lit _ | .CSort _ | .Hole => []

/-- Computes output indices: position i is an output if any output variable appears in it -/
def computeOutputIndicesForRewrite (hypArgs : List ConstructorExpr) (outputVarNames : List Name) : List Nat :=
  filterMapWithIndex (fun i arg =>
    let vars := varsInConstructorExpr arg
    if vars.any (· ∈ outputVarNames) then some i else none) hypArgs

/-- Rewrites `Source.NonRec` calls in schedule steps to `Source.MutRec` when the hypothesis
    matches a sibling spec exactly (same inductive, same output positions, same derive sort).
    `siblings` is `(inductiveName, outputIndices, auxFnName, siblingDeriveSort)`. -/
def rewriteMutualCalls (steps : List ScheduleStep) (siblings : List (Name × List Nat × Name × DeriveSort)) : List ScheduleStep :=
  let matchesSibling (hyp : HypothesisExpr) (outNames : List Name) (stepDeriveSort : DeriveSort) : Option (Name × List Nat) :=
    let (hypName, hypArgs) := hyp
    let stepOutputIdxs := computeOutputIndicesForRewrite hypArgs outNames
    siblings.findSome? fun (indName, sibOutputIdxs, auxName, sibSort) =>
      if hypName == indName && stepOutputIdxs == sibOutputIdxs && stepDeriveSort == sibSort then
        some (auxName, sibOutputIdxs)
      else none
  steps.map fun step =>
    match step with
    | .SuchThat vs (.NonRec hyp) ps =>
      let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
      match matchesSibling hyp (vs.map Prod.fst) ds with
      | some (auxName, outputIdxs) =>
        let (_, hypArgs) := hyp
        let inputArgs := filterWithIndex (fun i _ => i ∉ outputIdxs) hypArgs
        .SuchThat vs (.MutRec auxName inputArgs) ps
      | none => step
    | .Unconstrained v (.NonRec hyp) ps =>
      let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
      match matchesSibling hyp [v] ds with
      | some (auxName, outputIdxs) =>
        let (_, hypArgs) := hyp
        let inputArgs := filterWithIndex (fun i _ => i ∉ outputIdxs) hypArgs
        .Unconstrained v (.MutRec auxName inputArgs) ps
      | none => step
    | .Check (.NonRec hyp) pol =>
      match matchesSibling hyp [] .Checker with
      | some (auxName, _) =>
        let (_, hypArgs) := hyp
        .Check (.MutRec auxName hypArgs) pol
      | none => step
    | other => other

/-- Identifies a unique derivation spec (inductive + output mode + sort). -/
structure SpecKey where
  inductiveName : Name
  outputIndices : List Nat
  deriveSort : DeriveSort
  deriving Repr, BEq, Hashable, Inhabited

/-- Pretty-prints a SpecKey as a spec form like "fun τ => ∃ Γ e, typing Γ e τ".
    Requires knowing the inductive's arg types (number of args). -/
def SpecKey.prettyPrint (key : SpecKey) (numArgs : Nat)
    (constraints : Array Name := #[]) (typeParamIndices : Array Nat := #[]) : String :=
  let varPool := #["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"]
  let (inputs, outputs, appArgs) := Id.run do
    let mut inputs : List String := []
    let mut outputs : List String := []
    let mut appArgs : List String := []
    for i in List.range numArgs do
      let name := varPool.getD i s!"v{i}"
      if i ∈ key.outputIndices then
        outputs := outputs ++ [name]
      else
        inputs := inputs ++ [name]
      appArgs := appArgs ++ [name]
    (inputs, outputs, appArgs)
  let constraintStr := if constraints.isEmpty || typeParamIndices.isEmpty then ""
    else
      let binders := typeParamIndices.toList.flatMap fun i =>
        let varName := varPool.getD i s!"v{i}"
        constraints.toList.map fun c => s!"[{c.getString!} {varName}]"
      s!" {String.intercalate " " binders}"
  let inputsStr := if inputs.isEmpty then "" else s!"fun {String.intercalate " " inputs}{constraintStr} => "
  let outputsStr := if outputs.isEmpty then "" else s!"∃ {String.intercalate " " outputs}, "
  let sortStr := match key.deriveSort with
    | .Generator => "[generator] "
    | .Enumerator => "[enumerator] "
    | .Checker => "[checker] "
    | .Theorem => "[theorem] "
  s!"{sortStr}{inputsStr}{outputsStr}{key.inductiveName} {String.intercalate " " appArgs}"

/-- Score for a derived schedule (used for selecting best schedule). -/
structure SpecScore where
  checks : Nat := 0
  unconstrained : Nat := 0
  backtracking : Nat := 0
  deriving Repr, BEq, Ord

instance : Inhabited SpecScore := ⟨{}⟩

/-- A complete derivation plan for one inductive at one output mode.
    Analogous to QuickChick's `inductive_schedule`. -/
structure InductiveSchedule where
  /-- The spec this schedule is for -/
  key : SpecKey
  /-- Freshened argument names (used in the schedule steps) -/
  argNames : List Name
  /-- The recursive function name used in Source.Rec calls -/
  recFnName : Name
  /-- Per-constructor schedules for non-recursive (base) constructors -/
  baseSchedules : List (Name × Schedule)
  /-- Per-constructor schedules for recursive constructors -/
  recSchedules : List (Name × Schedule)
  /-- Quality score for this derivation (type-erased, from active scoring bundle) -/
  score : Score
  /-- True if this spec already has an instance in the environment (no need to compile) -/
  alreadyExists : Bool := false
  /-- Time taken to derive the full spec (in microseconds, includes dep derivation) -/
  derivationTimeUs : Nat := 0
  /-- Per-constructor stats: (name, time in μs, schedules considered, score) -/
  ctorStats : List (Name × Nat × Nat × Score) := []
  deriving Repr

/-- Result of deriving a schedule, stored in the dependency memo. -/
inductive MemoEntry
  | inProgress  -- derivation started, cycle detection
  | done (indSched : InductiveSchedule)
  | failed (msg : String)
  deriving Repr

/-- Whether a dependency is for a base type (needs Arbitrary/Enum) or a relation
    (needs ArbitrarySizedSuchThat/EnumSizedSuchThat/DecOpt). -/
inductive DepKind
  /-- Unconstrained generation of a base type (needs `Arbitrary` or `Enum`) -/
  | baseType
  /-- Constrained generation from a relation (needs `ArbitrarySizedSuchThat` or `EnumSizedSuchThat`) -/
  | relation
  /-- Checking a relation (needs `DecOpt`) -/
  | checker
  deriving Repr, BEq

/-- A dependency extracted from a schedule: what instance is needed.
    - `kind`: whether this is a base type, constrained relation, or checker
    - `inductiveName`: the type/relation being referenced
    - `hypothesis`: the full hypothesis expression (indName + args)
    - `outputVarNames`: the variables being produced (determines output positions)
    - `outputIndices`: positions in the hypothesis args that are outputs
    - `deriveSort`: the producer sort context (Generator or Enumerator) -/
structure ScheduleDep where
  kind : DepKind
  inductiveName : Name
  hypothesis : HypothesisExpr
  outputVarNames : List Name
  outputIndices : List Nat
  deriveSort : DeriveSort
  deriving Repr, BEq

/-- Computes output indices: which positions in hypArgs are output variables -/
def computeOutputIndices (hypArgs : List ConstructorExpr) (outputVarNames : List Name) : List Nat :=
  filterMapWithIndex (fun i arg =>
    match arg with
    | .Unknown name => if name ∈ outputVarNames then some i else none
    | _ => none) hypArgs

/-- Extracts all `Source.NonRec` dependencies from schedule steps.
    Each dependency tells us what instance is needed: which inductive,
    which argument positions are outputs, and what derive sort. -/
def collectNonRecDeps (steps : List ScheduleStep) : List ScheduleDep :=
  steps.filterMap fun step =>
    match step with
    | .SuchThat vs (.NonRec hyp) ps =>
      let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
      let outNames := vs.map Prod.fst
      some { kind := .relation
             inductiveName := hyp.fst
             hypothesis := hyp
             outputVarNames := outNames
             outputIndices := computeOutputIndices hyp.snd outNames
             deriveSort := ds }
    | .Unconstrained v (.NonRec hyp) ps =>
      let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
      some { kind := .baseType
             inductiveName := hyp.fst
             hypothesis := hyp
             outputVarNames := [v]
             outputIndices := computeOutputIndices hyp.snd [v]
             deriveSort := ds }
    | .Check (.NonRec hyp) _ =>
      some { kind := .checker
             inductiveName := hyp.fst
             hypothesis := hyp
             outputVarNames := []
             outputIndices := []
             deriveSort := .Checker }
    | _ => none

/-- DFS from a root SpecKey through chosen schedules to find all actually-used dependencies. -/
partial def collectUsedDeps (root : SpecKey) (memo : Std.HashMap SpecKey MemoEntry)
    (visited : Std.HashSet SpecKey := {}) : Std.HashSet SpecKey :=
  if visited.contains root then visited
  else
    let visited := visited.insert root
    match memo[root]? with
    | some (.done indSched) =>
      let allSchedules := indSched.baseSchedules ++ indSched.recSchedules
      let deps := allSchedules.flatMap (fun (_, (steps, _)) => collectNonRecDeps steps)
      let relDeps := deps.filter (fun d => d.kind == .relation || d.kind == .checker)
      relDeps.foldl (fun acc dep =>
        let depKey : SpecKey := { inductiveName := dep.inductiveName, outputIndices := dep.outputIndices, deriveSort := dep.deriveSort }
        collectUsedDeps depKey memo acc) visited
    | _ => visited

/-- Given a set of used SpecKeys and the memo, compute SCCs (mutual groups).
    Returns components in topological order (dependencies before dependants). -/
def computeSpecSCC (usedKeys : List SpecKey) (memo : Std.HashMap SpecKey MemoEntry) : List (List SpecKey) :=
  let successors (key : SpecKey) : List SpecKey :=
    match memo[key]? with
    | some (.done indSched) =>
      let allScheds := indSched.baseSchedules ++ indSched.recSchedules
      let deps := allScheds.flatMap (fun (_, (steps, _)) => collectNonRecDeps steps)
      let relDeps := deps.filter (fun d => d.kind == .relation || d.kind == .checker)
      let depKeys := relDeps.map (fun d => SpecKey.mk d.inductiveName d.outputIndices d.deriveSort)
      depKeys.filter (usedKeys.contains ·)
    | _ => []
  Lean.SCC.scc usedKeys successors

/-- Checks if any step in a schedule uses `Source.MutRec`. -/
def scheduleUsesMutualCall (steps : List ScheduleStep) : Bool :=
  steps.any fun step =>
    match step with
    | .Unconstrained _ (.MutRec ..) _ => true
    | .SuchThat _ (.MutRec ..) _ => true
    | .Check (.MutRec ..) _ => true
    | _ => false

/-- Count how many size-consuming calls appear in a constructor's schedule steps.
    Includes self-recursive, mutual-recursive, AND non-recursive calls to the same
    inductive (any mode), since all produce values of the same type and should share
    the size budget. Used for Haskell QuickCheck-style budget splitting: each child
    gets `size / count`. See the "Generating Recursive Data Types" section of the
    QuickCheck manual (www.cse.chalmers.se/~rjmh/QuickCheck/manual_body.html), where a
    binary tree generator passes `n \`div\` 2` to each child so that size bounds the total
    node count. We generalize beyond direct recursion: mutually recursive calls and
    non-recursive calls to the same inductive (with a different mode) also consume the
    budget, since they still use fuel to construct the target output rather than an
    independent dependency. -/
def countSizeConsumingCalls (targetInductive : Name) (steps : List ScheduleStep) : Nat :=
  let isSameInductive (src : Source) : Bool :=
    match src with
    | .Rec .. | .MutRec .. => true
    | .NonRec (indName, _) => indName == targetInductive
  steps.foldl (fun acc step =>
    match step with
    | .Unconstrained _ src _ => if isSameInductive src then acc + 1 else acc
    | .SuchThat _ src _ => if isSameInductive src then acc + 1 else acc
    | .Check src _ => if isSameInductive src then acc + 1 else acc
    | _ => acc) 0

end Schedules
