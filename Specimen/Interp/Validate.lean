import Specimen.Interp.Env

/-!
# Validating an `InterpEnv` before running it

`GeneratorCombinators.backtrack` catches every error so it can try the next constructor. That is
what makes derived generators robust, and it is also what would make a *misconfigured* interpreter
indistinguishable from a schedule that simply never succeeds: forget to register one `Arbitrary`
leaf and the run just returns "all branches failed".

So check first. `InterpEnv.check` walks every registered schedule, simulates the binder flow, and
reports each step it could not resolve — missing leaves, unknown recursive functions, unbound
variables, arity mismatches, and step forms outside v1's scope. Nothing here runs a generator or
consumes randomness.
-/

open Lean Schedules

namespace Specimen.Interp

/-- One reason an `InterpEnv` cannot run a schedule. Every issue names the spec and constructor it
    was found in, so the report points at an exact place to fix. -/
inductive InterpIssue where
  /-- An `Unconstrained` step needs a generator for a type nothing is registered for. -/
  | missingArbitrary (spec : SpecKey) (ctor : Name) (renderedTy : String) (headName : Name)
      (target : Name)
  /-- A `SuchThat` step needs a constrained producer for a spec nothing is registered for. -/
  | missingProducer (spec : SpecKey) (ctor : Name) (needed : SpecKey) (rendered : String)
  /-- A `Check` step needs a checker for a relation nothing is registered for. -/
  | missingChecker (spec : SpecKey) (ctor : Name) (relName : Name) (rendered : String)
  /-- An expression applies a function with no registered interpretation. -/
  | missingFunc (spec : SpecKey) (ctor : Name) (fn : Name)
  /-- A recursive or mutual call names a function no registered relation answers to. -/
  | unknownRecFn (spec : SpecKey) (ctor : Name) (fn : Name)
  /-- A step reads a variable that nothing bound — usually a schedule edited out of order. -/
  | unboundVar (spec : SpecKey) (ctor : Name) (variable_ : Name) (context : String)
  /-- A call passes the wrong number of value-level arguments for the callee's input arity. -/
  | arityMismatch (spec : SpecKey) (ctor : Name) (callee : String) (given expected : Nat)
  /-- A step or schedule form v1 does not interpret. -/
  | unsupported (spec : SpecKey) (ctor : Name) (why : String)
  deriving Repr

namespace InterpIssue

/-- The spec an issue was found in. -/
def spec : InterpIssue → SpecKey
  | missingArbitrary s .. | missingProducer s .. | missingChecker s .. | missingFunc s ..
  | unknownRecFn s .. | unboundVar s .. | arityMismatch s .. | unsupported s .. => s

/-- The constructor an issue was found in. -/
def ctor : InterpIssue → Name
  | missingArbitrary _ c .. | missingProducer _ c .. | missingChecker _ c .. | missingFunc _ c ..
  | unknownRecFn _ c .. | unboundVar _ c .. | arityMismatch _ c .. | unsupported _ c .. => c

/-- A one-line description, including the call that fixes it where there is one. -/
def message : InterpIssue → String
  | missingArbitrary _ _ ty head target =>
    s!"no unconstrained generator for `{ty}` (needed to generate '{target}'). Register with \
      `.addArbitrary ``{head} g` or, to distinguish instantiations, `.addArbitraryAt \"{ty}\" g`."
  | missingProducer _ _ needed rendered =>
    s!"no producer for {renderSpecKey needed} (needed for `{rendered}`). Register a schedule with \
      `.addRelation`, or a leaf with `.addProducer`."
  | missingChecker _ _ relName rendered =>
    s!"no checker for '{relName}' (needed to check `{rendered}`). Register with `.addChecker`."
  | missingFunc _ _ fn =>
    s!"no interpretation for function '{fn}'. Register with `.addFunc`."
  | unknownRecFn _ _ fn =>
    s!"call to '{fn}' but no registered relation has that `recFnName`."
  | unboundVar _ _ v ctx =>
    s!"'{v}' is read {ctx} but never bound earlier in the schedule."
  | arityMismatch _ _ callee given expected =>
    s!"call to {callee} passes {given} value argument(s) but it takes {expected}."
  | unsupported _ _ why => why

/-- `spec / ctor: message`, the form used in reports. -/
def render (i : InterpIssue) : String :=
  s!"{renderSpecKey i.spec} / {i.ctor}: {i.message}"

end InterpIssue

/-- Every variable an expression reads. -/
partial def exprVars : ConstructorExpr → List Name
  | .Unknown u => [u]
  | .Ctor _ args | .TyCtor _ args | .FuncApp _ args =>
    args.foldl (fun acc a => acc ++ exprVars a) []
  | _ => []

/-- Every function an expression applies that needs an interpretation registered.

    Type-class dictionaries are excluded, whether nullary (`instLENat`) or applied to nothing but
    other types and dictionaries (`instHMul Nat (instMulNat)`, from reifying `n * n`): those evaluate
    to opaque atoms rather than being called, so registering them would be meaningless. The predicate
    is `Specimen.Interp.isTypeOrDict`, the same one `evalConstructorExpr` uses, so what `check`
    demands and what evaluation demands cannot drift apart. -/
partial def exprFuncs (funcs : FuncTable) : ConstructorExpr → List Name
  | .FuncApp f args =>
    let nested := args.foldl (fun acc a => acc ++ exprFuncs funcs a) []
    if (valueArgs args).all (isTypeOrDict funcs) then nested else f :: nested
  | .Ctor _ args | .TyCtor _ args => args.foldl (fun acc a => acc ++ exprFuncs funcs a) []
  | _ => []

/-- Every variable a pattern binds (the wildcard binds nothing). -/
partial def patternVars : Pattern → List Name
  | .UnknownPattern u => if u == `_ then [] else [u]
  | .CtorPattern _ ps => ps.foldl (fun acc p => acc ++ patternVars p) []
  | .LitPattern _ => []

/-- Checks that every variable and function an expression mentions is available. A bare unknown may
    also resolve to a registered nullary function, which is how `Range`-derived expressions spell
    constants. -/
private def checkExprs (env : InterpEnv) (spec : SpecKey) (ctor : Name) (bound : List Name)
    (context : String) (exprs : List ConstructorExpr) : List InterpIssue :=
  let vars := exprs.foldl (fun acc e => acc ++ exprVars e) []
  let funcs := exprs.foldl (fun acc e => acc ++ exprFuncs env.funcs e) []
  let varIssues := vars.foldl (fun acc v =>
    if bound.contains v || env.funcs.contains v then acc
    else acc ++ [InterpIssue.unboundVar spec ctor v context]) []
  let funcIssues := funcs.foldl (fun acc f =>
    if env.funcs.contains f then acc else acc ++ [InterpIssue.missingFunc spec ctor f]) []
  varIssues ++ funcIssues

/-- The value-level input arity a registered spec expects, if it is registered. -/
private def inputArity? (env : InterpEnv) (key : SpecKey) : Option Nat :=
  (env.relations[key]?).map (fun rel => rel.inputPositions.length)

/-- Checks a recursive or mutual call: the callee must be registered, and the call must pass the
    right number of value-level arguments. -/
private def checkCall (env : InterpEnv) (spec : SpecKey) (ctor : Name) (bound : List Name)
    (context : String) (f : Name) (args : List ConstructorExpr) : List InterpIssue :=
  let argIssues := checkExprs env spec ctor bound context (valueArgs args)
  match env.keyOfFn? f with
  | none => argIssues ++ [.unknownRecFn spec ctor f]
  | some key =>
    match inputArity? env key with
    | some n =>
      let given := (valueArgs args).length
      if given == n then argIssues
      else argIssues ++ [.arityMismatch spec ctor s!"'{f}' ({renderSpecKey key})" given n]
    | none => argIssues

/-- Checks one constructor's schedule, threading the set of bound variables through the steps. -/
private def checkSchedule (env : InterpEnv) (rel : RelSchedule) (ctor : Name) (sched : Schedule) :
    List InterpIssue :=
  let spec := rel.key
  let (steps, sort) := sched
  let rec go (bound : List Name) (steps : List ScheduleStep) : List InterpIssue :=
    match steps with
    | [] =>
      match sort with
      | .ProducerSchedule _ outputs =>
        checkExprs env spec ctor bound "in the constructor's conclusion" outputs
      -- A checker's conclusion holds nothing to evaluate: reaching it is the verdict.
      | .CheckerSchedule => []
      | .TheoremSchedule .. =>
        [.unsupported spec ctor "theorem schedule; the interpreter covers generators, enumerators \
          and checkers"]
    | step :: rest =>
      match step with
      | .Unconstrained v src ps =>
        match src with
        | .NonRec hyp =>
          -- Which leaf table answers this depends on the producer sort: a generator step wants an
          -- `Arbitrary`, an enumerator step wants an `Enum`.
          let issues :=
            if ps == .Enumerator then
              if (env.lookupEnum hyp).isSome then []
              else [InterpIssue.missingArbitrary spec ctor (ppHypothesisExpr hyp) hyp.1 v]
            else
              if (env.lookupArbitrary hyp).isSome then []
              else [InterpIssue.missingArbitrary spec ctor (ppHypothesisExpr hyp) hyp.1 v]
          issues ++ go (bound ++ [v]) rest
        | .Rec f args | .MutRec f args =>
          checkCall env spec ctor bound s!"in the call producing '{v}'" f args
            ++ go (bound ++ [v]) rest
      | .SuchThat varsTys src ps =>
        let vars := varsTys.map Prod.fst
        let sortIssues : List InterpIssue := []
        match src with
        | .NonRec hypExpr =>
          let (relName, args) := hypExpr
          let rendered := ppHypothesisExpr hypExpr
          let context := s!"in the constraint `{rendered}`"
          -- Output positions are the arguments that *mention* one of `vars`, matching
          -- `Schedules.computeOutputIndicesForRewrite` and `Specimen.Interp.splitHypothesis`.
          let outputIdxs := args.zipIdx.foldl (fun acc (a, i) =>
            match (varsInConstructorExpr a).find? (fun u => vars.contains u) with
            | some u => if !acc.any (fun (_, u') => u' == u) then acc ++ [(i, u)] else acc
            | none => acc) []
          let missing := vars.filter (fun v => !outputIdxs.any (fun (_, u) => u == v))
          let missingIssues := if missing.isEmpty then [] else
            [InterpIssue.unsupported spec ctor
              s!"{missing} are produced by `{rendered}` but do not appear as arguments of it, so \
                their output position is unknown"]
          -- The callee's type and instance positions are skipped too, exactly as `splitHypothesis`
          -- skips them, so the arity checked below is the arity the call will pass.
          let typeIdx := env.typeArgIndicesOf relName
          let inputExprs := args.zipIdx.filterMap (fun (a, i) =>
            if outputIdxs.any (fun (j, _) => j == i) || typeIdx.contains i || isTypeLevel a then none
            else some a)
          let inputIssues := checkExprs env spec ctor bound context inputExprs
          let depIssues :=
            if relName == ``Eq then
              if outputIdxs.length == 1 && inputExprs.length ≥ 1 then []
              else [InterpIssue.unsupported spec ctor
                s!"cannot solve `{rendered}` for {vars}: the built-in equality producer needs \
                  exactly one unknown side and one known side"]
            else
              -- The dependency's sort follows the step's: an enumerator step needs an enumerator.
              let depSort := if ps == .Enumerator then DeriveSort.Enumerator else .Generator
              -- `typeArgs` must match what `stepDepKey?` records, or a monomorphised callee that *was*
              -- derived looks missing: the two keys would differ only in the instantiation.
              let key : SpecKey :=
                { inductiveName := relName, outputIndices := outputIdxs.map Prod.fst,
                  deriveSort := depSort, typeArgs := renderedTypeArgs (relName, args) }
              match env.relations[key]? with
              | some callee =>
                -- Existence is not enough: the call must pass what the callee binds. Without this,
                -- `check` reported Cedar's closure clean while every `MapNotContainsKey` producer call
                -- handed its callee an instance dictionary as an extra input and died in `bindInputs`.
                let expected := callee.inputPositions.length
                if inputExprs.length == expected then []
                else [InterpIssue.arityMismatch spec ctor s!"{renderSpecKey key} (for `{rendered}`)"
                  inputExprs.length expected]
              | none =>
                if (env.producers[key]?).isSome || (env.enumProducers[key]?).isSome then []
                else [InterpIssue.missingProducer spec ctor key rendered]
          sortIssues ++ missingIssues ++ inputIssues ++ depIssues ++ go (bound ++ vars) rest
        | .Rec f args | .MutRec f args =>
          sortIssues ++ checkCall env spec ctor bound s!"in the call producing {vars}" f args
            ++ go (bound ++ vars) rest
      | .Check src _ =>
        match src with
        | .NonRec hypExpr =>
          let (relName, args) := hypExpr
          let rendered := ppHypothesisExpr hypExpr
          -- What the checker will be handed: `checkSource`/`checkSourceIn` drop the relation's type
          -- and instance positions, not only what is syntactically type-level.
          let given := valueArgsAt (env.typeArgIndicesOf relName) args
          let argIssues :=
            checkExprs env spec ctor bound s!"in the check `{rendered}`" given
          -- Keyed with the instantiation, as `checkSourceIn` looks it up. A polymorphic relation's
          -- checker is registered as e.g. `MapNotContainsKey[]@(0:Attr, …)`; the bare key missed it, so
          -- `check` demanded a leaf for a checker the closure had derived, and never saw its arity.
          let checkerKey : SpecKey :=
            { inductiveName := relName, outputIndices := [], deriveSort := .Checker,
              typeArgs := renderedTypeArgs hypExpr }
          let checkerIssues :=
            if relName == ``Eq || relName == ``Ne then []
            else
              match env.relations[checkerKey]? with
              | some callee =>
                let expected := callee.inputPositions.length
                let arity :=
                  if given.length == expected then []
                  else [InterpIssue.arityMismatch spec ctor
                    s!"{renderSpecKey checkerKey} (for `{rendered}`)" given.length expected]
                -- A *generator*'s `Check` runs through `checkSource`, which reads only name-keyed leaves
                -- (`env.checkers`); a derived checker mode reaches it only once
                -- `publishInterpretedCheckers` has registered it as one. Checker and enumerator schedules
                -- go through `checkSourceIn`, which does read `env.relations`. Accepting the mode here for
                -- a generator reported "resolved" for a check that then failed every attempt at run time —
                -- absorbed by `backtrack` as an ordinary discard.
                let unpublished :=
                  if spec.deriveSort == .Generator && !env.checkers.contains relName then
                    [InterpIssue.missingChecker spec ctor relName rendered]
                  else []
                arity ++ unpublished
              | none =>
                if env.checkers.contains relName then []
                else [InterpIssue.missingChecker spec ctor relName rendered]
          argIssues ++ checkerIssues ++ go bound rest
        | .Rec f args | .MutRec f args =>
          let argIssues :=
            checkExprs env spec ctor bound s!"in the recursive check via '{f}'" (valueArgs args)
          let checkerIssues :=
            -- A recursive check resolves through `byFn` to this relation's own checker mode.
            if env.checkers.contains f then []
            else match env.keyOfFn? f with
              | some k => if k.deriveSort == .Checker then [] else
                  [InterpIssue.unsupported spec ctor
                    s!"checks via '{f}', which names a {repr k.deriveSort}, not a checker"]
              | none => [InterpIssue.unknownRecFn spec ctor f]
          argIssues ++ checkerIssues ++ go bound rest
      | .Match _ scrutinee pattern =>
        let scrutIssues :=
          if bound.contains scrutinee then []
          else [InterpIssue.unboundVar spec ctor scrutinee "as a match scrutinee"]
        scrutIssues ++ go (bound ++ patternVars pattern) rest
  go rel.inputNames steps

/-- Every reason this environment cannot run one of its registered schedules. An empty list means
    every step resolves; it does *not* promise the schedules are productive. -/
def InterpEnv.check (env : InterpEnv) : List InterpIssue :=
  env.relations.toList.foldl (fun acc (_, rel) =>
    let sortIssue :=
      if rel.key.deriveSort == .Theorem then
        [InterpIssue.unsupported rel.key .anonymous
          "spec derives a Theorem; the interpreter covers generators, enumerators and checkers"]
      else []
    let argIssue :=
      if rel.argNames.length ≥ rel.key.outputIndices.length then []
      else [InterpIssue.unsupported rel.key .anonymous
        s!"{rel.argNames.length} argument name(s) but output indices {rel.key.outputIndices}"]
    -- Callers decide which argument positions carry no value from the relation's *name*
    -- (`typeArgIndicesOf`, filled from whichever mode was registered with them). That is only sound if
    -- every mode of the relation agrees; a mode registered with different positions would bind its inputs
    -- against one layout while its callers pass another — an arity or misalignment error that
    -- `backtrack` would otherwise absorb as a discard.
    let recorded := env.typeArgIndicesOf rel.key.inductiveName
    let positionIssue :=
      if rel.typeArgIndices == recorded || (rel.typeArgIndices.isEmpty && recorded.isEmpty) then []
      else [InterpIssue.unsupported rel.key .anonymous
        s!"registered with type/instance positions {rel.typeArgIndices}, but its callers drop \
          {recorded} (every mode of a relation must agree; see `typeArgIndicesOf`)"]
    acc ++ sortIssue ++ argIssue ++ positionIssue
      ++ rel.allSchedules.foldl (fun a (c, s) => a ++ checkSchedule env rel c s) []) []

/-- A human-readable validation report: either a confirmation line, or one line per issue. -/
def InterpEnv.checkReport (env : InterpEnv) : String :=
  match env.check with
  | [] =>
    let n := env.relations.size
    s!"[interp] ok: {n} relation(s) registered, every step resolves"
  | issues =>
    let lines := issues.map (fun i => s!"  • {i.render}")
    s!"[interp] {issues.length} issue(s):\n" ++ "\n".intercalate lines

/-- `Except`-flavoured validation, for use before a run: `.ok ()` or the full report. -/
def InterpEnv.validate (env : InterpEnv) : Except String Unit :=
  match env.check with
  | [] => .ok ()
  | _ => .error env.checkReport

end Specimen.Interp
