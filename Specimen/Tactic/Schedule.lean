import Specimen.DeriveConstrainedProducer
import Specimen.DeriveSchedules
import Specimen.MExp
import Specimen.Schedules
import Specimen.Scoring
import Specimen.Debug
import Specimen.Utils

open Lean Elab Term Meta
open Idents Schedules MExp
open Plausible

/-! # Scheduling and compiling a theorem statement

A proposition `∀ x₁ … xₙ, H₁ → … → Hₘ → C` is scheduled as if it were a single constructor
whose conclusion is `C` and whose premises are the `Hᵢ`, with every bound variable an output.
That reuses the ordinary schedule search, so the hypotheses are ordered to generate witnesses
rather than merely to check them.

`compileTheoremDef` lowers the resulting schedule to a `Gen` returning both the conclusion's
verdict and the tuple of generated variables, so a failing run can report its counterexample.
-/

namespace Specimen.Tactic

/-- Splits the body of a universally quantified proposition into
    hypotheses (non-dependent arrow targets) and a conclusion.
    Given `H₁ → H₂ → ... → C`, returns `([H₁, H₂, ...], C)`.
    Stops at the first non-arrow. -/
private def splitImplications (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut hyps : Array Expr := #[]
  let mut current := e
  while current.isArrow do
    hyps := hyps.push current.bindingDomain!
    current := current.bindingBody!
  return (hyps, current)

/-- Gets a schedule for a theorem goal, treating it as a virtual constructor.
    All variables are outputs — there are no inputs. -/
def getTheoremSchedule (theoremType : Expr)
    (depMemo : Std.HashMap SpecKey MemoEntry := {})
    (memoRef : Option (IO.Ref (Std.HashMap SpecKey MemoEntry)) := none)
    (deriveDep : SpecKey → MetaM Unit := fun _ => pure ())
    : TermElabM (Option (List ScheduleStep × ScheduleSort × List (Name × Expr) × Nat × Score)) := do
  forallTelescopeReducing theoremType (cleanupAnnotations := true) fun binders body => do
    let bindersWithTypes ← binders.mapM fun fvar => do
      let localDecl := (← getLCtx).get! fvar.fvarId!
      let userName := localDecl.userName
      if not userName.hasMacroScopes || localDecl.binderInfo == .instImplicit then
        return (some userName, localDecl.type)
      else
        return (none, localDecl.type)

    let forAllVars := bindersWithTypes.toList.filterMap fun (nameOpt, ty) =>
      match nameOpt with
      | some name => some (name, ty)
      | none => none

    let hypotheses := bindersWithTypes.filterMap fun (nameOpt, tyExpr) =>
      match nameOpt with
      | none => some tyExpr
      | some _ => none

    let (extraHyps, conclusion) ← splitImplications body
    let allHypotheses := hypotheses ++ extraHyps

    let localCtx ← getLCtx
    let localInstances ← getLocalInstances

    let result ← UnifyM.runInMetaM (do
      -- For theorems: skip linearizeAndFlatten on the theorem itself.
      -- The conclusion is checked directly (not generated), so function calls
      -- like `n + 6` can be evaluated in place — no need to introduce fresh vars.
      -- (Sub-relation derivations still use linearizeAndFlatten via deriveBestInductiveSchedule.)
      withLCtx localCtx localInstances do
        let hypothesisExprs ← monadLift <| allHypotheses.toList.mapM (exprToHypothesisExpr `theorem)
        let conclusionExpr ← monadLift <| exprToHypothesisExpr `theorem conclusion

        let inputNames : List Name := []
        let initialUnifyState := mkCheckerInitialUnifyState inputNames forAllVars hypothesisExprs

        let unknowns : Array Name := forAllVars.toArray.map Prod.fst
        let updatedForAllVars := forAllVars

        UnifyM.extendState initialUnifyState
        let _ ← unknowns.mapM processCorrespondingRange

        let scheduleSort : ScheduleSort := .TheoremSchedule conclusionExpr (typeClassUsed := true)
        let fixedVars : List Name := []
        let updatedForAllVarsTyped := updatedForAllVars.map fun (n, ty) => TypedVar.mk n ty
        let multiOutput := Lean.Option.get (← getOptions) specimen.multiOutput
        let bundle ← Scoring.getActiveScorerBundle
        let key : SpecKey := { inductiveName := `_theorem, outputIndices := [], deriveSort := .Theorem }
        let limit := Lean.Option.get (← getOptions) specimen.searchLimit
        let delegableMap : Schedules.DelegableMap := []

        if bundle.usesMonadicPath && memoRef.isSome then
          match memoRef with
          | none => unreachable!
          | some ref => do
            let result ← monadLift <| searchBestScheduleM
              (ctorName := `theorem) (vars := updatedForAllVarsTyped)
              (hypotheses := hypothesisExprs) (deriveSort := .Theorem)
              (recCall := (`_theorem, [])) (fixedVars := fixedVars)
              (recFnName := `_theorem_rec)
              (multiOutput := multiOutput) (bundle := bundle) (memo := ref)
              (key := key) (limit := limit) (deriveDep := deriveDep)
              (delegableMap := delegableMap)
            match result with
            | some (steps, score, count) =>
              let updatedSteps ← updateScheduleSteps steps
              let finalState ← get
              let finalSchedule := addConclusionPatternsAndEqualitiesToSchedule
                finalState.patterns finalState.equalities (updatedSteps, scheduleSort)
              return some (finalSchedule.fst, finalSchedule.snd, forAllVars, count, score)
            | none => return none
        else
          let possibleSchedules := possibleSchedules
            (vars := updatedForAllVarsTyped)
            (hypotheses := hypothesisExprs)
            `theorem .Theorem (`_theorem, []) fixedVars `_theorem_rec multiOutput delegableMap
          match possibleSchedules with
          | .lnil => return none
          | .lcons fstSchdM rest => do
            let (fstSchd, _) ← fstSchdM
            let inputVarSet : Std.HashSet Name := {}
            let scoreSchedule := fun (steps : List ScheduleStep) => do
              let stepScores ← steps.mapM fun step => bundle.stepScorer key depMemo inputVarSet step
              return bundle.scheduleScorer stepScores
            let mut countProcessed := 1
            let mut bestScore ← scoreSchedule fstSchd
            let mut bestSchedule := fstSchd
            for schdM in rest.get do
              let (schd, _) ← schdM
              let score ← scoreSchedule schd
              countProcessed := countProcessed + 1
              if bundle.isBetter score bestScore then
                bestSchedule := schd
                bestScore := score
              if countProcessed > limit then
                break
            let updatedSteps ← updateScheduleSteps bestSchedule
            let finalState ← get
            let finalSchedule := addConclusionPatternsAndEqualitiesToSchedule
              finalState.patterns finalState.equalities (updatedSteps, scheduleSort)
            return some (finalSchedule.fst, finalSchedule.snd, forAllVars, countProcessed, bestScore)
        ) emptyUnifyState
      return result.join

/-- Compiles a theorem schedule into a def that returns `Gen (Except GenError (Bool × α))`
    where `α` is the tuple of the original forAll variables.
    - `Bool` = true means conclusion holds (pass), false means counterexample
    - On pass: `(true, vars)` — we have the values but they're not interesting
    - On fail: `(false, vars)` — counterexample! report `vars`
    - On error: hypothesis failed (discard)

    Uses a custom epilogue that checks the conclusion and bundles the result with the var tuple. -/
def compileTheoremDef (steps : List ScheduleStep) (sort : ScheduleSort)
    (recType : Expr) (defName : Name) (varNames : List Name) (varTypes : List Expr)
    : TermElabM (TSyntax `command) := do
  let fuelPrimeName := `fuel'
  let sizePrimeName := `size'

  -- Build the variable tuple MExp (to return alongside the conclusion result)
  let varMExps := varNames.map (fun n => MExp.MId n)
  let tupleMExp := match varMExps with
    | [] => MExp.MConst ``Unit.unit
    | [v] => v
    | vs => MExp.tupleOfList (fun e1 e2 => .MApp .allowImplicit (.MConst ``Prod.mk) [e1, e2]) vs vs[0]?

  -- Build a custom epilogue that checks the conclusion and returns (Bool × tuple)
  let customEpilogue ← match sort with
    | .TheoremSchedule conclusion typeClassUsed =>
      let conclusionMExp := MExp.hypothesisExprToMExp conclusion
      let scrutinee :=
        if typeClassUsed then MExp.decOptChecker conclusionMExp
          (.MApp .allowImplicit (.MConst ``Nat.mul) [.MLit (.natVal 3), .MApp .allowImplicit (.MConst ``Nat.add) [.MId `size, .MLit (.natVal 1)]])
        else conclusionMExp
      -- match scrutinee with
      -- | .ok true => return (.ok (true, tuple))
      -- | .ok false => return (.ok (false, tuple))
      -- | .error _ => return (.error genericFailure)
      let pairTrue := MExp.MApp .allowImplicit (.MConst ``Prod.mk) [MExp.MConst ``true, tupleMExp]
      let pairFalse := MExp.MApp .allowImplicit (.MConst ``Prod.mk) [MExp.MConst ``false, tupleMExp]
      let okTrue := MExp.MApp .allowImplicit (.MConst ``Except.ok) [pairTrue]
      let okFalse := MExp.MApp .allowImplicit (.MConst ``Except.ok) [pairFalse]
      pure <| MExp.MMatch .allowImplicit scrutinee
        [ (.CtorPattern ``Except.ok [.UnknownPattern ``true], .MRet okTrue)
        , (.CtorPattern ``Except.ok [.UnknownPattern ``false], .MRet okFalse)
        , (.CtorPattern ``Except.error [wildCardPattern], .MRet (.MApp .allowImplicit (.MConst ``Except.error) [.MConst ``Plausible.Gen.genericFailure]))
        ]
    | _ => pure <| MExp.MRet (.MApp .allowImplicit (.MConst ``Except.ok)
        [MExp.MApp .allowImplicit (.MConst ``Prod.mk) [MExp.MConst ``true, tupleMExp]])

  -- Compile steps with the custom epilogue
  let (body, _) ← (do
    let sizeExpr : MExp := .MId sizePrimeName
    let genMExp ← List.foldrM (fun step acc => scheduleStepToMExp step (.MId `initSize) acc recType fuelPrimeName sizeExpr `_theorem)
      customEpilogue steps
    mexpToTSyntax genMExp .Theorem).run #[]

  -- Build tuple type syntax (right-nested to match tupleOfList)
  let varTypeSyntaxes ← varTypes.mapM (fun ty => PrettyPrinter.delab ty)
  let tupleType ← match varTypeSyntaxes with
    | [] => `(Unit)
    | [t] => pure t
    | _ =>
      let rec buildProdType : List (TSyntax `term) → TermElabM (TSyntax `term)
        | [] => `(Unit)
        | [t] => pure t
        | t :: rest => do let r ← buildProdType rest; `($t × $r)
      buildProdType varTypeSyntaxes

  let defIdent := mkIdent defName
  let fuelIdent := mkIdent fuelPrimeName
  let initSizeIdent := mkIdent `initSize
  let sizeIdent := mkIdent `size
  `(private def $defIdent ($fuelIdent : Nat) ($initSizeIdent : Nat) ($sizeIdent : Nat) :
      Plausible.Gen (Except Plausible.GenError (Bool × $tupleType)) :=
    $body)

end Specimen.Tactic
