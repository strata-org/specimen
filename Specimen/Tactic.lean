import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import Specimen.MExp
import Specimen.Schedules
import Specimen.DeriveSchedules
import Specimen.Debug
import Specimen.Utils
import Specimen.TheoremChecker

import Plausible.Tactic

import Lean.Elab.Tactic
import Lean.Elab.Command

open Lean Elab Tactic Meta Term Command
open Idents Schedules Plausible Plausible.Decorations MExp

/-! # The `specimen` tactic

A tactic analogous to QuickChick's `quickchick` tactic.
Given a proof goal of the form `∀ x₁ ... xₙ, H₁ → ... → Hₘ → C`,
it treats the theorem as a virtual constructor where all variables are
outputs (to be generated), uses Specimen's schedule infrastructure
to derive generators/checkers for all transitive dependencies,
compiles a testing function, and runs it.
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
      let outputIndices : List Nat := []
      let (updatedHypotheses, updatedConclusion, freshNamesAndTypes, updatedLocalCtx) ←
        linearizeAndFlatten allHypotheses conclusion outputIndices localCtx

      withLCtx updatedLocalCtx localInstances do
        let hypothesisExprs ← monadLift <| updatedHypotheses.toList.mapM (exprToHypothesisExpr `theorem)
        let conclusionExpr ← monadLift <| exprToHypothesisExpr `theorem updatedConclusion

        let inputNames : List Name := []
        let initialUnifyState := mkCheckerInitialUnifyState inputNames forAllVars hypothesisExprs

        let unknowns : Array Name := forAllVars.toArray.map Prod.fst
        let updatedForAllVars := forAllVars ++ freshNamesAndTypes

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

/-- Compiles a theorem schedule into a `TheoremProperty` definition.
    Produces three components from the same schedule:
    - `generate`: runs the schedule steps (generating vars, checking hypotheses), returns the tuple
    - `checkConclusion`: re-runs the conclusion check on a tuple
    - `validShrinks`: for each var, tries shrink candidates, re-checks hypotheses in order

    `varNames` are the universally-quantified variable names (in order),
    `varTypes` are their elaborated types. -/
def compileTheoremDef (steps : List ScheduleStep) (sort : ScheduleSort)
    (recType : Expr) (defName : Name) : TermElabM (TSyntax `command) := do
  let fuelPrimeName := `fuel'
  let sizePrimeName := `size'
  let (mexp, _instances) ← (MExp.scheduleToMExp (steps, sort) (.MId `size) (.MId `initSize) recType
    (fuelPrimeName := fuelPrimeName) (sizePrimeName := sizePrimeName)
    (targetInductive := `_theorem)).run #[]
  let (body, _) ← (mexpToTSyntax mexp .Theorem).run #[]
  let defIdent := mkIdent defName
  let fuelIdent := mkIdent fuelPrimeName
  let initSizeIdent := mkIdent `initSize
  let sizeIdent := mkIdent `size
  `(private def $defIdent ($fuelIdent : Nat) ($initSizeIdent : Nat) ($sizeIdent : Nat) :
      Plausible.Gen (Except Plausible.GenError Bool) :=
    $body)

/-- The `specimen` command: property-based testing for propositions involving inductive relations.
    Usage: `specimen_test (prop)` where `prop` is a universally-quantified proposition. -/
syntax (name := specimenTestCmd) "specimen_test " term : command

@[command_elab specimenTestCmd]
unsafe def elabSpecimenTest : CommandElab := fun stx => do
  match stx with
  | `(specimen_test $prop:term) => do
    let memo ← IO.mkRef ({} : Std.HashMap SpecKey MemoEntry)

    -- Elaborate the proposition and compute its schedule
    let scheduleResult ← withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
      liftTermElabM do
        let e ← elabTerm prop (some (mkSort .zero))
        let tgt ← instantiateMVars e
        let termElabCtx ← readThe Lean.Elab.Term.Context
        let deriveDep : SpecKey → MetaM Unit := fun depKey => do
          let _ ← (deriveBestInductiveSchedule depKey memo).run termElabCtx
        getTheoremSchedule tgt (memoRef := some memo) (deriveDep := deriveDep)

    match scheduleResult with
    | none => throwError "specimen: unable to compute a testing schedule for this proposition.\n\
        It must be of the form `∀ x₁ ... xₙ, H₁ → ... → Hₘ → C` where\n\
        the hypotheses and conclusion involve inductive relations."
    | some (steps, sort, varNamesTypes, _count, _score) =>
      -- Ensure the conclusion's relation has a DecOpt instance derived
      match sort with
      | .TheoremSchedule (conclusionName, _) true =>
        withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
          liftTermElabM do
            let conclusionKey : SpecKey := { inductiveName := conclusionName, outputIndices := [], deriveSort := .Checker }
            let termElabCtx ← readThe Lean.Elab.Term.Context
            let _ ← (deriveBestInductiveSchedule conclusionKey memo).run termElabCtx
      | _ => pure ()

      let finalMemo ← memo.get
      let directDeps : Array ScheduleDep := (collectNonRecDeps steps).toArray
      let mut usedKeys : Std.HashSet SpecKey := {}
      -- Include the conclusion checker in the used keys
      match sort with
      | .TheoremSchedule (conclusionName, _) true =>
        let conclusionKey : SpecKey := { inductiveName := conclusionName, outputIndices := [], deriveSort := .Checker }
        usedKeys := collectUsedDeps conclusionKey finalMemo usedKeys
      | _ => pure ()
      for dep in directDeps do
        if dep.kind == DepKind.relation || dep.kind == DepKind.checker then
          let depKey : SpecKey := { inductiveName := dep.inductiveName, outputIndices := dep.outputIndices, deriveSort := dep.deriveSort }
          usedKeys := collectUsedDeps depKey finalMemo usedKeys

      -- Emit all dependency instances
      let components := computeSpecSCC usedKeys.toList finalMemo
      for comp in components do
        for key in comp do
          match finalMemo[key]? with
          | some (.done indSched) =>
            if indSched.alreadyExists then continue
            let uid ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_tactic)
            let globalName := Name.mkSimple s!"{uid}_{key.inductiveName.toString.replace "." "_"}"
            let siblings : List (Name × List Nat × Name × DeriveSort) :=
              comp.map (fun (k : SpecKey) =>
                let gn := Name.mkSimple s!"{uid}_{k.inductiveName.toString.replace "." "_"}"
                (k.inductiveName, k.outputIndices, gn, k.deriveSort))
            try
              let (defCmd, instCmd) ← liftTermElabM <|
                compileInductiveSchedule indSched globalName siblings
              elabCommand defCmd
              elabCommand instCmd
            catch e : Exception =>
              logWarning m!"specimen: failed to compile instance for {key.inductiveName}: {e.toMessageData}"
          | _ => pure ()

      -- Emit rich HTML widget showing the theorem schedule + derived dependencies
      -- (reuses the same HTML structure as derive_mutual)
      let richOutput := Lean.Option.get (← getOptions) specimen.richOutput
      if richOutput then
        liftTermElabM do
          let mkSpan (style : Json) (text : String) : ProofWidgets.Html :=
            .element "span" #[("style", style)] #[.text text]
          let headerStyle := json% {"fontWeight": "bold", "fontSize": "1.2em", "color": "#4fc1ff"}
          let schedStyle := json% {"color": "#ce9178", "fontSize": "0.9em", "whiteSpace": "pre", "fontFamily": "var(--vscode-editor-font-family, monospace)"}
          let scoreStyle := json% {"color": "#808080", "fontSize": "0.9em"}
          let singletonStyle := json% {"color": "#b5cea8"}
          let srcStyle := json% {"color": "#dcdcaa", "fontWeight": "bold"}
          let bundle ← Scoring.getActiveScorerBundle
          let scoreToColor (score : Score) : String :=
            let b := bundle.scoreBadness score
            let hue := (1.0 - b) * 120.0
            s!"hsl({Float.toString hue}, 70%, 60%)"
          let specColor (indSched : InductiveSchedule) : String := scoreToColor indSched.score
          let getNumArgs (k : SpecKey) : TermElabM Nat := do
            try pure ((← getComponentsOfArrowType (← getConstInfoInduct k.inductiveName).type).size - 1)
            catch _ => pure k.outputIndices.length
          let mut htmlChildren : Array ProofWidgets.Html := #[]
          -- Title
          htmlChildren := htmlChildren.push (.element "div" #[("style", json% {"marginBottom": "12px"})] #[
            mkSpan headerStyle s!"⚗ specimen_test — {usedKeys.size} derived specs"
          ])
          -- Theorem schedule section
          let stepColor (step : ScheduleStep) : String :=
            match step with
            | .Check (.NonRec (name, _)) true =>
              let depKey := SpecKey.mk name [] .Checker
              match finalMemo[depKey]? with
              | some (.done depSched) => specColor depSched
              | _ => "hsl(30, 70%, 60%)"
            | .Check _ false => "hsl(0, 70%, 60%)"
            | .Check _ true => "hsl(30, 70%, 60%)"
            | .Unconstrained _ (.NonRec (name, _)) _ =>
              let depKey := SpecKey.mk name [] .Generator
              match finalMemo[depKey]? with
              | some (.done depSched) => specColor depSched
              | _ => "hsl(60, 70%, 60%)"
            | .Unconstrained _ _ _ => "hsl(60, 70%, 60%)"
            | .SuchThat vs (.NonRec (name, args)) ps =>
              let outNames := vs.map Prod.fst
              let outIdxs := computeOutputIndices args outNames
              let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
              let depKey := SpecKey.mk name outIdxs ds
              match finalMemo[depKey]? with
              | some (.done depSched) => specColor depSched
              | _ => "hsl(90, 70%, 60%)"
            | .SuchThat _ (.Rec ..) _ | .SuchThat _ (.MutRec ..) _ => "hsl(200, 50%, 60%)"
            | .Match .. => "hsl(120, 40%, 60%)"
          let stepHtmls := steps.toArray.map fun step =>
            let color := stepColor step
            ProofWidgets.Html.element "div" #[] #[mkSpan (json% {"color": $(color)}) (ppStep step)]
          let conclusionStr := match sort with
            | .TheoremSchedule hyp _ => s!"check_conclusion {ppHypothesisExpr hyp}"
            | _ => "?"
          let conclusionHtml := ProofWidgets.Html.element "div" #[] #[
            mkSpan (json% {"color": "hsl(120, 70%, 70%)"}) conclusionStr]
          htmlChildren := htmlChildren.push (ProofWidgets.Html.element "details" #[("open", json% true)] #[
            .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginBottom": "6px"})] #[
              .text "📋 Theorem Schedule"
            ],
            .element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "6px", "padding": "4px 8px", "background": "#1a1a2e", "borderRadius": "4px", "border": "1px solid #2a2a4a", "whiteSpace": "pre", "fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "0.9em", "lineHeight": "1.5"})]
              (stepHtmls.push conclusionHtml)
          ])
          -- Derived specs section (same as derive_mutual's topological order display)
          let components' := computeSpecSCC usedKeys.toList finalMemo
          let mut orderItems : Array ProofWidgets.Html := #[]
          for comp in components' do
            for k in comp do
              let numArgs ← getNumArgs k
              match finalMemo[k]? with
              | some (.done indSched) =>
                if indSched.alreadyExists then
                  orderItems := orderItems.push (.element "div" #[("style", json% {"marginBottom": "2px"})] #[
                    .text "● ", mkSpan singletonStyle (k.prettyPrint numArgs),
                    mkSpan scoreStyle " (pre-existing)"
                  ])
                else
                  let timeStr := if indSched.derivationTimeUs >= 1000 then s!" {indSched.derivationTimeUs / 1000}ms"
                    else if indSched.derivationTimeUs > 0 then s!" {indSched.derivationTimeUs}μs" else ""
                  let nCtors := indSched.baseSchedules.length + indSched.recSchedules.length
                  let specNameStyle := json% {"color": $(specColor indSched), "fontWeight": "bold"}
                  let indScoreStr := bundle.reprScore indSched.score
                  -- Per-constructor schedule details
                  let allScheds := indSched.baseSchedules ++ indSched.recSchedules
                  let ctorItems : Array ProofWidgets.Html := Id.run do
                    let mut items := #[]
                    for (ctorName, (ctorSteps, ctorSort)) in allScheds do
                      let isBase := indSched.baseSchedules.any (fun (n, _) => n == ctorName)
                      let tag := if isBase then "base" else "rec"
                      let tagColor := if isBase then json% {"color": "#4ec9b0"} else json% {"color": "#d7ba7d"}
                      let ctorStepHtmls := ctorSteps.toArray.map fun step =>
                        ProofWidgets.Html.element "div" #[] #[mkSpan (json% {"color": $(stepColor step)}) (ppStep step)]
                      let ctorConclusionStr := match ctorSort with
                        | .ProducerSchedule _ conclusion =>
                          let outputStr := match conclusion with
                            | [e] => ppConstructorExpr e
                            | es => s!"({String.intercalate ", " (es.map ppConstructorExpr)})"
                          s!"return {outputStr}"
                        | .CheckerSchedule => "return ok"
                        | .TheoremSchedule hyp _ => s!"check_conclusion {ppHypothesisExpr hyp}"
                      let ctorConcHtml := ProofWidgets.Html.element "div" #[] #[
                        mkSpan (json% {"color": "hsl(120, 70%, 70%)"}) ctorConclusionStr]
                      items := items.push (ProofWidgets.Html.element "details" #[] #[
                        .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                          mkSpan (json% {"fontWeight": "bold"}) ctorName.getString!,
                          .text " ",
                          mkSpan tagColor s!"[{tag}]"
                        ],
                        .element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "6px", "padding": "4px 8px", "background": "#1a1a2e", "borderRadius": "4px", "border": "1px solid #2a2a4a"})]
                          (ctorStepHtmls.push ctorConcHtml)
                      ])
                    items
                  orderItems := orderItems.push (ProofWidgets.Html.element "details" #[] #[
                    .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                      .text "● ",
                      mkSpan specNameStyle (k.prettyPrint numArgs),
                      mkSpan scoreStyle s!" ({nCtors} ctors{timeStr}) score: {indScoreStr}"
                    ],
                    .element "div" #[("style", json% {"marginLeft": "12px"})] ctorItems
                  ])
              | _ => pure ()
          if !orderItems.isEmpty then
            htmlChildren := htmlChildren.push (ProofWidgets.Html.element "details" #[("open", json% true)] #[
              .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginBottom": "6px"})] #[
                .text s!"📋 Derived Specs ({usedKeys.size} total)"
              ],
              .element "div" #[("style", json% {"marginLeft": "8px"})] orderItems
            ])
          let fullHtml := ProofWidgets.Html.element "div"
            #[("style", json% {"fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "13px", "lineHeight": "1.6", "padding": "8px"})]
            htmlChildren
          let htmlMsg ← Lean.MessageData.ofHtml fullHtml
            s!"specimen_test: {usedKeys.size} derived specs"
          logInfo htmlMsg

      -- Compile the theorem schedule into a checker def
      let defName ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_theorem_checker)
      let defCmd ← withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
        liftTermElabM <| compileTheoremDef steps sort (mkSort .zero) defName
      elabCommand defCmd

      -- Run the test loop using TheoremProperty
      let checkerIdent : TSyntax `term := mkIdent defName
      let testExpr ← liftTermElabM <| `(do
        let mut successes : Nat := 0
        let mut failures : Nat := 0
        let mut discards : Nat := 0
        for i in List.range 100 do
          let size := i + 1
          let genResult ← Plausible.Gen.run (($checkerIdent) size size size) size
          match genResult with
          | .ok true => successes := successes + 1
          | .ok false => failures := failures + 1
          | .error _ => discards := discards + 1
        if failures > 0 then
          throw <| IO.userError s!"specimen: Found {failures} counter-example(s) in {successes + failures + discards} tests ({discards} discarded)"
        else
          IO.println s!"specimen: {successes} tests passed ({discards} discarded)")

      let e ← liftTermElabM <| Term.elabTerm testExpr (some (mkApp (mkConst ``IO) (mkConst ``PUnit [1])))
      let action ← liftTermElabM <| unsafe Lean.Meta.evalExpr (IO PUnit) (mkApp (mkConst ``IO) (mkConst ``PUnit [1])) e
      _ ← action

  | _ => throwUnsupportedSyntax

-- TODO: Add `specimen` tactic that extracts the goal and delegates to `specimen_test`

end Specimen.Tactic
