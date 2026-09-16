import Specimen.DeriveConstrainedProducer
import Specimen.Schedules
import Specimen.Scoring
import Specimen.PatternCoverage

open Lean Elab Term Meta
open Idents Schedules
open Plausible

/-! # Infoview widget for `specimen_test`

Renders the derived theorem schedule, its dependency specs and their generated code as
collapsible HTML for the Lean infoview. Presentation only: nothing here affects which
schedule is chosen or what code is emitted, and `specimen.richOutput` gates the whole thing.
-/

namespace Specimen.Tactic

/-- A styled `span`. -/
private def mkSpan (style : Json) (text : String) : ProofWidgets.Html :=
  .element "span" #[("style", style)] #[.text text]

private def headerStyle : Json := json% {"fontWeight": "bold", "fontSize": "1.2em", "color": "#4fc1ff"}
private def scoreStyle : Json := json% {"color": "#808080", "fontSize": "0.9em"}
private def singletonStyle : Json := json% {"color": "#b5cea8"}
private def srcStyle : Json := json% {"color": "#dcdcaa", "fontWeight": "bold"}
private def dstStyle : Json := json% {"color": "#9cdcfe"}
private def reqStyle : Json := json% {"color": "#c586c0", "fontStyle": "italic"}

/-- Green through red by badness, so a glance at the colour reads as schedule quality. -/
private def scoreToColor (bundle : Scoring.ScorerBundle) (score : Score) : String :=
  let b := bundle.scoreBadness score
  let hue := (1.0 - b) * 120.0
  s!"hsl({Float.toString hue}, 70%, 60%)"

private def specColor (bundle : Scoring.ScorerBundle) (indSched : InductiveSchedule) : String :=
  scoreToColor bundle indSched.score

private def getNumArgs (k : SpecKey) : TermElabM Nat := do
  try pure ((← getComponentsOfArrowType (← getConstInfoInduct k.inductiveName).type).size - 1)
  catch _ => pure k.outputIndices.length

/-- Colour a schedule step by the quality of whatever produces it: a step delegating to a
    derived spec inherits that spec's colour, while steps with no spec get a fixed hue. -/
private def stepColor (bundle : Scoring.ScorerBundle)
    (finalMemo : Std.HashMap SpecKey MemoEntry) (step : ScheduleStep) : String :=
  match step with
  | .Check (.NonRec (name, _)) true =>
    match finalMemo[SpecKey.mk name [] .Checker]? with
    | some (.done depSched) => specColor bundle depSched
    | _ => "hsl(30, 70%, 60%)"
  | .Check _ false => "hsl(0, 70%, 60%)"
  | .Check _ true => "hsl(30, 70%, 60%)"
  | .Unconstrained _ (.NonRec (name, _)) _ =>
    match finalMemo[SpecKey.mk name [] .Generator]? with
    | some (.done depSched) => specColor bundle depSched
    | _ => "hsl(60, 70%, 60%)"
  | .Unconstrained _ _ _ => "hsl(60, 70%, 60%)"
  | .SuchThat vs (.NonRec (name, args)) ps =>
    let outIdxs := computeOutputIndices args (vs.map Prod.fst)
    let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
    match finalMemo[SpecKey.mk name outIdxs ds]? with
    | some (.done depSched) => specColor bundle depSched
    | _ => "hsl(90, 70%, 60%)"
  | .SuchThat _ (.Rec ..) _ | .SuchThat _ (.MutRec ..) _ => "hsl(200, 50%, 60%)"
  | .Match .. => "hsl(120, 40%, 60%)"


/-- One collapsible entry per derived spec, in topological order, each showing its
    constructor scores and the code emitted for it. Also returns the number of dependency
    edges seen, which decides whether the dependency-graph section is worth showing. -/
private def derivedSpecsSection (finalMemo : Std.HashMap SpecKey MemoEntry)
    (usedKeys : Std.HashSet SpecKey) (components : List (List SpecKey))
    (compiledCodeMap : Std.HashMap SpecKey (String × String)) :
    TermElabM (Option ProofWidgets.Html × Nat) := do
  let bundle ← Scoring.getActiveScorerBundle
  let scoreToColor := scoreToColor bundle
  let specColor := specColor bundle
  let stepColor := stepColor bundle finalMemo
  let mut orderItems : Array ProofWidgets.Html := #[]
  let mut totalEdges : Nat := 0
  for comp in components do
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
          -- Per-constructor details with scores
          let allScheds := indSched.baseSchedules ++ indSched.recSchedules
          -- Count edges for dep graph
          let deps := allScheds.flatMap (fun (_, (s, _)) => collectNonRecDeps s)
          let relDeps := deps.filter (fun d => d.kind == .relation || d.kind == .checker)
          let depKeys := relDeps.map (fun d => SpecKey.mk d.inductiveName d.outputIndices d.deriveSort)
            |>.filter (usedKeys.contains ·) |>.eraseDups
          totalEdges := totalEdges + depKeys.length
          let ctorItems : Array ProofWidgets.Html := Id.run do
            let mut items := #[]
            for (ctorName, (ctorSteps, ctorSort)) in allScheds do
              let isBase := indSched.baseSchedules.any (fun (n, _) => n == ctorName)
              let tag := if isBase then "base" else "rec"
              let tagColor := if isBase then json% {"color": "#4ec9b0"} else json% {"color": "#d7ba7d"}
              let (ctorInfoStr, ctorColor) := match indSched.ctorStats.find? (fun (n, _, _, _) => n == ctorName) with
                | some (_, us, count, score) =>
                  let timeStr := if us >= 1000 then s!"{us / 1000}ms" else if us > 0 then s!"{us}μs" else ""
                  let countStr := if count > 1 then s!"{count} considered" else ""
                  let scoreStr := bundle.reprScore score
                  let parts := [timeStr, countStr, scoreStr].filter (· != "")
                  (s!" ({String.intercalate ", " parts})", scoreToColor score)
                | none => ("", scoreToColor bundle.emptyScore)
              let ctorNameStyle := json% {"color": $(ctorColor), "fontWeight": "bold"}
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
              let ctorConcHtml : ProofWidgets.Html := .element "div" #[] #[
                mkSpan (json% {"color": "hsl(120, 70%, 70%)"}) ctorConclusionStr]
              items := items.push (.element "details" #[] #[
                .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
                  mkSpan ctorNameStyle ctorName.getString!,
                  .text " ",
                  mkSpan tagColor s!"[{tag}]",
                  mkSpan scoreStyle ctorInfoStr
                ],
                .element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "6px", "padding": "4px 8px", "background": "#1a1a2e", "borderRadius": "4px", "border": "1px solid #2a2a4a", "whiteSpace": "pre", "fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "0.9em", "lineHeight": "1.5"})]
                  (ctorStepHtmls.push ctorConcHtml)
              ])
            items
          -- Code dropdown
          let codeDropdown : Array ProofWidgets.Html := match compiledCodeMap[k]? with
            | some (defStr, instStr) =>
              let codeStyle := json% {"whiteSpace": "pre-wrap", "fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "0.85em", "lineHeight": "1.4", "padding": "8px", "background": "#0d1117", "borderRadius": "4px", "border": "1px solid #30363d", "overflow": "auto", "maxHeight": "400px"}
              #[.element "details" #[] #[
                .element "summary" #[("style", json% {"cursor": "pointer", "marginTop": "4px", "marginBottom": "2px"})] #[
                  mkSpan (json% {"color": "#79c0ff", "fontSize": "0.9em"}) "📝 generated code"
                ],
                .element "div" #[("style", codeStyle)] #[.text (defStr ++ "\n\n" ++ instStr)]
              ]]
            | none => #[]
          orderItems := orderItems.push (.element "details" #[] #[
            .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
              .text "● ",
              mkSpan specNameStyle (k.prettyPrint numArgs),
              mkSpan scoreStyle s!" ({nCtors} ctors{timeStr}) score: {indScoreStr}"
            ],
            .element "div" #[("style", json% {"marginLeft": "12px"})] (ctorItems ++ codeDropdown)
          ])
      | _ => pure ()
  if orderItems.isEmpty then return (none, totalEdges)
  return (some (.element "details" #[("open", json% true)] #[
      .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginBottom": "6px"})] #[
        .text s!"📋 Derived Specs ({usedKeys.size} total, topological order)"
      ],
      .element "div" #[("style", json% {"marginLeft": "8px"})] orderItems
    ]), totalEdges)

/-- Each derived spec listed with the specs it calls, shown only when there is at least one
    edge to draw. -/
private def depGraphSection (finalMemo : Std.HashMap SpecKey MemoEntry)
    (usedKeys : Std.HashSet SpecKey) (totalEdges : Nat) :
    TermElabM (Option ProofWidgets.Html) := do
  let bundle ← Scoring.getActiveScorerBundle
  let scoreToColor := scoreToColor bundle
  let specColor := specColor bundle
  let mut htmlChildren : Array ProofWidgets.Html := #[]
  if totalEdges > 0 then
    let mut graphItems : Array ProofWidgets.Html := #[]
    for k in usedKeys.toList do
      let nArgs ← getNumArgs k
      let label := k.prettyPrint nArgs
      match finalMemo[k]? with
      | some (.done indSched) =>
        let allScheds := indSched.baseSchedules ++ indSched.recSchedules
        let mut depCtors : Std.HashMap SpecKey (List Name) := {}
        for (ctorName, (ctorSteps, _)) in allScheds do
          let deps := collectNonRecDeps ctorSteps
          let relDeps := deps.filter (fun d => d.kind == .relation || d.kind == .checker)
          for d in relDeps do
            let dk := SpecKey.mk d.inductiveName d.outputIndices d.deriveSort
            if usedKeys.contains dk then
              let existing := depCtors.getD dk []
              if ctorName ∉ existing then
                depCtors := depCtors.insert dk (existing ++ [ctorName])
        if !depCtors.isEmpty then
          let mut dstItems : Array ProofWidgets.Html := #[]
          for (dk, ctors) in depCtors.toList do
            let dkArgs ← getNumArgs dk
            let ctorStr := String.intercalate ", " (ctors.map Name.getString!)
            dstItems := dstItems.push (.element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "3px"})] #[
              mkSpan reqStyle "requires ",
              mkSpan dstStyle (dk.prettyPrint dkArgs),
              .text s!"  via {ctorStr}"
            ])
          graphItems := graphItems.push (.element "details" #[] #[
            .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
              mkSpan srcStyle label,
              mkSpan (json% {"color": "#808080"}) s!" ({depCtors.size} deps)"
            ],
            .element "div" #[] dstItems
          ])
      | _ => pure ()
    htmlChildren := htmlChildren.push (.element "details" #[] #[
      .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginTop": "12px", "marginBottom": "6px"})] #[
        .text s!"📊 Dependency Graph ({totalEdges} edges)"
      ],
      .element "div" #[("style", json% {"marginLeft": "8px", "borderLeft": "2px solid #3c3c3c", "paddingLeft": "12px"})] graphItems
    ])
  return htmlChildren[0]?

/-- The pattern-coverage trie for each derived inductive: how the input space is partitioned
    and which constructors cover each leaf. -/
private def coverageSection (finalMemo : Std.HashMap SpecKey MemoEntry)
    (usedKeys : Std.HashSet SpecKey) : TermElabM (Option ProofWidgets.Html) := do
  let bundle ← Scoring.getActiveScorerBundle
  let scoreToColor := scoreToColor bundle
  let specColor := specColor bundle
  let mut htmlChildren : Array ProofWidgets.Html := #[]
  let mut trieItems : Array ProofWidgets.Html := #[]
  for k in usedKeys.toList do
    match finalMemo[k]? with
    | some (.done indSched) =>
      if indSched.alreadyExists then pure ()
      else
        let nArgs ← getNumArgs k
        let indInfo ← getConstInfoInduct k.inductiveName
        let mut patterns : List (Name × PatternCoverage.CovPattern) := []
        for ctorName in indInfo.ctors do
          let ctorInfo ← getConstInfoCtor ctorName
          let pat ← forallTelescopeReducing ctorInfo.type fun _ conclusion => do
            PatternCoverage.conclusionToCovPattern k.inductiveName conclusion k.outputIndices indInfo.numParams
          patterns := patterns ++ [(ctorName, pat)]
        let numAllArgs := indInfo.numParams + indInfo.numIndices
        let initChildren := (List.range numAllArgs).map fun i =>
          if i ∈ k.outputIndices then PatternCoverage.CovPattern.output else .wild
        let initPat := PatternCoverage.CovPattern.ctr k.inductiveName initChildren
        let tree ← PatternCoverage.coverPatterns patterns initPat
        let leaves := PatternCoverage.collectLeaves tree
        let ctorScores : List (Name × Score) := indSched.ctorStats.map fun (name, _, _, score) => (name, score)
        let mut leafHtmls : Array ProofWidgets.Html := #[]
        for (pat, rules) in leaves do
          let covering := rules.filterMap fun r => ctorScores.find? (fun x => x.1 == r)
          let leafScore := bundle.leafAggregator covering
          let patStr := PatternCoverage.ppCovPattern pat
          let leafColor := scoreToColor leafScore
          if covering.isEmpty then
            leafHtmls := leafHtmls.push (.element "div" #[("style", json% {"marginLeft": "8px", "marginBottom": "4px"})] #[
              mkSpan (json% {"color": "hsl(0, 70%, 60%)"}) s!"{patStr}",
              .element "br" #[] #[],
              mkSpan (json% {"color": "hsl(0, 50%, 50%)", "marginLeft": "16px"}) "UNCOVERED"
            ])
          else
            let ctorItemsHtml : Array ProofWidgets.Html := covering.toArray.map fun (r, s) =>
              let shortName := (r.componentsRev.head?.getD r).toString
              .element "div" #[("style", json% {"marginLeft": "16px"})] #[
                mkSpan (json% {"color": $(scoreToColor s)}) s!"{shortName}: {bundle.reprScore s}"
              ]
            leafHtmls := leafHtmls.push (.element "div" #[("style", json% {"marginLeft": "8px", "marginBottom": "6px"})] (
              #[mkSpan (json% {"color": $(leafColor), "fontWeight": "bold"}) patStr] ++ ctorItemsHtml
            ))
        trieItems := trieItems.push (.element "details" #[] #[
          .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
            mkSpan (json% {"color": $(specColor indSched), "fontWeight": "bold"}) (k.prettyPrint nArgs),
            mkSpan scoreStyle s!" ({leaves.length} leaves, score: {bundle.reprScore indSched.score})"
          ],
          .element "div" #[("style", json% {"marginLeft": "12px", "padding": "4px 0", "fontSize": "0.9em", "fontFamily": "var(--vscode-editor-font-family, monospace)"})] leafHtmls
        ])
    | _ => pure ()
  if !trieItems.isEmpty then
    htmlChildren := htmlChildren.push (.element "details" #[] #[
      .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginTop": "12px", "marginBottom": "6px"})] #[
        .text s!"🌲 Pattern Coverage ({trieItems.size} inductives)"
      ],
      .element "div" #[("style", json% {"marginLeft": "8px", "borderLeft": "2px solid #3c3c3c", "paddingLeft": "12px"})] trieItems
    ])
  return htmlChildren[0]?

/-- Build the infoview widget summarising one `specimen_test` derivation: the theorem's own
    schedule and score, then each dependency spec with its constructor scores and emitted
    code. The first arguments describe the theorem itself; `finalMemo` onwards describe the
    dependencies derived for it. -/
def theoremWidgetHtml
    (steps : List ScheduleStep) (sort : ScheduleSort) (theoremScore : Score)
    (scheduleTimeUs schedulesConsidered : Nat) (theoremCodeStr : String)
    (finalMemo : Std.HashMap SpecKey MemoEntry) (usedKeys : Std.HashSet SpecKey)
    (components : List (List SpecKey))
    (compiledCodeMap : Std.HashMap SpecKey (String × String)) :
    TermElabM MessageData := do
  let bundle ← Scoring.getActiveScorerBundle
  let scoreToColor := scoreToColor bundle
  let specColor := specColor bundle
  let stepColor := stepColor bundle finalMemo
  let mut htmlChildren : Array ProofWidgets.Html := #[]
  -- Title
  htmlChildren := htmlChildren.push (.element "div" #[("style", json% {"marginBottom": "12px"})] #[
    mkSpan headerStyle s!"⚗ specimen_test — {usedKeys.size} derived specs, {components.length} components"
  ])
  -- Theorem schedule section with score, time, code
  let theoremScoreStr := bundle.reprScore theoremScore
  let theoremScoreColor := scoreToColor theoremScore
  let theoremTimeStr := if scheduleTimeUs >= 1000 then s!"{scheduleTimeUs / 1000}ms"
    else if scheduleTimeUs > 0 then s!"{scheduleTimeUs}μs" else ""
  let stepHtmls := steps.toArray.map fun step =>
    ProofWidgets.Html.element "div" #[] #[mkSpan (json% {"color": $(stepColor step)}) (ppStep step)]
  let conclusionStr := match sort with
    | .TheoremSchedule hyp _ => s!"check_conclusion {ppHypothesisExpr hyp}"
    | _ => "?"
  let conclusionHtml : ProofWidgets.Html := .element "div" #[] #[
    mkSpan (json% {"color": "hsl(120, 70%, 70%)"}) conclusionStr]
  let codeStyle := json% {"whiteSpace": "pre-wrap", "fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "0.85em", "lineHeight": "1.4", "padding": "8px", "background": "#0d1117", "borderRadius": "4px", "border": "1px solid #30363d", "overflow": "auto", "maxHeight": "400px"}
  let theoremCodeDropdown : ProofWidgets.Html := .element "details" #[] #[
    .element "summary" #[("style", json% {"cursor": "pointer", "marginTop": "4px", "marginBottom": "2px"})] #[
      mkSpan (json% {"color": "#79c0ff", "fontSize": "0.9em"}) "📝 generated theorem checker"
    ],
    .element "div" #[("style", codeStyle)] #[.text theoremCodeStr]
  ]
  htmlChildren := htmlChildren.push (.element "details" #[("open", json% true)] #[
    .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginBottom": "6px"})] #[
      .text "📋 Theorem Schedule",
      mkSpan scoreStyle s!" ({schedulesConsidered} considered, {theoremTimeStr}) ",
      mkSpan (json% {"color": $(theoremScoreColor)}) s!"score: {theoremScoreStr}"
    ],
    .element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "6px", "padding": "4px 8px", "background": "#1a1a2e", "borderRadius": "4px", "border": "1px solid #2a2a4a", "whiteSpace": "pre", "fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "0.9em", "lineHeight": "1.5"})]
      ((stepHtmls.push conclusionHtml).push theoremCodeDropdown)
  ])
  -- Derived specs section with constructor scores, code dropdowns
  let (specsHtml, totalEdges) ← derivedSpecsSection finalMemo usedKeys components compiledCodeMap
  if let some h := specsHtml then htmlChildren := htmlChildren.push h
  -- Dependency graph section
  if let some h ← depGraphSection finalMemo usedKeys totalEdges then
    htmlChildren := htmlChildren.push h
  -- Pattern coverage trie
  if let some h ← coverageSection finalMemo usedKeys then
    htmlChildren := htmlChildren.push h
  let fullHtml := ProofWidgets.Html.element "div"
    #[("style", json% {"fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "13px", "lineHeight": "1.6", "padding": "8px"})]
    htmlChildren
  let htmlMsg ← Lean.MessageData.ofHtml fullHtml
    s!"specimen_test: {usedKeys.size} derived specs, {components.length} components"
  pure htmlMsg

/-- Render the shrink descent as a collapsible tree: one entry per round, each listing the
    candidate values tried and whether a hypothesis, the conclusion, or nothing rejected them.
    The last round is the fixpoint the descent settled on. -/
def shrinkTreeHtml (shrinkTree : List (String × List (String × String × String))) :
    TermElabM MessageData := do
  let mkSpan (style : Json) (text : String) : ProofWidgets.Html :=
    .element "span" #[("style", style)] #[.text text]
  let mut treeItems : Array ProofWidgets.Html := #[]
  let mut idx : Nat := 0
  for entry in shrinkTree do
    let (tupleStr, diag) := entry
    let isLast := idx == shrinkTree.length - 1
    let headerColor := if isLast then json% {"color": "#4ec9b0", "fontWeight": "bold"}
      else json% {"color": "#dcdcaa"}
    let headerText := if isLast then s!"[fixpoint] ({tupleStr})"
      else s!"[round {idx}] ({tupleStr})"
    let mut diagItems : Array ProofWidgets.Html := #[]
    for diagEntry in diag do
      let (varName, shrunkVal, outcome) := diagEntry
      let outcomeColor := if outcome == "accepted" then "hsl(120, 70%, 60%)"
        else if outcome.startsWith "conclusion" then "hsl(60, 70%, 60%)"
        else "hsl(0, 60%, 60%)"
      diagItems := diagItems.push (.element "div" #[("style", json% {"marginLeft": "16px", "marginBottom": "2px"})] #[
        mkSpan (json% {"color": "#9cdcfe"}) s!"{varName}→{shrunkVal}",
        .text " ",
        mkSpan (json% {"color": $(outcomeColor)}) outcome
      ])
    let isOpen := if idx == 0 then json% true else json% false
    treeItems := treeItems.push (.element "details" #[("open", isOpen)] #[
      .element "summary" #[("style", json% {"cursor": "pointer", "marginBottom": "2px"})] #[
        mkSpan headerColor headerText
      ],
      .element "div" #[("style", json% {"marginLeft": "8px", "borderLeft": "2px solid #3c3c3c", "paddingLeft": "8px"})] diagItems
    ])
    idx := idx + 1
  let fullTreeHtml := ProofWidgets.Html.element "details" #[] #[
    .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginBottom": "6px"})] #[
      .text s!"🔬 Shrink Tree ({shrinkTree.length} rounds)"
    ],
    .element "div" #[("style", json% {"marginLeft": "8px", "fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "0.9em", "lineHeight": "1.5"})] treeItems
  ]
  let shrinkMsg ← Lean.MessageData.ofHtml fullTreeHtml s!"shrink tree ({shrinkTree.length} rounds)"
  pure shrinkMsg

end Specimen.Tactic
