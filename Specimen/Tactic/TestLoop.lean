import Specimen.Debug
import Specimen.TheoremChecker
import Specimen.LazyList
import Lean.Elab.Command

open Lean Elab Term Command Meta
open Plausible

/-! # The generated test loop

Builds the term `specimen_test` evaluates: a loop that samples the compiled checker over a
ramp of sizes, classifies each run as pass, counterexample, or discard, and on a
counterexample runs the greedy shrink descent before formatting the result.

The loop is emitted as syntax rather than run directly because the checker it calls is a
freshly elaborated definition, so it only exists in the environment being built.
-/

namespace Specimen.Tactic

/-- Build the test-loop term. `checkerIdent`, `shrinksIdent` and `diagIdent` name the three
    definitions emitted for this proposition; sizes ramp from `minSize` to `maxSize` across
    `numTests` runs. `richOutput` also enables collecting the shrink-diagnostic tree, which
    only the infoview widget consumes. Yields
    `IO (message, shrinkCount, shrinkTree)`. -/
def buildTestExpr (varNames : List Name) (varTypes : List Expr)
    (checkerIdent shrinksIdent diagIdent : TSyntax `term)
    (minSize maxSize numTests : Nat) (richOutput : Bool) :
    CommandElabM (TSyntax `term) := do
  -- Build per-variable labels: "  name : Type := " for the error message
  let varTypeSyntaxes ← liftTermElabM <| varTypes.mapM (fun ty => PrettyPrinter.delab ty)
  let varLabels ← liftTermElabM <| (varNames.zip varTypeSyntaxes).mapM fun (n, tySyn) => do
    let tyStr := Format.pretty (← PrettyPrinter.ppTerm tySyn)
    pure s!"  {n} : {tyStr} := "

  -- Build the formatter: for each variable, project from the tuple and repr it
  let cexIdent : TSyntax `term := mkIdent `specimen_cex
  let formatParts ← liftTermElabM <| do
    let mut parts : Array (TSyntax `term) := #[]
    for i in [:varNames.length] do
      let label := Syntax.mkStrLit varLabels[i]!
      let proj ← if varNames.length == 1 then
        pure cexIdent
      else if i == 0 then
        `(($cexIdent).1)
      else
        let mut e := cexIdent
        for _ in [:i - 1] do e ← `(($e).2)
        if i == varNames.length - 1 then
          `(($e).2)
        else
          `(($e).2.1)
      parts := parts.push (← `($label ++ reprStr $proj))
    pure parts
  let nlLit := Syntax.mkStrLit "\n"
  let formatExpr ← liftTermElabM <|
    formatParts.toList.tail!.foldlM (fun acc part => `($acc ++ $nlLit ++ $part)) formatParts[0]!

  -- formatTuple: given tuple, repr each var on its own line
  let formatTupleIdent : TSyntax `term := mkIdent `specimen_fmt_tup
  let fmtTupleParts ← liftTermElabM <| do
    let mut parts : Array (TSyntax `term) := #[]
    for i in [:varNames.length] do
      let label := Syntax.mkStrLit s!"{varNames[i]!}="
      let proj ← if varNames.length == 1 then pure formatTupleIdent
        else if i == 0 then `(($formatTupleIdent).1)
        else
          let mut e := formatTupleIdent
          for _ in [:i - 1] do e ← `(($e).2)
          if i == varNames.length - 1 then `(($e).2) else `(($e).2.1)
      parts := parts.push (← `($label ++ reprStr $proj))
    pure parts
  let fmtTupleBody ← liftTermElabM <| match fmtTupleParts.toList with
    | [] => `("")
    | [x] => pure x
    | x :: rest => do
      let sep := Syntax.mkStrLit ", "
      rest.foldlM (fun acc part => `($acc ++ $sep ++ $part)) x

  -- The test expression now returns (String, Nat, List (String × List (String × String × String)))
  -- = (resultMessage, shrinkCount, shrinkTree)
  -- shrinkTree: for each shrink round, (tupleRepr, diagnostics)
  let minSizeLit := Syntax.mkNumLit (toString minSize)
  let maxSizeLit := Syntax.mkNumLit (toString maxSize)
  let numTestsLit := Syntax.mkNumLit (toString numTests)
  -- Denominator for the size ramp (spread min..max over the test runs; avoid div-by-zero).
  let rampDenomLit := Syntax.mkNumLit (toString (Nat.max 1 (numTests - 1)))
  -- Only collect the (expensive) shrink-diagnostic tree when the widget is enabled.
  let collectDiagLit : TSyntax `term ← liftTermElabM <| if richOutput then `(true) else `(false)
  -- Shrink controls
  let shrinkEnabled := Lean.Option.get (← getOptions) specimen.shrink
  let shrinkEnabledLit : TSyntax `term ← liftTermElabM <| if shrinkEnabled then `(true) else `(false)
  let shrinkBreadth := Lean.Option.get (← getOptions) specimen.shrinkBreadth
  let shrinkBreadthLit := Syntax.mkNumLit (toString shrinkBreadth)
  let shrinkDepthLit := Syntax.mkNumLit (toString (Lean.Option.get (← getOptions) specimen.shrinkDepth))
  -- Diagnostic display cap: at most breadth candidates per variable.
  let diagCapLit := Syntax.mkNumLit (toString (shrinkBreadth * varNames.length + 1))
  liftTermElabM <| `((do
    let mut successes : Nat := 0
    let mut discards : Nat := 0
    for i in List.range $numTestsLit do
      let sz := $minSizeLit + i * ($maxSizeLit - $minSizeLit) / $rampDenomLit
      -- A dead-ended constrained generator throws (Gen.run turns GenError into an IO
      -- exception); treat that as a discard rather than crashing the whole test.
      let genResult ← try
          (Except.ok <$> Plausible.Gen.run (($checkerIdent) sz sz sz) sz : IO (Except Plausible.GenError _))
        catch _ => pure (Except.error (Plausible.GenError.genError "generation dead-ended"))
      match genResult with
      | .ok (.ok (true, _)) => successes := successes + 1
      | .ok (.ok (false, specimen_cex_raw)) =>
        let fuel := 3 * (sz + 1)
        -- Bounded backtracking over a LAZY candidate stream: `validShrinks` returns a
        -- `LazyList`, so `.head?`/`.take` force only what is consumed — candidate
        -- generation and DecOpt re-checks short-circuit at the first valid shrink.
        let mut bestResult := specimen_cex_raw
        let mut bestCount : Nat := 0
        -- The winning path is only stored when the diagnostic widget is enabled.
        let mut bestPath : List _ := []
        if $shrinkEnabledLit then
          let firstLevel := LazyList.take $shrinkBreadthLit (($shrinksIdent) specimen_cex_raw fuel)
          for candidate in firstLevel do
            let mut current := candidate
            let mut count : Nat := 1
            let mut path := if $collectDiagLit then [candidate] else []
            for _ in List.range $shrinkDepthLit do
              match LazyList.head? (($shrinksIdent) current fuel) with
              | some smaller =>
                current := smaller
                count := count + 1
                if $collectDiagLit then path := path ++ [smaller]
              | none => break
            if count > bestCount then
              bestResult := current
              bestCount := count
              bestPath := path
        let mut $cexIdent:term := bestResult
        let shrinkCount := bestCount
        -- Build the shrink diagnostic tree only when the widget is enabled
        -- (recomputing per-candidate outcomes is expensive for large values).
        let shrinkTree : List (String × List (String × String × String)) :=
          if $collectDiagLit then Id.run do
            let mut t : List (String × List (String × String × String)) := []
            let diag0 := LazyList.take $diagCapLit (($diagIdent) specimen_cex_raw fuel)
            let $formatTupleIdent:term := specimen_cex_raw
            t := [($fmtTupleBody, diag0)]
            for step in bestPath do
              let diagS := LazyList.take $diagCapLit (($diagIdent) step fuel)
              let $formatTupleIdent:term := step
              t := t ++ [($fmtTupleBody, diagS)]
            t
          else []
        let details := $formatExpr
        let msg := s!"Found counter-example!\n{details}\n({successes} tests passed, {discards} discarded, {shrinkCount} shrinks)"
        return (msg, shrinkCount, shrinkTree)
      | .ok (.error _) => discards := discards + 1
      | .error _ => discards := discards + 1
    return (s!"{successes} tests passed ({discards} discarded)", 0, [])
    : IO (String × Nat × List (String × List (String × String × String)))))

end Specimen.Tactic
