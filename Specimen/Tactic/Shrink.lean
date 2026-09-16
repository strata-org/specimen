import Specimen.DeriveConstrainedProducer
import Specimen.MExp
import Specimen.Schedules
import Specimen.Debug
import Specimen.LazyList
import Specimen.TheoremChecker
import Plausible.DeriveShrinkable

open Lean Elab Term Meta
open Idents Schedules MExp
open Plausible

/-! # Shrinking for `specimen_test`

Compiles the two shrink-side functions emitted alongside a theorem checker:

* `validShrinks` — smaller candidate tuples that still satisfy every hypothesis and still
  violate the conclusion, so the greedy descent in `Specimen/Tactic.lean` can take the first
  one it is handed.
* `shrinkDiag` — the same walk, but recording which hypothesis rejected each candidate, for
  the shrink-tree display in the infoview.

Both build breadth-capped `LazyList`s so the consumer forces only the candidates it uses.
-/

namespace Specimen.Tactic

/-- Compiles a `validShrinks` function from the theorem schedule.
    For each variable position, tries `Shrinkable.shrink` on that variable,
    then walks the schedule steps in order: for each `SuchThat`/`Check` step,
    re-checks the hypothesis with `DecOpt.decOpt` (short-circuiting on failure).
    Finally confirms the conclusion still fails. Returns all valid shrunk tuples. -/
def compileValidShrinksDef (steps : List ScheduleStep) (sort : ScheduleSort)
    (defName : Name) (varNames : List Name) (varTypes : List Expr) (breadth : Nat)
    : TermElabM (TSyntax `command) := do
  let breadthLit := Syntax.mkNumLit (toString breadth)
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

  -- Build projection syntax for variable i from the tuple
  let mkProj (tupleIdent : TSyntax `term) (i : Nat) : TermElabM (TSyntax `term) := do
    if varNames.length == 1 then pure tupleIdent
    else if i == 0 then `(($tupleIdent).1)
    else
      let mut e := tupleIdent
      for _ in [:i - 1] do e ← `(($e).2)
      if i == varNames.length - 1 then `(($e).2)
      else `(($e).2.1)

  -- Build a tuple expression from individual variable idents
  let mkTupleFromIdents (idents : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
    match idents.toList with
    | [] => `(())
    | [x] => pure x
    | _ =>
      let rec go : List (TSyntax `term) → TermElabM (TSyntax `term)
        | [] => `(())
        | [x] => pure x
        | x :: rest => do let r ← go rest; `(($x, $r))
      go idents.toList

  -- Collect DecOpt check expressions from the schedule steps (SuchThat and Check)
  -- Uses MExp → mexpToTSyntax to handle implicit args correctly (e.g. HAdd.hAdd)
  let fuelMExp : MExp := .MId `specimen_fuel

  let mut checkExprs : Array (TSyntax `term) := #[]
  for step in steps do
    match step with
    | .SuchThat _varsTys src _ps =>
      match src with
      | .NonRec hypExpr =>
        let chk := decOptChecker (hypothesisExprToMExp hypExpr) fuelMExp
        let (stx, _) ← (mexpToTSyntax chk .Checker).run #[]
        checkExprs := checkExprs.push stx
      | _ => pure ()
    | .Check src polarity =>
      match src with
      | .NonRec hypExpr =>
        let baseChk := decOptChecker (hypothesisExprToMExp hypExpr) fuelMExp
        let chk := if polarity then baseChk
          else .MApp .allowImplicit (.MConst ``DecOpt.negOpt) [baseChk]
        let (stx, _) ← (mexpToTSyntax chk .Checker).run #[]
        checkExprs := checkExprs.push stx
      | _ => pure ()
    | _ => pure ()

  -- Build the conclusion check (must still fail for the shrink to be a valid counterexample)
  let conclusionCheckExpr ← match sort with
    | .TheoremSchedule conclusion _ =>
      let chk := decOptChecker (hypothesisExprToMExp conclusion) fuelMExp
      let (stx, _) ← (mexpToTSyntax chk .Checker).run #[]
      pure stx
    | _ => `(Except.ok true)

  -- Build the validity check body:
  -- all hypothesis checks pass (.ok true) AND conclusion still fails (not .ok true)
  let mut validBody ← `(!(Specimen.isOkTrue ($conclusionCheckExpr)))
  for checkExpr in checkExprs.reverse do
    validBody ← `(if Specimen.isOkTrue ($checkExpr) then $validBody else false)

  -- Build shrink candidates with coarse-to-fine ordering:
  -- 1. All-at-once (zip all shrink lists for jointly-constrained groups)
  -- 2. Pairs (zip each pair of shrink lists within groups)
  -- 3. Singles (each variable independently)
  -- All streams are interleaved fairly.
  let tupleIdent := mkIdent `specimen_tup

  -- Track which variables are produced by multi-output SuchThat steps
  let mut suchThatGroups : Array (Array Nat) := #[]
  for step in steps do
    match step with
    | .SuchThat varsTys _ _ =>
      let groupVarNames := varsTys.map Prod.fst
      let mut group : Array Nat := #[]
      for gv in groupVarNames do
        let mut idx : Nat := 0
        for vn in varNames do
          if vn == gv then
            group := group.push idx
          idx := idx + 1
      if group.size > 1 then
        suchThatGroups := suchThatGroups.push group
    | _ => pure ()

  -- Helper: build a filtered shrink expression given the shrunk tuple parts
  -- Checks all hypotheses + conclusion still fails
  let mkValidityCheck : TermElabM (TSyntax `term) := do
    let rebuiltIdent := mkIdent `specimen_rebuilt
    let mut checkBody ← `($validBody)
    for j in (List.range varNames.length).reverse do
      let varIdent := mkIdent varNames[j]!
      let projJ ← mkProj rebuiltIdent j
      checkBody ← `(let $(varIdent) := $projJ; $checkBody)
    pure checkBody

  -- A lazy, breadth-capped shrink list for the variable at index `i`.
  let cappedShrink (i : Nat) : TermElabM (TSyntax `term) := do
    let proj ← mkProj tupleIdent i
    `(LazyList.fromList ((Shrinkable.shrink $proj).take $breadthLit))

  -- Tier 1: All-at-once for each SuchThat group (lazy cartesian product of all shrink lists)
  let mut tier1Exprs : Array (TSyntax `term) := #[]
  for group in suchThatGroups do
    if group.size < 2 then continue
    let mut candidateIdents : Array Lean.Ident := #[]
    for k in [:group.size] do
      candidateIdents := candidateIdents.push (mkIdent (Name.mkSimple s!"specimen_all_{k}"))
    let mut rebuiltParts : Array (TSyntax `term) := #[]
    for j in [:varNames.length] do
      let gPos := group.toList.findIdx (· == j)
      if group.contains j then
        rebuiltParts := rebuiltParts.push candidateIdents[gPos]!
      else
        rebuiltParts := rebuiltParts.push (← mkProj tupleIdent j)
    let rebuiltTuple ← mkTupleFromIdents rebuiltParts
    -- Build nested lazy bind from inside out; innermost yields a singleton
    let mut cartesian ← `(LazyList.pureLazyList $rebuiltTuple)
    for k in (List.range group.size).reverse do
      let cIdent := candidateIdents[k]!
      let base ← cappedShrink group[k]!
      cartesian ← `(LazyList.bindLazyList $base (fun $(cIdent) => $cartesian))
    let entryIdent := mkIdent `specimen_cart_e
    let rebuiltIdent := mkIdent `specimen_rebuilt
    let checkBody ← mkValidityCheck
    let filterExpr ← `(LazyList.filter (fun $(entryIdent) =>
      let $(rebuiltIdent) := $(entryIdent)
      $checkBody) $cartesian)
    tier1Exprs := tier1Exprs.push filterExpr

  -- Tier 2: Pairs for each SuchThat group (lazy cartesian product of each pair)
  let mut tier2Exprs : Array (TSyntax `term) := #[]
  for group in suchThatGroups do
    for gi in [:group.size] do
      for gj in [gi+1:group.size] do
        let idxI := group[gi]!
        let idxJ := group[gj]!
        let ciIdent := mkIdent (Name.mkSimple s!"specimen_pi_{idxI}")
        let cjIdent := mkIdent (Name.mkSimple s!"specimen_pj_{idxJ}")
        let mut rebuiltParts : Array (TSyntax `term) := #[]
        for j in [:varNames.length] do
          if j == idxI then rebuiltParts := rebuiltParts.push ciIdent
          else if j == idxJ then rebuiltParts := rebuiltParts.push cjIdent
          else rebuiltParts := rebuiltParts.push (← mkProj tupleIdent j)
        let rebuiltTuple ← mkTupleFromIdents rebuiltParts
        let baseI ← cappedShrink idxI
        let baseJ ← cappedShrink idxJ
        let cartesian ← `(LazyList.bindLazyList $baseI (fun $(ciIdent) =>
          LazyList.mapLazyList (fun $(cjIdent) => $rebuiltTuple) $baseJ))
        let entryIdent := mkIdent `specimen_pair_e
        let rebuiltIdent := mkIdent `specimen_rebuilt
        let checkBody ← mkValidityCheck
        let filterExpr ← `(LazyList.filter (fun $(entryIdent) =>
          let $(rebuiltIdent) := $(entryIdent)
          $checkBody) $cartesian)
        tier2Exprs := tier2Exprs.push filterExpr

  -- Tier 3: Singles (each variable independently)
  let mut tier3Exprs : Array (TSyntax `term) := #[]
  for i in [:varNames.length] do
    let candidateIdent := mkIdent (Name.mkSimple s!"specimen_c_{i}")
    let mut rebuiltParts : Array (TSyntax `term) := #[]
    for j in [:varNames.length] do
      if j == i then rebuiltParts := rebuiltParts.push candidateIdent
      else rebuiltParts := rebuiltParts.push (← mkProj tupleIdent j)
    let rebuiltTuple ← mkTupleFromIdents rebuiltParts
    let base ← cappedShrink i
    let rebuiltIdent := mkIdent `specimen_rebuilt
    let checkBody ← mkValidityCheck
    let mapped ← `(LazyList.mapLazyList (fun $(candidateIdent) => $rebuiltTuple) $base)
    let filterExpr ← `(LazyList.filter (fun $(rebuiltIdent) => $checkBody) $mapped)
    tier3Exprs := tier3Exprs.push filterExpr

  -- Combine tiers lazily in coarse-to-fine order (all-at-once, then pairs, then singles).
  -- `LazyList.append` keeps evaluation lazy so the greedy shrinker forces only what it consumes.
  let allStreams := tier1Exprs ++ tier2Exprs ++ tier3Exprs
  let fullBody ← match allStreams.toList with
    | [] => `((LazyList.lnil : LazyList $tupleType))
    | x :: rest => rest.foldlM (fun acc e => `(LazyList.append $acc $e)) x

  let defIdent := mkIdent defName
  let tupleBinderIdent := mkIdent `specimen_tup
  let fuelBinderIdent := mkIdent `specimen_fuel
  let retType ← `(LazyList $tupleType)
  `(private def $defIdent ($tupleBinderIdent : $tupleType) ($fuelBinderIdent : Nat) : $retType :=
    $fullBody)

/-- Compiles a `shrinkDiag` function that returns diagnostic info for each shrink attempt.
    Returns: `TupleType → Nat → List (String × String × String)` where each entry is
    `(varName, reprOfShrunkValue, outcome)`. Outcome is one of:
    - "accepted" (valid shrink)
    - "hyp: <hypothesis> failed" (which hypothesis rejected it)
    - "conclusion passed" (conclusion no longer fails — not a counterexample) -/
def compileShrinkDiagDef (steps : List ScheduleStep) (sort : ScheduleSort)
    (defName : Name) (varNames : List Name) (varTypes : List Expr) (breadth : Nat)
    : TermElabM (TSyntax `command) := do
  let breadthLit := Syntax.mkNumLit (toString breadth)
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

  let mkProj (tupleIdent : TSyntax `term) (i : Nat) : TermElabM (TSyntax `term) := do
    if varNames.length == 1 then pure tupleIdent
    else if i == 0 then `(($tupleIdent).1)
    else
      let mut e := tupleIdent
      for _ in [:i - 1] do e ← `(($e).2)
      if i == varNames.length - 1 then `(($e).2)
      else `(($e).2.1)

  let mkTupleFromIdents (idents : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
    match idents.toList with
    | [] => `(())
    | [x] => pure x
    | _ =>
      let rec go : List (TSyntax `term) → TermElabM (TSyntax `term)
        | [] => `(())
        | [x] => pure x
        | x :: rest => do let r ← go rest; `(($x, $r))
      go idents.toList

  let fuelMExp : MExp := .MId `specimen_fuel

  -- Collect check expressions AND their human-readable labels
  let mut checkExprsAndLabels : Array (TSyntax `term × String) := #[]
  for step in steps do
    match step with
    | .SuchThat _varsTys src _ps =>
      match src with
      | .NonRec hypExpr =>
        let chk := decOptChecker (hypothesisExprToMExp hypExpr) fuelMExp
        let (stx, _) ← (mexpToTSyntax chk .Checker).run #[]
        checkExprsAndLabels := checkExprsAndLabels.push (stx, ppHypothesisExpr hypExpr)
      | _ => pure ()
    | .Check src polarity =>
      match src with
      | .NonRec hypExpr =>
        let baseChk := decOptChecker (hypothesisExprToMExp hypExpr) fuelMExp
        let chk := if polarity then baseChk
          else .MApp .allowImplicit (.MConst ``DecOpt.negOpt) [baseChk]
        let (stx, _) ← (mexpToTSyntax chk .Checker).run #[]
        let label := if polarity then ppHypothesisExpr hypExpr else s!"¬{ppHypothesisExpr hypExpr}"
        checkExprsAndLabels := checkExprsAndLabels.push (stx, label)
      | _ => pure ()
    | _ => pure ()

  let conclusionLabel := match sort with
    | .TheoremSchedule conclusion _ => ppHypothesisExpr conclusion
    | _ => "conclusion"

  let conclusionCheckExpr ← match sort with
    | .TheoremSchedule conclusion _ =>
      let chk := decOptChecker (hypothesisExprToMExp conclusion) fuelMExp
      let (stx, _) ← (mexpToTSyntax chk .Checker).run #[]
      pure stx
    | _ => `(Except.ok true)

  -- For each variable position, for each shrink candidate, determine the outcome:
  -- Walk checks in order, return the label of the first failing one, or "conclusion passed",
  -- or "accepted"
  let tupleIdent := mkIdent `specimen_tup
  let mut allDiagExprs : Array (TSyntax `term) := #[]
  for i in [:varNames.length] do
    let projI ← mkProj tupleIdent i
    -- Lazy, breadth-capped shrink candidates (mirrors validShrinks' singles tier)
    let shrinkCandidates ← `(LazyList.fromList ((Shrinkable.shrink $projI).take $breadthLit))
    let candidateIdent := mkIdent (Name.mkSimple s!"specimen_c_{i}")
    let mut rebuiltParts : Array (TSyntax `term) := #[]
    for j in [:varNames.length] do
      if j == i then
        rebuiltParts := rebuiltParts.push candidateIdent
      else
        rebuiltParts := rebuiltParts.push (← mkProj tupleIdent j)
    let rebuiltTuple ← mkTupleFromIdents rebuiltParts
    let rebuiltIdent := mkIdent `specimen_rebuilt

    -- Build the diagnostic body: check each hypothesis in order, short-circuit with label
    let conclusionLabelLit := Syntax.mkStrLit s!"conclusion {conclusionLabel} passed"
    let mut diagBody ← `(if Specimen.isOkTrue ($conclusionCheckExpr) then $conclusionLabelLit else "accepted")
    for (checkExpr, label) in checkExprsAndLabels.reverse do
      let labelLit := Syntax.mkStrLit s!"hyp: {label} failed"
      diagBody ← `(if Specimen.isOkTrue ($checkExpr) then $diagBody else $labelLit)

    -- Wrap with let bindings for variable names from the rebuilt tuple
    let mut letBody ← `($diagBody)
    for j in (List.range varNames.length).reverse do
      let varIdent := mkIdent varNames[j]!
      let projJ ← mkProj rebuiltIdent j
      letBody ← `(let $(varIdent) := $projJ; $letBody)

    let varNameLit := Syntax.mkStrLit varNames[i]!.toString
    let diagExpr ← `(LazyList.mapLazyList (fun $(candidateIdent) =>
      let $(rebuiltIdent) := $rebuiltTuple
      let outcome := $letBody
      ($varNameLit, reprStr $(candidateIdent), outcome)) $shrinkCandidates)
    allDiagExprs := allDiagExprs.push diagExpr

  let fullBody ← match allDiagExprs.toList with
    | [] => `((LazyList.lnil : LazyList (String × String × String)))
    | x :: rest => rest.foldlM (fun acc e => `(LazyList.append $acc $e)) x

  let defIdent := mkIdent defName
  let tupleBinderIdent := mkIdent `specimen_tup
  let fuelBinderIdent := mkIdent `specimen_fuel
  let retType ← `(LazyList (String × String × String))
  `(private def $defIdent ($tupleBinderIdent : $tupleType) ($fuelBinderIdent : Nat) : $retType :=
    $fullBody)

end Specimen.Tactic
