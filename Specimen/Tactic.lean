import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import Specimen.MExp
import Specimen.Schedules
import Specimen.DeriveSchedules
import Specimen.Debug
import Specimen.Utils
import Specimen.TheoremChecker
import Specimen.LazyList

import Plausible.Tactic
import Plausible.DeriveShrinkable

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

/-- The `specimen` command: property-based testing for propositions involving inductive relations.
    Config fields `min`, `max`, `tests` are all optional and may appear in any order, e.g.
    `specimen_test (min := 5, max := 200, tests := 500) (prop)`. -/
syntax minField := &"min" " := " num
syntax maxField := &"max" " := " num
syntax testsField := &"tests" " := " num
syntax configField := minField <|> maxField <|> testsField
syntax sizeConfig := atomic("(" configField) ("," configField)* ")"
syntax (name := specimenTestCmd) "specimen_test " (sizeConfig)? term : command

/-- Recursively search a syntax tree for a node of the given kind, returning its num arg. -/
private partial def findFieldNum (stx : Syntax) (kind : Name) : Option Nat :=
  if stx.getKind == kind then
    -- Field is `&"<name>" " := " num`, so num is the last arg
    stx.getArgs.back?.bind (·.isNatLit?)
  else
    stx.getArgs.foldl (fun acc arg => acc <|> findFieldNum arg kind) none

/-- Extract the numeric value of a `min`/`max`/`tests` field from a `sizeConfig` node. -/
private def extractSizeField (cfg : Syntax) (fieldName : String) : Option Nat :=
  let kind := match fieldName with
    | "min" => `Specimen.Tactic.minField
    | "max" => `Specimen.Tactic.maxField
    | _ => `Specimen.Tactic.testsField
  findFieldNum cfg kind

@[command_elab specimenTestCmd]
unsafe def elabSpecimenTest : CommandElab := fun stx => do
  match stx with
  | `(specimen_test $[$cfg:sizeConfig]? $prop:term) => do
    let minSize : Nat := match cfg with
      | some c => (extractSizeField c.raw "min").getD 1
      | none => 1
    let maxSize : Nat := match cfg with
      | some c => (extractSizeField c.raw "max").getD 100
      | none => 100
    let numTests : Nat := match cfg with
      | some c => (extractSizeField c.raw "tests").getD 100
      | none => 100
    let memo ← IO.mkRef ({} : Std.HashMap SpecKey MemoEntry)

    -- Elaborate the proposition and compute its schedule
    let scheduleStartTime ← IO.monoNanosNow
    let scheduleResult ← withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
      liftTermElabM do
        let e ← elabTerm prop (some (mkSort .zero))
        let tgt ← instantiateMVars e
        let termElabCtx ← readThe Lean.Elab.Term.Context
        let deriveDep : SpecKey → MetaM Unit := fun depKey => do
          let _ ← (deriveBestInductiveSchedule depKey memo).run termElabCtx
        getTheoremSchedule tgt (memoRef := some memo) (deriveDep := deriveDep)
    let scheduleEndTime ← IO.monoNanosNow
    let scheduleTimeUs := (scheduleEndTime - scheduleStartTime) / 1000

    match scheduleResult with
    | none => throwError "specimen: unable to compute a testing schedule for this proposition.\n\
        It must be of the form `∀ x₁ ... xₙ, H₁ → ... → Hₘ → C` where\n\
        the hypotheses and conclusion involve inductive relations."
    | some (steps, sort, varNamesTypes, schedulesConsidered, theoremScore) =>
      -- Ensure the conclusion's relation has a DecOpt instance derived
      match sort with
      | .TheoremSchedule (conclusionName, _) true =>
        withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
          liftTermElabM do
            let conclusionKey : SpecKey := { inductiveName := conclusionName, outputIndices := [], deriveSort := .Checker }
            let termElabCtx ← readThe Lean.Elab.Term.Context
            let _ ← (deriveBestInductiveSchedule conclusionKey memo).run termElabCtx
      | _ => pure ()

      -- Derive DecOpt checkers for all hypothesis relations (needed by validShrinks/shrinkDiag)
      for step in steps do
        match step with
        | .SuchThat _ (.NonRec (hypName, _)) _ =>
          withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
            liftTermElabM do
              let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
              let termElabCtx ← readThe Lean.Elab.Term.Context
              let _ ← (deriveBestInductiveSchedule hypCheckerKey memo).run termElabCtx
        | .Check (.NonRec (hypName, _)) _ =>
          withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
            liftTermElabM do
              let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
              let termElabCtx ← readThe Lean.Elab.Term.Context
              let _ ← (deriveBestInductiveSchedule hypCheckerKey memo).run termElabCtx
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
      -- Include hypothesis checkers (for validShrinks)
      for step in steps do
        match step with
        | .SuchThat _ (.NonRec (hypName, _)) _ =>
          let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
          usedKeys := collectUsedDeps hypCheckerKey finalMemo usedKeys
        | .Check (.NonRec (hypName, _)) _ =>
          let hypCheckerKey : SpecKey := { inductiveName := hypName, outputIndices := [], deriveSort := .Checker }
          usedKeys := collectUsedDeps hypCheckerKey finalMemo usedKeys
        | _ => pure ()
      for dep in directDeps do
        if dep.kind == DepKind.relation || dep.kind == DepKind.checker then
          let depKey : SpecKey := { inductiveName := dep.inductiveName, outputIndices := dep.outputIndices, deriveSort := dep.deriveSort }
          usedKeys := collectUsedDeps depKey finalMemo usedKeys

      -- Compile & emit all dependency instances using the SAME machinery as derive_mutual
      -- (so mutually-recursive components — e.g. the two modes of `typing` — go into a
      -- single `mutual … end` block with a consistent sibling-name mapping).
      let components := computeSpecSCC usedKeys.toList finalMemo
      let debugLog := Lean.Option.get (← getOptions) specimen.debug
      if debugLog then
        logInfo m!"specimen: {components.length} SCC components, {usedKeys.size} used keys"
        for comp in components do
          let compDesc := comp.map (fun k =>
            m!"{k.inductiveName} outputs={k.outputIndices} sort={repr k.deriveSort}")
          logInfo m!"  component: {compDesc}"
      let constraintMap ← liftTermElabM <| propagateConstraints components finalMemo
      let (compiledComponents, compiledCodeMap) ←
        compileSpecComponents components finalMemo constraintMap
      emitSpecComponents compiledComponents .global

      -- Compile the theorem schedule into a checker def (before widget so we can show the code)
      let defName ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_theorem_checker)
      let varNames := varNamesTypes.map Prod.fst
      let varTypes := varNamesTypes.map Prod.snd
      let defCmd ← withScope (fun scope => { scope with opts := scope.opts.set `specimen.multiOutput true }) do
        liftTermElabM <| compileTheoremDef steps sort (mkSort .zero) defName varNames varTypes
      let theoremCodeStr ← liftTermElabM <| try
        let fmt ← Lean.PrettyPrinter.ppCommand defCmd
        pure fmt.pretty
      catch _ => pure "(failed to pretty-print)"
      if debugLog then
        logInfo m!"── emitting theorem checker {defName}:\n{theoremCodeStr}"
      elabCommand defCmd

      -- Compile the validShrinks function
      let shrinkBreadth := Lean.Option.get (← getOptions) specimen.shrinkBreadth
      let shrinksName ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_valid_shrinks)
      let shrinksCmd ← liftTermElabM <| compileValidShrinksDef steps sort shrinksName varNames varTypes shrinkBreadth
      elabCommand shrinksCmd

      -- Compile the shrink diagnostic function (for HTML trace)
      let shrinkDiagName ← liftTermElabM (Lean.Core.mkFreshUserName `specimen_shrink_diag)
      let shrinkDiagCmd ← liftTermElabM <| compileShrinkDiagDef steps sort shrinkDiagName varNames varTypes shrinkBreadth
      elabCommand shrinkDiagCmd

      -- Build rich HTML widget (emitted after test result for better infoview order)
      let richOutput := Lean.Option.get (← getOptions) specimen.richOutput
      let widgetMsg ← if richOutput then
        liftTermElabM do
          let mkSpan (style : Json) (text : String) : ProofWidgets.Html :=
            .element "span" #[("style", style)] #[.text text]
          let headerStyle := json% {"fontWeight": "bold", "fontSize": "1.2em", "color": "#4fc1ff"}
          let schedStyle := json% {"color": "#ce9178", "fontSize": "0.9em", "whiteSpace": "pre", "fontFamily": "var(--vscode-editor-font-family, monospace)"}
          let scoreStyle := json% {"color": "#808080", "fontSize": "0.9em"}
          let singletonStyle := json% {"color": "#b5cea8"}
          let srcStyle := json% {"color": "#dcdcaa", "fontWeight": "bold"}
          let dstStyle := json% {"color": "#9cdcfe"}
          let reqStyle := json% {"color": "#c586c0", "fontStyle": "italic"}
          let bundle ← Scoring.getActiveScorerBundle
          let scoreToColor (score : Score) : String :=
            let b := bundle.scoreBadness score
            let hue := (1.0 - b) * 120.0
            s!"hsl({Float.toString hue}, 70%, 60%)"
          let specColor (indSched : InductiveSchedule) : String := scoreToColor indSched.score
          let getNumArgs (k : SpecKey) : TermElabM Nat := do
            try pure ((← getComponentsOfArrowType (← getConstInfoInduct k.inductiveName).type).size - 1)
            catch _ => pure k.outputIndices.length
          let stepColor (step : ScheduleStep) : String :=
            match step with
            | .Check (.NonRec (name, _)) true =>
              match finalMemo[SpecKey.mk name [] .Checker]? with
              | some (.done depSched) => specColor depSched
              | _ => "hsl(30, 70%, 60%)"
            | .Check _ false => "hsl(0, 70%, 60%)"
            | .Check _ true => "hsl(30, 70%, 60%)"
            | .Unconstrained _ (.NonRec (name, _)) _ =>
              match finalMemo[SpecKey.mk name [] .Generator]? with
              | some (.done depSched) => specColor depSched
              | _ => "hsl(60, 70%, 60%)"
            | .Unconstrained _ _ _ => "hsl(60, 70%, 60%)"
            | .SuchThat vs (.NonRec (name, args)) ps =>
              let outIdxs := computeOutputIndices args (vs.map Prod.fst)
              let ds := match ps with | .Generator => DeriveSort.Generator | .Enumerator => .Enumerator
              match finalMemo[SpecKey.mk name outIdxs ds]? with
              | some (.done depSched) => specColor depSched
              | _ => "hsl(90, 70%, 60%)"
            | .SuchThat _ (.Rec ..) _ | .SuchThat _ (.MutRec ..) _ => "hsl(200, 50%, 60%)"
            | .Match .. => "hsl(120, 40%, 60%)"
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
          if !orderItems.isEmpty then
            htmlChildren := htmlChildren.push (.element "details" #[("open", json% true)] #[
              .element "summary" #[("style", json% {"cursor": "pointer", "fontWeight": "bold", "color": "#569cd6", "marginBottom": "6px"})] #[
                .text s!"📋 Derived Specs ({usedKeys.size} total, topological order)"
              ],
              .element "div" #[("style", json% {"marginLeft": "8px"})] orderItems
            ])
          -- Dependency graph section
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
          -- Pattern coverage trie
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
          let fullHtml := ProofWidgets.Html.element "div"
            #[("style", json% {"fontFamily": "var(--vscode-editor-font-family, monospace)", "fontSize": "13px", "lineHeight": "1.6", "padding": "8px"})]
            htmlChildren
          let htmlMsg ← Lean.MessageData.ofHtml fullHtml
            s!"specimen_test: {usedKeys.size} derived specs, {components.length} components"
          pure (some htmlMsg)
      else
        pure none

      -- Run the test loop
      let checkerIdent : TSyntax `term := mkIdent defName
      let shrinksIdent : TSyntax `term := mkIdent shrinksName
      let diagIdent : TSyntax `term := mkIdent shrinkDiagName

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
      let shrinkBreadthLit := Syntax.mkNumLit (toString (Lean.Option.get (← getOptions) specimen.shrinkBreadth))
      let shrinkDepthLit := Syntax.mkNumLit (toString (Lean.Option.get (← getOptions) specimen.shrinkDepth))
      -- Diagnostic display cap: at most breadth candidates per variable.
      let diagCapLit := Syntax.mkNumLit (toString (shrinkBreadth * varNames.length + 1))
      let testExpr ← liftTermElabM <| `((do
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

      let e ← liftTermElabM <| Term.elabTerm testExpr none
      let expectedType ← liftTermElabM <| inferType e
      let action ← liftTermElabM <| unsafe Lean.Meta.evalExpr
        (IO (String × Nat × List (String × List (String × String × String)))) expectedType e
      let (resultMsg, _shrinkCount, shrinkTree) ← action

      -- Emit the test result first (appears at top of infoview)
      if resultMsg.startsWith "Found counter-example!" then
        logError resultMsg
      else
        logInfo resultMsg

      -- Build shrink tree HTML widget if there was shrinking
      if !shrinkTree.isEmpty then
        let shrinkHtml ← liftTermElabM do
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
        logInfo shrinkHtml

      -- Emit the main widget after test result
      if let some msg := widgetMsg then
        logInfo msg

  | _ => throwUnsupportedSyntax

/-- Run a `CommandElabM` action from within `CoreM`, building a command context/state
    from the current core context/state and syncing the environment, name generators,
    messages, traces, and info trees back afterward.

    This is the inverse of `Lean.Elab.Command.runCore` (which runs `CoreM` inside
    `CommandElabM`). It lets the `specimen` tactic reuse the `specimen_test` command
    logic (which emits derived instances via `elabCommand`). -/
def runCommandElabMInCore (x : CommandElabM α) : CoreM α := do
  let coreCtx ← readThe Core.Context
  let coreState ← getThe Core.State
  let opts ← getOptions
  let cmdCtx : Lean.Elab.Command.Context := {
    fileName       := coreCtx.fileName
    fileMap        := coreCtx.fileMap
    currRecDepth   := coreCtx.currRecDepth
    currMacroScope := coreCtx.currMacroScope
    ref            := coreCtx.ref
    snap?          := none
    cancelTk?      := coreCtx.cancelTk?
  }
  -- Preserve the current namespace and open declarations so name resolution
  -- inside the emitted commands matches the tactic's context.
  let scope : Lean.Elab.Command.Scope := {
    header       := ""
    opts         := opts
    currNamespace := coreCtx.currNamespace
    openDecls    := coreCtx.openDecls
  }
  let cmdState : Lean.Elab.Command.State := {
    env            := coreState.env
    messages       := coreState.messages
    scopes         := [scope]
    nextMacroScope := coreState.nextMacroScope
    maxRecDepth    := coreCtx.maxRecDepth
    ngen           := coreState.ngen
    auxDeclNGen    := coreState.auxDeclNGen
    infoState      := coreState.infoState
    traceState     := coreState.traceState
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run cmdState) with
  | .error e => throw e
  | .ok (a, sNew) =>
    modifyThe Core.State fun s => { s with
      env            := sNew.env
      messages       := sNew.messages
      nextMacroScope := sNew.nextMacroScope
      ngen           := sNew.ngen
      auxDeclNGen    := sNew.auxDeclNGen
      infoState      := sNew.infoState
      traceState     := sNew.traceState
    }
    return a

/-- The `specimen` tactic: property-based testing of the current proof goal.

    Forms a closed universally-quantified proposition from the goal and all local
    hypotheses (via `mkForallFVars` — the proof state is *not* mutated), then tests
    it exactly as `specimen_test` does. Derived generators and checkers are added to
    the environment only for the duration of the test — the environment is restored
    afterward, so nothing leaks (the definitions are "local to the theorem").

    `specimen` is a diagnostic: it reports whether a counterexample was found and does
    not alter the goal or claim to prove it. If it passes, prove the goal as usual;
    if it reports a counterexample, the goal is false as stated.

    Usage: `specimen`, `specimen (min := 5)`, `specimen (max := 200)`,
    `specimen (min := 5, max := 200)`. -/
syntax (name := specimenTac) "specimen" (sizeConfig)? : tactic

@[tactic specimenTac]
unsafe def evalSpecimenTac : Tactic := fun stx => do
  match stx with
  | `(tactic| specimen $[$cfg:sizeConfig]?) => withMainContext do
    -- Build the closed ∀-proposition from the goal + local hypotheses WITHOUT
    -- mutating the proof state (no revert): abstract the local fvars over the target.
    let tgt ← getMainTarget
    let fvars := (← getLocalHyps)
    let closedProp ← instantiateMVars (← mkForallFVars fvars tgt)
    -- Delaborate the closed proposition into a term syntax
    let tgtStx ← PrettyPrinter.delab closedProp
    -- Build the `specimen_test` command syntax (forwarding any size config)
    let cmdStx ← match cfg with
      | some c => `(command| specimen_test $c:sizeConfig $tgtStx:term)
      | none => `(command| specimen_test $tgtStx:term)
    -- Snapshot the environment; run the test; restore so derived defs don't leak
    let savedEnv ← getEnv
    try
      runCommandElabMInCore (Lean.Elab.Command.elabCommand cmdStx)
      setEnv savedEnv
    catch e =>
      setEnv savedEnv
      throw e
  | _ => throwUnsupportedSyntax

end Specimen.Tactic
