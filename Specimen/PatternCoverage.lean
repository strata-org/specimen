import Specimen.Schedules
import Specimen.Scoring
import Lean

namespace PatternCoverage

open Lean Meta Schedules

/-- Coverage pattern — tracks why a position is unconstrained.
    Used for partitioning the input space of an inductive relation. -/
inductive CovPattern
  | ctr : Name → List CovPattern → CovPattern
  | wild : CovPattern
  | typeVar : Name → CovPattern
  | instParam : Name → CovPattern
  | funcApp : Name → CovPattern
  | output : CovPattern
  /-- Catch-all for literal values not explicitly branched on -/
  | otherLit : CovPattern
  deriving Repr, BEq, Inhabited

/-- The coverage tree.
    Partitions the input space of an inductive relation by the patterns
    of its constructors (rules). Each leaf tracks which rules cover it. -/
inductive CoverageTree
  | leaf (pat : CovPattern) (rules : List Name) : CoverageTree
  | node (pat : CovPattern) (rules : List Name) (splitPath : List Nat)
         (branches : List (Name × CoverageTree)) : CoverageTree
  deriving Repr, Inhabited

/-- A leaf annotated with covering constructors and their schedule scores. -/
structure AnnotatedLeaf where
  pattern : CovPattern
  coveringCtors : List (Name × ScheduleScore)
  deriving Repr

----------------------------------------------
-- Pure pattern helpers
----------------------------------------------

/-- A pattern position is splittable if it hasn't been refined yet (wild or otherLit). -/
def isSplittable : CovPattern → Bool
  | .wild => true
  | .otherLit => true
  | _ => false

/-- Flatten a CovPattern into (ctrName, arity, indexPath) triples.
    Only `ctr` nodes produce entries. -/
partial def decomposePath (p : CovPattern) (path : List Nat) : List (Name × Nat × List Nat) :=
  match p with
  | .ctr c ps =>
    (c, ps.length, path) :: (ps.zipIdx.flatMap fun (sub, i) => decomposePath sub (path ++ [i]))
  | _ => []

/-- Decompose a pattern for coverage analysis.
    The root `ctr indName [...]` wraps all input positions — it is included in
    the decomposition so that the initial tree gets split into the root shape,
    but `getSiblingCtors` handles it specially (returns only itself). -/
def decompose (p : CovPattern) : List (Name × Nat × List Nat) := decomposePath p []

/-- Replace the sub-pattern at `path` with `ctr name (replicate arity wild)`. -/
partial def insertAtPath (p : CovPattern) (path : List Nat) (name : Name) (arity : Nat) : CovPattern :=
  match path with
  | [] => if name == `_otherLit then .otherLit else .ctr name (List.replicate arity .wild)
  | i :: is =>
    match p with
    | .ctr c ps => .ctr c (ps.zipIdx.map fun (sub, j) =>
        if j == i then insertAtPath sub is name arity else sub)
    | other => other

/-- Retrieve the sub-pattern at a given index path. -/
partial def patternAtPath (p : CovPattern) (path : List Nat) : CovPattern :=
  match path with
  | [] => p
  | i :: is =>
    match p with
    | .ctr _ ps => match ps[i]? with
      | some sub => patternAtPath sub is
      | none => .wild
    | _ => .wild

----------------------------------------------
-- Pattern relations
----------------------------------------------

/-- Is `sub` a sub-pattern of `sup`?
    For coverage labeling: "does the leaf pattern fit inside the rule's pattern?" -/
partial def isSubpattern (sub sup : CovPattern) : Bool :=
  match sub, sup with
  | .output, .output => true
  | .output, _ => false
  | _, .output => false
  | _, .wild => true
  | _, .typeVar _ => true
  | _, .instParam _ => true
  | _, .funcApp _ => true
  | _, .otherLit => true
  | .ctr c1 ps1, .ctr c2 ps2 =>
    c1 == c2 && ps1.length == ps2.length &&
    (ps1.zip ps2).all fun (s, p) => isSubpattern s p
  | .wild, .ctr _ _ => false
  | .typeVar _, .ctr _ _ => false
  | .instParam _, .ctr _ _ => false
  | .funcApp _, .ctr _ _ => false
  | .otherLit, .ctr _ _ => false

/-- Can these two patterns overlap? Used for early pruning during labeling. -/
partial def isCompatible (p1 p2 : CovPattern) : Bool :=
  match p1, p2 with
  | .output, .output => true
  | .output, _ | _, .output => false
  | _, .wild | .wild, _ => true
  | _, .typeVar _ | .typeVar _, _ => true
  | _, .instParam _ | .instParam _, _ => true
  | _, .funcApp _ | .funcApp _, _ => true
  | _, .otherLit | .otherLit, _ => true
  | .ctr c1 ps1, .ctr c2 ps2 =>
    c1 == c2 && ps1.length == ps2.length &&
    (ps1.zip ps2).all fun (s, p) => isCompatible s p

----------------------------------------------
-- Tree operations (labeling is pure)
----------------------------------------------

/-- Label all descendants of a tree with a rule name. -/
partial def labelTree (rule : Name) (tree : CoverageTree) : CoverageTree :=
  match tree with
  | .leaf pat rules => .leaf pat (rule :: rules)
  | .node pat rules splitPath branches =>
    .node pat (rule :: rules) splitPath (branches.map fun (c, sub) => (c, labelTree rule sub))

/-- Mark leaves whose pattern is subsumed by a rule's pattern. -/
partial def labelSubpatterns (rule : Name) (rulePat : CovPattern) (tree : CoverageTree) : CoverageTree :=
  match tree with
  | .leaf pat rules =>
    if isSubpattern pat rulePat then .leaf pat (rule :: rules) else tree
  | .node pat rules splitPath branches =>
    if isSubpattern pat rulePat then labelTree rule tree
    else if isCompatible pat rulePat then
      .node pat rules splitPath (branches.map fun (c, sub) => (c, labelSubpatterns rule rulePat sub))
    else tree

----------------------------------------------
-- Tree operations (splitting needs MetaM)
----------------------------------------------

private def isLiteralName (n : Name) : Bool :=
  match n with
  | .str .anonymous s => (s.startsWith "\"" && s.endsWith "\"") || (s.startsWith "'" && s.endsWith "'")
  | _ => false

/-- Get all sibling constructors of `ctrName` and their arities (non-param args).
    - Literal names → return [(lit, 0), (_otherLit, 0)]
    - Non-constructor names → return [(name, arity)] (synthetic root)
    - Real constructors → return all siblings of the parent inductive -/
private partial def getSiblingCtors (ctrName : Name) (arity : Nat) : MetaM (List (Name × Nat)) := do
  if isLiteralName ctrName then
    return [(ctrName, 0), (`_otherLit, 0)]
  let env ← getEnv
  if !env.isConstructor ctrName then
    return [(ctrName, arity)]
  let ctorInfo ← getConstInfoCtor ctrName
  let indInfo ← getConstInfoInduct ctorInfo.induct
  let numParams := indInfo.numParams
  let mut result : List (Name × Nat) := []
  for sibName in indInfo.ctors do
    let sibInfo ← getConstInfoCtor sibName
    let sibArity ← forallTelescopeReducing sibInfo.type fun args _ => do
      return args.size - numParams
    result := result ++ [(sibName, sibArity)]
  return result

/-- Split the tree at `splitPath` for constructor `ctrName` (with known `arity`).
    When we hit a leaf with `wild` at the split position, expand into branches. -/
partial def coverSingleLayer (ctrName : Name) (arity : Nat) (splitPath : List Nat)
    (patSoFar : CovPattern) (tree : CoverageTree) : MetaM CoverageTree := do
  match tree with
  | .leaf pat rules =>
    if !isSplittable (patternAtPath pat splitPath) then
      return tree
    let siblings ← getSiblingCtors ctrName arity
    let newPattern c a := insertAtPath pat splitPath c a
    let newLeaves := siblings.map fun (c, a) => (c, CoverageTree.leaf (newPattern c a) rules)
    return .node pat rules splitPath newLeaves
  | .node pat rules splitPath' branches =>
    if splitPath == splitPath' then
      if isLiteralName ctrName && !branches.any (·.1 == ctrName) then
        -- New literal at an already-split position: add it as a sibling,
        -- keeping the existing _otherLit branch for everything else.
        match branches.find? (·.1 == `_otherLit) with
        | some (_, otherSub) =>
          let newLeafPat := insertAtPath pat splitPath ctrName 0
          let newBranch := (ctrName, CoverageTree.leaf newLeafPat (match otherSub with | .leaf _ rs => rs | .node _ rs .. => rs))
          let branches' := branches.filter (·.1 != `_otherLit) ++ [newBranch, (`_otherLit, otherSub)]
          return .node pat rules splitPath' branches'
        | none => return tree
      else
        return tree
    else
      match patternAtPath patSoFar splitPath' with
      | .wild =>
        let branches' ← branches.mapM fun (c, sub) => do
          let sub' ← coverSingleLayer ctrName arity splitPath patSoFar sub
          return (c, sub')
        return .node pat rules splitPath' branches'
      | .ctr c _ =>
        let branches' ← branches.mapM fun (branchCtr, sub) => do
          if branchCtr == c then
            let sub' ← coverSingleLayer ctrName arity splitPath patSoFar sub
            return (branchCtr, sub')
          else
            return (branchCtr, sub)
        return .node pat rules splitPath' branches'
      | _ =>
        return tree

/-- Apply a full decomposition to the tree, refining step by step. -/
partial def coverDecomposed (patSoFar : CovPattern) (dec : List (Name × Nat × List Nat))
    (tree : CoverageTree) : MetaM CoverageTree := do
  match dec with
  | [] => return tree
  | (c, arity, path) :: rest =>
    let tree' ← coverSingleLayer c arity path patSoFar tree
    let patSoFar' := insertAtPath patSoFar path c arity
    coverDecomposed patSoFar' rest tree'

/-- Refine tree structure for one rule (decompose + split). No labeling. -/
partial def refineTree (pat : CovPattern) (tree : CoverageTree) : MetaM CoverageTree := do
  let dec := decompose pat
  coverDecomposed .wild dec tree

/-- Build the complete coverage tree from all rules' patterns.
    Phase 1: refine tree structure from all rules' patterns.
    Phase 2: label leaves with which rules cover them.
    `initPat` provides the initial root shape (with `output` markers at output positions). -/
partial def coverPatterns (rules : List (Name × CovPattern)) (initPat : CovPattern := .wild) : MetaM CoverageTree := do
  -- Phase 1: build tree structure
  let mut tree : CoverageTree := .leaf initPat []
  for (_, pat) in rules do
    tree ← refineTree pat tree
  -- Phase 2: label leaves with covering rules
  for (rule, pat) in rules do
    tree := labelSubpatterns rule pat tree
  return tree

----------------------------------------------
-- Dep-aware schedule scoring
----------------------------------------------


----------------------------------------------
-- Leaf collection + scoring
----------------------------------------------

/-- Collect all leaves as (pattern, covering rule names). -/
partial def collectLeaves (tree : CoverageTree) : List (CovPattern × List Name) :=
  match tree with
  | .leaf pat rules => [(pat, rules)]
  | .node _ _ _ branches => branches.flatMap fun (_, sub) => collectLeaves sub

/-- Annotate raw leaves with ScheduleScores from the per-constructor map. -/
def annotateLeaves (leaves : List (CovPattern × List Name))
    (ctorScores : List (Name × ScheduleScore)) : List AnnotatedLeaf :=
  leaves.map fun (pat, rules) =>
    { pattern := pat
      coveringCtors := rules.filterMap fun r =>
        match ctorScores.find? (·.1 == r) with
        | some (_, score) => some (r, score)
        | none => none }

/-- Modular scoring aggregation.
    Policy: for each leaf, take the best covering constructor's score.
    Aggregate across leaves by summing the worst components.

    This is the single policy point — swap to change scoring strategy. -/
def aggregateCoverageScore (leaves : List AnnotatedLeaf) : SpecScore :=
  let uncoveredLeaf : SpecScore := ⟨1, 0, 0⟩
  let initBest : SpecScore := ⟨100, 100, 0⟩
  let leafScores := leaves.map fun leaf =>
    match leaf.coveringCtors with
    | [] => uncoveredLeaf
    | ctors =>
      ctors.foldl (fun (acc : SpecScore) (_, s) =>
        ⟨min acc.checks s.checks, min acc.unconstrained s.unconstrained, 0⟩) initBest
  leafScores.foldl (fun (acc : SpecScore) (s : SpecScore) =>
    ⟨acc.checks + s.checks, acc.unconstrained + s.unconstrained, acc.backtracking + s.backtracking⟩)
    ⟨0, 0, 0⟩

----------------------------------------------
-- MetaM entry points
----------------------------------------------

/-- Convert an Expr argument to a CovPattern node.
    Recursively descends into constructor applications. -/
private partial def exprToCovPattern (e : Expr) : MetaM CovPattern := do
  let e ← Lean.Meta.withTransparency .instances <| whnf e
  if e.isApp || e.isConst then
    let (head, args) := e.getAppFnArgs
    let env ← getEnv
    if env.isConstructor head then
      let ctorInfo ← getConstInfoCtor head
      let indInfo ← getConstInfoInduct ctorInfo.induct
      let nonParamArgs := args.toList.drop indInfo.numParams
      let subPats ← nonParamArgs.mapM exprToCovPattern
      return .ctr head subPats
    else if head == ``Char.ofNat && args.size == 1 then
      match args[0]! with
      | .lit (.natVal n) => return .ctr (Name.mkSimple s!"'{Char.ofNat n}'") []
      | _ => return .funcApp head
    else if ← isInductive head then
      return .typeVar head
    else
      return .funcApp head
  else if e.isLit then
    match e.litValue! with
    | .natVal 0 => return .ctr ``Nat.zero []
    | .natVal (n + 1) => return .ctr ``Nat.succ [← exprToCovPattern (mkRawNatLit n)]
    | .strVal s => return .ctr (Name.mkSimple s!"\"{s}\"") []
  else if e.isFVar then
    let ty ← inferType e
    if ty.isSort then
      let name ← e.fvarId!.getUserName
      return .typeVar name
    else
      return .wild
  else
    return .wild

/-- Convert one constructor's conclusion Expr to a CovPattern.
    The conclusion is `ind arg₀ arg₁ ... argₙ` (all args including params).
    Type params (whose type is Sort/Type) → `typeVar`.
    Output indices → excluded.
    Everything else → classified via `exprToCovPattern`. -/
partial def conclusionToCovPattern (indName : Name) (conclusion : Expr)
    (outputIndices : List Nat) (numParams : Nat) : MetaM CovPattern := do
  let (_, allArgs) := conclusion.getAppFnArgs
  let allArgsList := allArgs.toList
  let mut pats : List CovPattern := []
  for idx in [:allArgsList.length] do
    if idx ∈ outputIndices then
      pats := pats ++ [.output]
    else
      let arg := allArgsList[idx]!
      if idx < numParams then
        let ty ← inferType arg
        if ty.isSort then
          pats := pats ++ [.typeVar (← if arg.isFVar then arg.fvarId!.getUserName else pure (Name.mkSimple s!"param_{idx}"))]
        else
          let pat ← exprToCovPattern arg
          pats := pats ++ [pat]
      else
        let pat ← exprToCovPattern arg
        pats := pats ++ [pat]
  return .ctr indName pats

/-- Full pipeline: build coverage tree + annotate + aggregate.
    Called after all per-constructor schedules are derived.
    Uses the active scoring bundle's leaf and inductive aggregators. -/
partial def computeInductiveScore (indName : Name) (outputIndices : List Nat)
    (ctorScores : List (Name × Score)) : MetaM Score := do
  let bundle ← Scoring.getActiveScorerBundle
  let indInfo ← getConstInfoInduct indName
  let mut patterns : List (Name × CovPattern) := []
  for ctorName in indInfo.ctors do
    if ctorScores.any (·.1 == ctorName) then
      let ctorInfo ← getConstInfoCtor ctorName
      let pat ← forallTelescopeReducing ctorInfo.type fun _ conclusion => do
        conclusionToCovPattern indName conclusion outputIndices indInfo.numParams
      patterns := patterns ++ [(ctorName, pat)]
  let numAllArgs := indInfo.numParams + indInfo.numIndices
  let initChildren := (List.range numAllArgs).map fun i =>
    if i ∈ outputIndices then CovPattern.output else .wild
  let initPat := CovPattern.ctr indName initChildren
  let tree ← coverPatterns patterns initPat
  let leaves := collectLeaves tree
  -- Annotate leaves with type-erased scores and aggregate via bundle
  let annotatedLeaves := leaves.map fun (_, rules) =>
    let covering : List (Name × Score) := rules.filterMap fun r =>
      ctorScores.find? (fun x => x.1 == r) |>.map (·)
    bundle.leafAggregator covering
  return bundle.inductiveAggregator annotatedLeaves

----------------------------------------------
-- Pretty printing (for debugging traces)
----------------------------------------------

partial def ppCovPattern : CovPattern → String
  | .ctr c [] => c.componentsRev.head?.getD c |>.toString
  | .ctr c ps =>
    let shortName := c.componentsRev.head?.getD c |>.toString
    let argsStr := ", ".intercalate (ps.map ppCovPattern)
    s!"{shortName}({argsStr})"
  | .wild => "↓"
  | .output => "↑"
  | .otherLit => "⟨lit⟩"
  | .typeVar n => s!"@{n.toString}"
  | .instParam n => s!"[{n.toString}]"
  | .funcApp n => s!"({n.componentsRev.head?.getD n |>.toString} ...)"

partial def ppCoverageTree (indent : Nat := 0) : CoverageTree → String
  | .leaf pat rules =>
    let pad := "".pushn ' ' indent
    let rulesStr := ", ".intercalate (rules.map fun r => (r.componentsRev.head?.getD r).toString)
    s!"{pad}{ppCovPattern pat} : [{rulesStr}]"
  | .node pat rules _ branches =>
    let pad := "".pushn ' ' indent
    let rulesStr := ", ".intercalate (rules.map fun r => (r.componentsRev.head?.getD r).toString)
    let branchStrs := branches.map fun (_, sub) => ppCoverageTree (indent + 2) sub
    s!"{pad}{ppCovPattern pat} : [{rulesStr}]\n{"\n".intercalate branchStrs}"

end PatternCoverage