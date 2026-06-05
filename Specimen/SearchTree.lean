import Specimen.LazyRoseTree
import Specimen.LazyList
namespace SearchTree
-- Chunks structure for dependency-aware ordering
structure Chunks' α where
  beforeAnchor : List α
  anchors : List (List α)
  numAnchors : Nat
  deriving Repr

private def getNeighbors {α v} [BEq α] [BEq v] (hyps : List (α × List v)) : List (α × List (α × List v)) :=
  hyps.map (fun (hyp, vars) =>
    let neighbors := hyps.filterMap (fun (otherHyp, otherVars) =>
      if hyp == otherHyp then .none else
      let vars' := vars.filter (otherVars.contains ·)
      if vars'.isEmpty then
        .none
      else
        .some (otherHyp, vars'))
    (hyp, neighbors))

private def splitIntoChunks {α} [BEq α] (order : List α) (anchors : List α) : Chunks' α :=
  let (beforeAnchor, rest) := order.span (!anchors.contains ·)
  let rec split (remaining : List α) (currentChunk : List α) (result : List (List α)) : List (List α) :=
    match remaining with
    | [] => currentChunk.reverse :: result |>.reverse
    | x :: xs =>
      if anchors.contains x then
        split xs [x] (currentChunk.reverse :: result)
      else
        split xs (x :: currentChunk) result
  let anchors :=
    match rest with
    | firstAnchor :: rest' => split rest' [firstAnchor] []
    | [] => []
  let numAnchors := anchors.length
  ⟨beforeAnchor, anchors, numAnchors⟩

-- Create lazy search tree for enumDependencySatisfyingOrderings
def enumDependencySatisfyingOrderingsTree {α v} [BEq α] [Repr α] [Repr v] [BEq v]
  (hyps : List (α × List v)) : LazyRoseTree (List α) :=
  let neighbors := getNeighbors hyps

  let rec buildTree (remaining : List (α × List (α × List v))) (currentOrder : List α) : LazyRoseTree (List α) :=
    -- dbg_trace s!"leaking info on {repr currentOrder}\n"
    match remaining with
    | [] => ⟨currentOrder, ⟨fun _ => []⟩⟩
    | (h, deps) :: rest =>
      let inOrder := Id.run do
        let mut inOrder := []
        let mut env := []
        for (h', vs) in deps do
          if !(vs.removeAll env).isEmpty then
            inOrder := h' :: inOrder
          env := vs ++ env
        return inOrder

      -- let inOrder := deps.filter (currentOrder.contains ·)
      let chunks := splitIntoChunks currentOrder inOrder
      let insertionPositions := List.range (chunks.numAnchors + 1)

      ⟨currentOrder, ⟨fun _ =>
        insertionPositions.map fun pos =>
        let newChunks := {chunks with anchors := chunks.anchors.insertIdx pos [h], numAnchors := chunks.numAnchors + 1}
        let newOrder := newChunks.beforeAnchor ++ newChunks.anchors.flatten
        buildTree rest newOrder⟩⟩

  buildTree neighbors []



-- Prune tree with global best score state
partial def pruneTreeWithScore {α σ} [LT σ] [Min σ] [DecidableRel (fun a b : σ => a < b)] (tree : LazyRoseTree α) (score : α → σ) (bestScore : σ) : Option (LazyRoseTree α × σ) :=

  let nodeScore := score tree.val
  if nodeScore > bestScore then none else
  let children := tree.children.get
  if children.isEmpty then
    -- Leaf node: check score and update best
    some (⟨tree.val, ⟨fun _ => []⟩⟩, nodeScore)
  else Id.run do
    -- Internal node: prune children with scores >= bestScore
    let mut prunedChildren := []
    let mut finalBest := bestScore
    let children := children.toArray.qsort (fun a b => score a.val < score b.val)
    for child in children do
      match pruneTreeWithScore child score finalBest with
      | none => continue
      | some (prunedChild, childBest) =>
        prunedChildren := prunedChild :: prunedChildren
        finalBest := min finalBest childBest

    if prunedChildren.isEmpty then none else
    some (⟨tree.val, ⟨fun _ => prunedChildren.reverse⟩⟩, finalBest)

-- Prune tree with global best score state
partial def minTreePruning {α σ} [LT σ] [Min σ] [DecidableRel (fun a b : σ => a < b)] (tree : LazyRoseTree α) (score : α → σ) (bestScore : σ) : Option (α × σ) :=

  let nodeScore := score tree.val
  if nodeScore > bestScore then none else
  let children := tree.children.get
  if children.isEmpty then
    -- Leaf node: check score and update best
    some (tree.val, nodeScore)
  else Id.run do
    -- Internal node: prune children with scores >= bestScore
    let mut bestChild := none
    let mut bestScore := bestScore
    let children := children.toArray.qsort (fun a b => score a.val < score b.val)
    for child in children do
      match minTreePruning child score bestScore with
      | none => continue
      | some (bestA, childBestScore) =>
        if childBestScore < bestScore then
          bestChild := some bestA
          bestScore := childBestScore

    bestChild.map (fun a => (a,bestScore))

-- Prune tree and tag each value with its score
def pruneTreeWithScoredValues {α : Type} {σ : Type} [LT σ] [Min σ] [Ord σ] [DecidableRel (fun a b : σ => a < b)] [Repr σ] [Inhabited (α × σ)]
                                      (tree : LazyRoseTree α) (score : α → σ) (bestScore : σ)
                                      : Option (LazyRoseTree (α × σ) × σ) :=
  pruneTreeWithScore (tree.map fun a => (a, score a)) (fun a => a.snd) bestScore

-- Original scoring function for simple variable lists
def scoreOrdering {α v} [BEq α] [BEq v] (hypVarMap : List (α × List v)) (ordering : List α) : Nat :=
  let rec go (remaining : List α) (env : List v) (checks : Nat) : Nat :=
    match remaining with
    | [] => checks
    | hyp :: rest =>
      match hypVarMap.find? (fun (h, _) => h == hyp) with
      | none => go rest env (checks + 1)  -- Unknown hyp = check
      | some (_, vars) =>
        if vars.all (env.contains ·) then
          go rest (vars ++ env) (checks + 1)  -- All vars bound = check
        else
          go rest (vars ++ env) checks  -- Generate vars, no check
  go ordering [] 0

-- Test with simple example
#guard_msgs(error, drop info) in
#eval
  let tree := enumDependencySatisfyingOrderingsTree [("H",[1]),("I",[1,2]),("J",[2])]
  tree



-- Lexicographic ordering for Nat × Nat
instance : LT (Nat × Nat) where
  lt a b := Prod.Lex (· < ·) (· < ·) a b

instance : DecidableRel (fun a b : Nat × Nat => a < b) := Prod.Lex.instDecidableRelOfDecidableEq

instance : Min (Nat × Nat) where
  min a b := if a < b then a else b

instance : Ord (Nat × Nat) where
  compare a b :=
    match compare a.1 b.1 with
    | Ordering.lt => Ordering.lt
    | Ordering.gt => Ordering.gt
    | Ordering.eq => compare a.2 b.2

abbrev LexNat := Nat × Nat

-- Variable expression types
inductive VarExpr (v : Type) where
| Var : v → VarExpr v  -- Single variable
| Ctor : List v → VarExpr v  -- Contains constructor, but not function
| Func : List v → VarExpr v  -- Contains function application
  deriving BEq, Repr

-- Extract all variables from a VarExpr
def extractVars {α} [BEq α] : VarExpr α → List α
| .Var v => [v]
| .Ctor args => args
| .Func args => args

-- Check if VarExpr contains function applications
partial def containsFunc : VarExpr α → Bool
| .Func .. => true
| _ => false

-- Extensible scoring function with constructor/function support
def scoreOrderingAdvanced {α v} [BEq α] [BEq v] (hypVarMap : List (α × List (VarExpr v))) (ordering : List α) : Nat :=
  let processed := ordering.filterMap (fun h => hypVarMap.find? (fun (h', _) => h == h'))
  let unprocessed := hypVarMap.filter (fun (h, _) => !ordering.contains h)
  let rec go (remaining : List (α × List (VarExpr v))) (env : List v) (arbitrary : List v) (checks : Nat) : Nat :=
    match remaining with
    | [] =>
      -- Add lower bound for remaining hypotheses that will be checks
      let forcedChecks := unprocessed.filter (fun (_, varExprs) =>
        varExprs.flatMap extractVars |>.all env.contains)
      -- Filter forced checks by whether they use any arbitrary variable
      let guaranteedChecks := forcedChecks.filter (fun (_, varExprs) =>
        (varExprs.flatMap extractVars).any (!arbitrary.contains ·))
      checks + guaranteedChecks.length
    | (_, varExprs) :: rest =>
      let producers := varExprs.filter (fun x => !containsFunc x && (extractVars x).all fun v => !env.contains v)
      let newVars := varExprs.flatMap extractVars
      let newArbitrary := newVars.filter (!env.contains ·)
      if producers.isEmpty then
        go rest (env ++ newVars) arbitrary (checks + 1)
      else
        go rest (env ++ newVars) (arbitrary ++ newArbitrary) checks
  go processed [] [] 0

-- Get current environment from partial ordering
def getCurrentEnv {α v} [BEq α] [BEq v] (currentOrder : List α) (hypVarMap : List (α × List v)) : List v :=
  let rec go (order : List α) (env : List v) : List v :=
    match order with
    | [] => env
    | hyp :: rest =>
      match hypVarMap.find? (fun (h, _) => h == hyp) with
      | some (_, vars) => go rest (vars ++ env)
      | none => go rest env
  go currentOrder []

-- Get variables that could be arbitrarily generated in current ordering
def getArbitraryVars {α v} [BEq α] [BEq v] (currentOrder : List α) (hypVarMap : List (α × List v)) : List v :=
  let rec go (order : List α) (env : List v) (arbitrary : List v) : List v :=
    match order with
    | [] => arbitrary
    | hyp :: rest =>
      match hypVarMap.find? (fun (h, _) => h == hyp) with
      | some (_, vars) =>
        let newVars := vars.filter (!env.contains ·)  -- Variables this hyp can generate
        go rest (vars ++ env) (newVars ++ arbitrary)
      | none => go rest env arbitrary
  go currentOrder [] []
-- Count guaranteed arbitrary variables
def countGuaranteedArbitraries {α v} [BEq α] [BEq v] (currentOrder : List α) (remaining : List (α × List v)) (hypVarMap : List (α × List v)) : Nat :=
  let remainingVars := remaining.flatMap (fun (_, vars) => vars)

  let rec collectArbitraryVars (order : List α) (env : List v) (arbitraryCount : Nat) : Nat :=
    match order with
    | [] => arbitraryCount
    | hyp :: rest =>
      match hypVarMap.find? (fun (h, _) => h == hyp) with
      | some (_, vars) =>
        let newArbitraries := vars.filter (fun v => !env.contains v && !remainingVars.contains v)
        let newEnv := vars ++ env
        collectArbitraryVars rest newEnv (arbitraryCount + newArbitraries.length)
      | none => collectArbitraryVars rest env arbitraryCount

  let arbitraryCount := collectArbitraryVars currentOrder [] 0
  max 0 (arbitraryCount - 1)

-- Lower bound score for internal nodes (primary: checks, secondary: -arbitraries)
def lowerBoundScore {α v} [BEq α] [BEq v] (currentOrder : List α) (remaining : List (α × List v)) (hypVarMap : List (α × List v)) : LexNat :=
  let currentScore := scoreOrdering hypVarMap currentOrder
  let currentEnv := getCurrentEnv currentOrder hypVarMap
  let arbitraryVars := getArbitraryVars currentOrder hypVarMap

  -- Count hypotheses that will definitely be checks
  let forcedChecks := remaining.filter (fun (_, vars) =>
    vars.all (currentEnv.contains ·))  -- All vars already bound

  let guaranteedChecks := forcedChecks.filter (fun (_, vars) =>
    let generatableVars := vars  -- For simple case, all vars are generatable
    generatableVars.any (!arbitraryVars.contains ·))  -- Can't be arbitrary

  let primaryScore := currentScore + guaranteedChecks.length
  let secondaryScore := countGuaranteedArbitraries currentOrder remaining hypVarMap
  (primaryScore, secondaryScore)

-- Lexicographic scoring: (primary: checks, secondary: -arbitraries)
def scoreOrderingLex {α v} [BEq α] [BEq v] (hypVarMap : List (α × List v)) (ordering : List α) : LexNat :=
  if ordering.length == hypVarMap.length then
    -- Complete ordering: count actual arbitrary variables
    let arbitraryVars := getArbitraryVars ordering hypVarMap
    (scoreOrdering hypVarMap ordering, arbitraryVars.length)
  else
    -- Partial ordering: use lower bound
    let remaining := hypVarMap.filter (fun (h, _) => !ordering.contains h)
    lowerBoundScore ordering remaining hypVarMap

-- Optimized scoring with cached computations
def scoreOrderingOptimized {α v} [BEq α] [BEq v] (hypVarMap : List (α × List v)) (ordering : List α) : LexNat :=
  if ordering.length == hypVarMap.length then
    -- Complete ordering: optimized computation
    let rec go (order : List α) (env : List v) (checks : Nat) (arbitraries : Nat) : Nat × Nat :=
      match order with
      | [] => (checks, arbitraries)
      | hyp :: rest =>
        match hypVarMap.find? (fun (h, _) => h == hyp) with
        | some (_, vars) =>
          let unboundVars := vars.filter (!env.contains ·)
          let newEnv := vars ++ env
          if unboundVars.isEmpty then
            go rest newEnv (checks + 1) arbitraries
          else
            go rest newEnv checks (arbitraries + unboundVars.length)
        | none => go rest env (checks + 1) arbitraries
    go ordering [] 0 0
  else
    -- Partial ordering: use optimized lower bound
    let remaining := hypVarMap.filter (fun (h, _) => !ordering.contains h)
    let currentScore := scoreOrdering hypVarMap ordering
    let secondaryScore := countGuaranteedArbitraries ordering remaining hypVarMap
    (currentScore, secondaryScore)

-- Augmented scoring function with lexicographic lower bounds
def scoreOrderingWithLowerBound {α v} [BEq α] [BEq v] (hypVarMap : List (α × List v)) (ordering : List α) : LexNat :=
  scoreOrderingOptimized hypVarMap ordering

-- Function to test pruning with hypothesis-variable mapping
def testPruning {α v} [BEq α] [Repr α] [Repr v] [BEq v] [Hashable v] (hypVarMap : List (α × List v)) (maxScore : Nat) :=
  let tree := enumDependencySatisfyingOrderingsTree hypVarMap
  let scoreFunc := scoreOrdering hypVarMap
  pruneTreeWithScore tree scoreFunc maxScore

-- Function to test pruning with scored values
def testPruningWithScores {α v} [BEq α] [Repr α] [Repr v] [BEq v] [Hashable v] (hypVarMap : List (α × List v)) (maxScore : Nat) :=
  let tree := enumDependencySatisfyingOrderingsTree hypVarMap
  let scoreFunc := scoreOrdering hypVarMap
  pruneTreeWithScoredValues tree scoreFunc maxScore

-- Function to test pruning with lexicographic scoring (lower bounds)
def testPruningWithLexScoring {α v} [BEq α] [Repr α] [Repr v] [BEq v] (hypVarMap : List (α × List v)) (maxScore : LexNat) :=
  let tree := enumDependencySatisfyingOrderingsTree hypVarMap
  let scoreFunc := scoreOrderingWithLowerBound hypVarMap
  pruneTreeWithScoredValues tree scoreFunc maxScore


#guard_msgs(error, drop info) in
#eval enumDependencySatisfyingOrderingsTree [("H", [1]), ("I", [1,2]), ("J", [2])]
-- Example 1: Simple case
#guard_msgs(error, drop info) in
#eval testPruning [("H", [1]), ("I", [1,2]), ("J", [2])] 5

-- Example 1b: Simple case with scored values
#guard_msgs(error, drop info) in
#eval testPruningWithScores [("H", [1]), ("I", [1,2]), ("J", [2])] 5

#guard_msgs(error, drop info) in
#eval testPruningWithLexScoring [("H", [1]), ("I", [1,2]), ("J", [2])] (2, 1)

-- Example 2: STLC TApp constructor with VarExpr
-- typing Γ e1 (Fun τ1 τ2) has constructor Fun constraining τ1, τ2
-- typing Γ e2 τ1 has simple variable τ1
#guard_msgs(error, drop info) in
#eval
  let hypMapVarExpr := [("typing_e1", [VarExpr.Var "e1", .Ctor ["tau1", "tau2"]]),
                        ("typing_e2", [.Var "e2", .Var "tau1"])]
  let hypMapFlat := [("typing_e1", ["e1", "tau1", "tau2"]), ("typing_e2", ["e2", "tau1"])]
  let tree := enumDependencySatisfyingOrderingsTree hypMapFlat
  let scoreFunc := scoreOrderingAdvanced hypMapVarExpr
  pruneTreeWithScoredValues tree scoreFunc 2

-- Count total nodes in a tree
partial def countNodes {α} (tree : LazyRoseTree α) : Nat :=
  1 + (tree.children.get.map countNodes).foldl (· + ·) 0

-- Count leaf nodes in a tree
partial def countLeaves {α} (tree : LazyRoseTree α) : Nat :=
  let children := tree.children.get
  if children.isEmpty then 1 else (children.map countLeaves).foldl (· + ·) 0

-- Analytical tree size calculation matching buildTree's dynamic anchor computation
def calculateTreeSize {α v} [BEq α] [BEq v] (hyps : List (α × List v)) : Nat × Nat :=
  let neighbors := getNeighbors hyps

  let rec countTree (remaining : List (α × List (α × List v))) (currentOrder : List α) : Nat × Nat :=
    match remaining with
    | [] => (1, 1)
    | (h, deps) :: rest =>
      let inOrder := Id.run do
        let mut inOrder := []
        let mut env := []
        for (h', vs) in deps do
          if !(vs.removeAll env).isEmpty then
            inOrder := h' :: inOrder
          env := vs ++ env
        return inOrder
      let chunks := splitIntoChunks currentOrder inOrder
      let insertionPositions := List.range (chunks.numAnchors + 1)
      insertionPositions.foldl (fun (accNodes, accLeaves) pos =>
        let newChunks := {chunks with anchors := chunks.anchors.insertIdx pos [h], numAnchors := chunks.numAnchors + 1}
        let newOrder := newChunks.beforeAnchor ++ newChunks.anchors.flatten
        let (childNodes, childLeaves) := countTree rest newOrder
        (accNodes + childNodes, accLeaves + childLeaves)
      ) (1, 0)

  countTree neighbors []

-- Measure pruning effectiveness
def measurePruning {α v} [BEq α] [Repr α] [Repr v] [BEq v] (hypVarMap : List (α × List v)) (maxScore : _) :=
  let (originalNodes, originalLeaves) := calculateTreeSize hypVarMap

  let originalTree := enumDependencySatisfyingOrderingsTree hypVarMap
  let scoreFunc := scoreOrderingLex hypVarMap
  let prunedResult := pruneTreeWithScore originalTree scoreFunc maxScore

  match prunedResult with
  | none => (originalNodes, originalLeaves, 0, 0, 100)  -- 100% pruned
  | some (prunedTree, _) =>
    let prunedNodes := countNodes prunedTree
    let prunedLeaves := countLeaves prunedTree
    let leafReduction := (originalLeaves - prunedLeaves) * 100 / originalLeaves
    (originalNodes, originalLeaves, prunedNodes, prunedLeaves, leafReduction)

-- Example 1: Simple case with pruning measurement
#guard_msgs(error, drop info) in
#eval measurePruning [("H", [1]), ("I", [1,2]), ("J", [2])] (6,0)

#guard_msgs(error, drop info) in
#eval testPruningWithScores [("H", [1]), ("I", [1,2]), ("J", [2])] 10

-- Example 1c: Simple case with lexicographic scoring
#guard_msgs(error, drop info) in
#eval testPruningWithLexScoring [("H", [1]), ("I", [1,2]), ("J", [2])] (2, 1)

-- Example 3: Many hypotheses with pruning measurement
#guard_msgs(error, drop info) in
#eval measurePruning [("H1", ["a"]), ("H2", ["a", "b"]), ("H3", ["b", "c"]),
                      ("H4", ["c", "d"]), ("H5", ["d", "e"]), ("H6", ["a", "e"])] (7,0)

#guard_msgs(error, drop info) in
#eval testPruningWithScores [("H1", ["a"]), ("H2", ["a", "b"]), ("H3", ["b", "c"]),
                      ("H4", ["c", "d"]), ("H5", ["d", "e"]), ("H6", ["a", "e"])] 3

-- Example 3b: Many hypotheses with lexicographic scoring
#guard_msgs(error, drop info) in
#eval testPruningWithLexScoring [("H1", ["a"]), ("H2", ["a", "b"]), ("H3", ["b", "c"]),
                      ("H4", ["c", "d"]), ("H5", ["d", "e"]), ("H6", ["a", "e"])] (4, 2)
def validTensorScalarOpHypotheses : List (String × List String) := [
  ("ValidHeader", ["header"]),
  ("ValidEvents", ["events"]),
  ("HasTensorScalarOpcode", ["header"]),
  ("TensorScalarValidOps", ["op0", "op1"]),
  ("TensorScalarValidTypes", ["header", "in_dtype", "out_dtype"]),
  ("TensorScalarImmediatesCheck", ["imm0_src", "imm1_src", "imm0", "imm1", "header", "in_dtype", "num_active_channels"]),
  ("TensorScalarShiftChk", ["op0", "op1", "in_dtype"]),
  ("TensorScalarTensorChk", ["src_mem_pattern", "in_dtype", "dst_mem_pattern", "out_dtype"]),
  ("TensorScalarReverseChk", []),
  ("S3d3TransposeCheck", ["header", "src_mem_pattern", "num_active_channels"]),
  ("ValidDtype_in", ["in_dtype"]),
  ("ValidDtype_out", ["out_dtype"]),
  ("ValidAluOp_op0", ["op0"]),
  ("ValidAluOp_op1", ["op1"]),
  ("HasZeroAccumCmdField", ["accumulator_cmd"]),
  ("HasValidActiveChannelRange", ["num_active_channels"]),
  ("StartAddrActiveChannels_src", ["src_mem_pattern", "num_active_channels"]),
  ("StartAddrActiveChannels_dst", ["dst_mem_pattern", "num_active_channels"]),
  ("Tensor3dValid_src", ["src_mem_pattern", "in_dtype"]),
  ("Tensor3dValid_dst", ["dst_mem_pattern", "out_dtype"])
]

-- #guard_msgs in
-- #eval measurePruning validTensorScalarOpHypotheses (9,14)

-- Lazy stream version that yields increasingly better values
partial def minTreePruningStream {α σ} [LT σ] [Min σ] [DecidableRel (fun a b : σ => a < b)] (tree : LazyRoseTree α) (score : α → σ) (bestScore : σ) : LazyList (α × σ) :=
  let nodeScore := score tree.val
  if nodeScore > bestScore then .lnil else
  let children := tree.children.get
  if children.isEmpty then
    pure (tree.val, nodeScore)
  else
    let children := children.toArray.qsort (fun a b => score a.val < score b.val)
    let rec processChildren (remaining : Array (LazyRoseTree α)) (currentBest : σ) : LazyList (α × σ) :=
      if h : 0 < remaining.size then
        let child := remaining[0]
        let rest := remaining.extract 1 remaining.size
        let childResults := minTreePruningStream child score currentBest
        match childResults with
        | .lnil => processChildren rest currentBest
        | .lcons (val, newScore) tail =>
          .lcons (val, newScore) ⟨fun _ =>
            let updatedBest := min currentBest newScore
            LazyList.append tail.get (processChildren rest updatedBest)⟩
      else .lnil
    processChildren children bestScore

-- Prune tree and tag each value with its score
def pruningStreamWithScoredValues {α : Type} {σ : Type} [LT σ] [Min σ] [Ord σ] [DecidableRel (fun a b : σ => a < b)] [Repr σ] [Inhabited (α × σ)]
                                      (tree : LazyRoseTree α) (score : α → σ) (bestScore : σ)
                                      : LazyList ((α × σ) × σ) :=
  minTreePruningStream (tree.map fun a => (a, score a)) (fun a => a.snd) bestScore

-- Enumerate dependency-satisfying orderings using pruning stream
def enumDependencySatisfyingOrderingsWithPruning {α v} [BEq α] [Repr α] [Repr v] [BEq v] [Hashable v] (hyps : List (α × List v)) : LazyList (List α) :=
  let tree := enumDependencySatisfyingOrderingsTree hyps
  let scoreFunc := scoreOrdering hyps
  minTreePruningStream tree scoreFunc (hyps.length + 1) |>.mapLazyList Prod.fst

-- Enumerate dependency-satisfying orderings using advanced scoring with VarExpr
def enumDependencySatisfyingOrderingsWithAdvancedPruning {α v} [BEq α] [Repr α] [Repr v] [BEq v] [Hashable v] (hyps : List (α × List v)) (toVarExpr : α → List (VarExpr v)) : LazyList (List α) :=
  let tree := enumDependencySatisfyingOrderingsTree hyps
  let hypMapVarExpr := hyps.map (fun (h, _) => (h, toVarExpr h))
  let scoreFunc := scoreOrderingAdvanced hypMapVarExpr
  minTreePruningStream tree scoreFunc (hyps.length + 1) |>.mapLazyList Prod.fst
