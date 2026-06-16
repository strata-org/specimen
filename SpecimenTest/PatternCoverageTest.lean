import Specimen.PatternCoverage
import Specimen.DeriveConstrainedProducer
import Specimen.Scoring

open Lean Meta Elab Term PatternCoverage Schedules Scoring

-- Test inductives

inductive IsSorted : List Nat → Prop
  | nil : IsSorted []
  | single : ∀ x, IsSorted [x]
  | cons : ∀ x y ys, x ≤ y → IsSorted (y :: ys) → IsSorted (x :: y :: ys)

inductive MyExp
  | var : Nat → MyExp
  | abs : Nat → MyExp → MyExp
  | app : MyExp → MyExp → MyExp

inductive MyTy
  | base : MyTy
  | arrow : MyTy → MyTy → MyTy

def lookup (Γ : List (Nat × MyTy)) (x : Nat) :=
  match Γ with
  | [] => none
  | ((x',τ) :: Γ) => if x = x' then some τ else lookup Γ x

-- Function app in conclusion args (lookup)
inductive HasType (Γ : List (Nat × MyTy)) : Nat → MyTy → Prop
  | found : ∀ x τ, lookup Γ x = some τ → HasType Γ x τ

inductive MyTyping : List (Nat × MyTy) → MyExp → MyTy → Prop
  | tvar : ∀ Γ x τ, HasType Γ x τ → MyTyping Γ (.var x) τ
  | tabs : ∀ Γ x e τ₁ τ₂, MyTyping ((x, τ₁) :: Γ) e τ₂ → MyTyping Γ (.abs x e) (.arrow τ₁ τ₂)
  | tapp : ∀ Γ e₁ e₂ τ₁ τ₂, MyTyping Γ e₁ (.arrow τ₁ τ₂) → MyTyping Γ e₂ τ₁ → MyTyping Γ (.app e₁ e₂) τ₂

inductive Even : Nat → Prop
  | zero : Even 0
  | succ : ∀ n, Even n → Even (n + 2)

inductive Reach : Nat → Nat → Prop
  | refl : ∀ x, Reach x x
  | step : ∀ x y z, Reach x y → Reach y z → Reach x z

inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → Nat → BinTree → BinTree

inductive IsBST : BinTree → Nat → Nat → Prop
  | leafBST : ∀ lo hi, IsBST .leaf lo hi
  | nodeBST : ∀ l r v lo hi,
      lo ≤ v → v ≤ hi →
      IsBST l lo v → IsBST r v hi →
      IsBST (.node l v r) lo hi

-- Polymorphic: type parameter α
inductive Elem (α : Type) : α → List α → Prop
  | here : ∀ x xs, Elem α x (x :: xs)
  | there : ∀ x y xs, Elem α x xs → Elem α x (y :: xs)

-- Instance parameter: DecidableEq
inductive UniqueList [DecidableEq α] : List α → Prop
  | nil : UniqueList []
  | cons : ∀ x xs, x ∉ xs → UniqueList xs → UniqueList (x :: xs)

-- Function applications in conclusion
inductive Palindrome : List Nat → Prop
  | nil : Palindrome []
  | single : ∀ x, Palindrome [x]
  | wrap : ∀ x xs, Palindrome xs → Palindrome (x :: xs ++ [x])

-- Mutual inductives
mutual
inductive MutEven : Nat → Prop
  | zero : MutEven 0
  | succ : ∀ n, MutOdd n → MutEven (n + 1)
inductive MutOdd : Nat → Prop
  | succ : ∀ n, MutEven n → MutOdd (n + 1)
end

-- Nested constructors and multiple type params
inductive Interleave : List Nat → List Nat → List Nat → Prop
  | nil : Interleave [] [] []
  | left : ∀ x xs ys zs, Interleave xs ys zs → Interleave (x :: xs) ys (x :: zs)
  | right : ∀ y xs ys zs, Interleave xs ys zs → Interleave xs (y :: ys) (y :: zs)



-- Deep nesting
inductive DeepList : List (List Nat) → Prop
  | nil : DeepList []
  | cons : ∀ xs xss, DeepList xss → DeepList (xs :: xss)

-- String literals
inductive Greeting : String → Prop
  | hello : Greeting "hello"
  | hi : Greeting "hi"
  | bye : Greeting "bye"
  | any : ∀ s, Greeting s

-- Char literal
inductive IsVowel : Char → Prop
  | a : IsVowel 'a'
  | e : IsVowel 'e'
  | i : IsVowel 'i'

def testCoverage (indName : Name) (outputIndices : List Nat) : TermElabM String := do
  let bundle ← Scoring.getActiveScorerBundle
  let indInfo ← getConstInfoInduct indName
  let mut patterns : List (Name × CovPattern) := []
  for ctorName in indInfo.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let pat ← forallTelescopeReducing ctorInfo.type fun _ conclusion => do
      conclusionToCovPattern indName conclusion outputIndices indInfo.numParams
    patterns := patterns ++ [(ctorName, pat)]

  let mut result := s!"=== Coverage for {indName} (outputs: {outputIndices}) ===\n"
  result := result ++ s!"Constructors and their input patterns:\n"
  for (name, pat) in patterns do
    let shortName := name.componentsRev.head?.getD name |>.toString
    result := result ++ s!"  {shortName}: {ppCovPattern pat}\n"

  let numAllArgs := indInfo.numParams + indInfo.numIndices
  let initChildren := (List.range numAllArgs).map fun i =>
    if i ∈ outputIndices then CovPattern.output else .wild
  let initPat := CovPattern.ctr indName initChildren
  let tree ← coverPatterns patterns initPat
  result := result ++ s!"\nCoverage tree:\n{ppCoverageTree 2 tree}\n"

  let leaves := collectLeaves tree

  -- Derive real schedules and get per-constructor scores
  let memo ← IO.mkRef ({} : Std.HashMap SpecKey MemoEntry)
  let deriveSort := if outputIndices.isEmpty then DeriveSort.Checker else .Generator
  let specKey : SpecKey := { inductiveName := indName, outputIndices := outputIndices, deriveSort := deriveSort }
  let _ ← deriveBestInductiveSchedule specKey memo
  let memoState : Std.HashMap SpecKey MemoEntry ← memo.get
  let ctorScores : List (Name × Score) := match memoState[specKey]? with
    | some (.done indSched) => indSched.ctorStats.map fun (name, _, _, score) => (name, score)
    | _ => []

  -- Use the bundle to aggregate leaf + inductive scores
  let leafScores := leaves.map fun (pat, rules) =>
    let covering : List (Name × Score) := rules.filterMap fun r =>
      ctorScores.find? (fun x => x.1 == r)
    let leafScore := bundle.leafAggregator covering
    (pat, covering, leafScore)

  result := result ++ s!"\nLeaves ({leafScores.length}):\n"
  for (pat, covering, _leafScore) in leafScores do
    if covering.isEmpty then
      result := result ++ s!"  {ppCovPattern pat} → UNCOVERED\n"
    else
      let ctorsStr := ", ".intercalate (covering.map fun (r, s) =>
        let shortName := r.componentsRev.head?.getD r |>.toString
        s!"{shortName}({bundle.reprScore s})")
      result := result ++ s!"  {ppCovPattern pat} → [{ctorsStr}]\n"

  let finalScore := bundle.inductiveAggregator (leafScores.map fun (_, _, s) => s)
  result := result ++ s!"\nInductive score: {bundle.reprScore finalScore}\n"
  return result

-- Basic: list structure splitting
/--
info: === Coverage for IsSorted (outputs: []) ===
Constructors and their input patterns:
  nil: IsSorted(nil)
  single: IsSorted(cons(↓, nil))
  cons: IsSorted(cons(↓, cons(↓, ↓)))

Coverage tree:
  IsSorted(↓) : []
    IsSorted(nil) : [nil]
    IsSorted(cons(↓, ↓)) : []
      IsSorted(cons(↓, nil)) : [single]
      IsSorted(cons(↓, cons(↓, ↓))) : [cons]

Leaves (3):
  IsSorted(nil) → [nil({ checks := 0, length := 0, unconstrained := 0 })]
  IsSorted(cons(↓, nil)) → [single({ checks := 0, length := 0, unconstrained := 0 })]
  IsSorted(cons(↓, cons(↓, ↓))) → [cons({ checks := 2, length := 2, unconstrained := 0 })]

Inductive score: { checks := 2, length := 2, unconstrained := 0 }

-/
#guard_msgs in
#eval show TermElabM _ from do IO.println (← testCoverage ``IsSorted [])

-- Nat literals (zero/succ)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Even [])

-- All-wild (no splitting needed)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Reach [])

-- Generator mode (output excluded)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Reach [1])

-- Multiple constructors, uncovered leaf
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MyTyping [])

-- Output position with constructor splitting
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MyTyping [2])

-- Tree structure splitting
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``IsBST [])

-- Generator for tree (all inputs wild)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``IsBST [0])

-- Polymorphic type param
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Elem [])

-- Polymorphic with output
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Elem [0])

-- Instance parameter (DecidableEq)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``UniqueList [])

-- Function application in conclusion (xs ++ [x])
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Palindrome [])

-- Mutual inductives
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MutEven [])
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MutOdd [])

-- Multiple inputs with constructors in several positions
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Interleave [])
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Interleave [2])

-- Function app in conclusion (Γ x = some τ)
/--
info: === Coverage for HasType (outputs: []) ===
Constructors and their input patterns:
  found: HasType(↓, ↓, ↓)

Coverage tree:
  HasType(↓, ↓, ↓) : [found]

Leaves (1):
  HasType(↓, ↓, ↓) → [found({ checks := 1, length := 1, unconstrained := 0 })]

Inductive score: { checks := 1, length := 1, unconstrained := 0 }

-/
#guard_msgs in
#eval show TermElabM _ from do IO.println (← testCoverage ``HasType [])

-- Deep nesting (List (List Nat))
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``DeepList [])

-- String literals
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Greeting [])

-- Char literals
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``IsVowel [])

----------------------------------------------
-- Scoring strategy tests
----------------------------------------------

def testStrategy (indName : Name) (outputIndices : List Nat) (bundle : ScorerBundle) : TermElabM String := do
  let indInfo ← getConstInfoInduct indName
  let mut patterns : List (Name × CovPattern) := []
  for ctorName in indInfo.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let pat ← forallTelescopeReducing ctorInfo.type fun _ conclusion => do
      conclusionToCovPattern indName conclusion outputIndices indInfo.numParams
    patterns := patterns ++ [(ctorName, pat)]
  let numAllArgs := indInfo.numParams + indInfo.numIndices
  let initChildren := (List.range numAllArgs).map fun i =>
    if i ∈ outputIndices then CovPattern.output else .wild
  let tree ← coverPatterns patterns (.ctr indName initChildren)
  let leaves := collectLeaves tree

  -- Get real schedules
  let memo ← IO.mkRef ({} : Std.HashMap SpecKey MemoEntry)
  let ds := if outputIndices.isEmpty then DeriveSort.Checker else .Generator
  let key : SpecKey := { inductiveName := indName, outputIndices, deriveSort := ds }
  let _ ← deriveBestInductiveSchedule key memo
  let memoState : Std.HashMap SpecKey MemoEntry ← memo.get
  let ctorScheds : List (Name × List ScheduleStep) := match memoState[key]? with
    | some (.done s) =>
      (s.baseSchedules ++ s.recSchedules).map fun (n, schedule) => (n, schedule.1)
    | _ => []

  -- Score each ctor with the bundle
  let inputVarSet : Std.HashSet Name := match memoState[key]? with
    | some (.done s) =>
      let inputNames := s.argNames.filter fun n =>
        key.outputIndices.all fun idx => s.argNames.getD idx `_ != n
      Std.HashSet.ofList inputNames
    | _ => {}
  let ctorScores : List (Name × Score) := ctorScheds.map fun (name, steps) =>
    let stepScores := steps.map fun step => bundle.stepScorer key memoState inputVarSet step
    (name, bundle.scheduleScorer stepScores)

  -- Leaf + inductive aggregation
  let leafScores := leaves.map fun (_, rules) =>
    let covering : List (Name × Score) := rules.filterMap fun r =>
      ctorScores.find? (fun x => x.1 == r)
    bundle.leafAggregator covering
  let final := bundle.inductiveAggregator leafScores

  return s!"  [{bundle.scoreTypeName}] {bundle.reprScore final}"

-- Compare strategies
/--
info: === Strategy comparison for IsSorted (checker) ===
  [Scoring.DefaultScore] { checks := 2, length := 5, unconstrained := 0 }
  [Scoring.WorstLeafScore] { checks := 2, length := 3, unconstrained := 0 }
  [Scoring.DensityScore] { density := Scoring.Density.Checking, varDeps := 4, forChecker := true }

=== Strategy comparison for Interleave (checker) ===
  [Scoring.DefaultScore] { checks := 10, length := 15, unconstrained := 0 }
  [Scoring.WorstLeafScore] { checks := 2, length := 4, unconstrained := 0 }
  [Scoring.DensityScore] { density := Scoring.Density.Checking, varDeps := 12, forChecker := true }

=== Strategy comparison for IsBST (checker) ===
  [Scoring.DefaultScore] { checks := 4, length := 6, unconstrained := 0 }
  [Scoring.WorstLeafScore] { checks := 4, length := 5, unconstrained := 0 }
  [Scoring.DensityScore] { density := Scoring.Density.Checking, varDeps := 6, forChecker := true }

=== Strategy comparison for Typing (output type) ===
  [Scoring.DefaultScore] { checks := 0, length := 3, unconstrained := 2 }
  [Scoring.WorstLeafScore] { checks := 0, length := 3, unconstrained := 2 }
  [Scoring.DensityScore] { density := Scoring.Density.Total, varDeps := 2, forChecker := false }

-/
#guard_msgs in
#eval show TermElabM _ from do
  let bundles ← scorerBundles.get
  let mut output := "=== Strategy comparison for IsSorted (checker) ===\n"
  for bundle in bundles do
    output := output ++ (← testStrategy ``IsSorted [] bundle) ++ "\n"
  output := output ++ "\n=== Strategy comparison for Interleave (checker) ===\n"
  for bundle in bundles do
    output := output ++ (← testStrategy ``Interleave [] bundle) ++ "\n"
  output := output ++ "\n=== Strategy comparison for IsBST (checker) ===\n"
  for bundle in bundles do
    output := output ++ (← testStrategy ``IsBST [] bundle) ++ "\n"
  output := output ++ "\n=== Strategy comparison for Typing (output type) ===\n"
  for bundle in bundles do
    output := output ++ (← testStrategy ``MyTyping [0, 1 , 2] bundle) ++ "\n"
  IO.println output


/--
info: === Coverage for MyTyping (outputs: [1, 2]) ===
Constructors and their input patterns:
  tvar: MyTyping(↓, ↑, ↑)
  tabs: MyTyping(↓, ↑, ↑)
  tapp: MyTyping(↓, ↑, ↑)

Coverage tree:
  MyTyping(↓, ↑, ↑) : [tapp, tabs, tvar]

Leaves (1):
  MyTyping(↓, ↑, ↑) → [tapp({ density := Scoring.Density.Partial, varDeps := 3, forChecker := false }), tabs({ density := Scoring.Density.Partial, varDeps := 3, forChecker := false }), tvar({ density := Scoring.Density.Backtracking, varDeps := 1, forChecker := false })]

Inductive score: { density := Scoring.Density.Partial, varDeps := 3, forChecker := false }

-/
#guard_msgs in
set_option specimen.scoreType "Scoring.DensityScore" in
#eval show TermElabM _ from do IO.println (← testCoverage ``MyTyping [1,2])
deriving instance Plausible.Arbitrary for MyTy
deriving instance DecidableEq for MyTy
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
#guard_msgs(drop info) in
derive_mutual
  (fun a c => ∃ b, MyTyping a b c)
