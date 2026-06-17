/-!
# Pattern Coverage Tests

Each section defines a test inductive, immediately followed by its coverage
test and expected output. This makes it easy to see what each case exercises
and what the trie/scoring produces.

## Sections
- **Basic coverage**: list splitting, Nat literals, all-wild, function apps
- **Advanced features**: polymorphism, instance params, mutual inductives, deep nesting, literals
- **Scoring strategies**: cross-strategy comparison on representative cases
- **End-to-end derivation**: full `derive_mutual` integration
-/
import Specimen.PatternCoverage
import Specimen.DeriveConstrainedProducer
import Specimen.Scoring

open Lean Meta Elab Term PatternCoverage Schedules Scoring

----------------------------------------------
-- Test harness
----------------------------------------------

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

----------------------------------------------
-- Basic coverage: list structure splitting
----------------------------------------------

-- Tests: constructors that progressively refine a List argument.
-- Expected: 3 leaves (nil, cons-nil, cons-cons) each covered by exactly one ctor.
inductive IsSorted : List Nat → Prop
  | nil : IsSorted []
  | single : ∀ x, IsSorted [x]
  | cons : ∀ x y ys, x ≤ y → IsSorted (y :: ys) → IsSorted (x :: y :: ys)

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

----------------------------------------------
-- Basic coverage: Nat literals (zero/succ)
----------------------------------------------

-- Tests: Nat constructors produce zero/succ branching in the trie.
inductive Even : Nat → Prop
  | zero : Even 0
  | succ : ∀ n, Even n → Even (n + 2)

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Even [])

----------------------------------------------
-- Basic coverage: all-wild (no splitting)
----------------------------------------------

-- Tests: when all constructors use fully general patterns (fvars only),
-- the trie has a single leaf covering everything.
inductive Reach : Nat → Nat → Prop
  | refl : ∀ x, Reach x x
  | step : ∀ x y z, Reach x y → Reach y z → Reach x z

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Reach [])

-- Generator mode: excluding output index 1 collapses the second argument.
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Reach [1])

----------------------------------------------
-- Basic coverage: function application in conclusion
----------------------------------------------

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

-- Tests: `lookup Γ x = some τ` in the conclusion becomes a funcApp node.
-- The trie cannot split on funcApp, so it remains a single leaf.
inductive HasType (Γ : List (Nat × MyTy)) : Nat → MyTy → Prop
  | found : ∀ x τ, lookup Γ x = some τ → HasType Γ x τ

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

----------------------------------------------
-- Basic coverage: multi-constructor typing relation
----------------------------------------------

-- Tests: overlapping output patterns (all three ctors share the same input
-- shape ↓), checker vs generator modes, uncovered leaves in checker mode
-- when constructors split on output positions.
inductive MyTyping : List (Nat × MyTy) → MyExp → MyTy → Prop
  | tvar : ∀ Γ x τ, HasType Γ x τ → MyTyping Γ (.var x) τ
  | tabs : ∀ Γ x e τ₁ τ₂, MyTyping ((x, τ₁) :: Γ) e τ₂ → MyTyping Γ (.abs x e) (.arrow τ₁ τ₂)
  | tapp : ∀ Γ e₁ e₂ τ₁ τ₂, MyTyping Γ e₁ (.arrow τ₁ τ₂) → MyTyping Γ e₂ τ₁ → MyTyping Γ (.app e₁ e₂) τ₂

-- Checker mode: all positions are inputs
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MyTyping [])

-- Generator with output at position 2 (type)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MyTyping [2])

----------------------------------------------
-- Basic coverage: tree structure
----------------------------------------------

inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → Nat → BinTree → BinTree

-- Tests: nested data type (BinTree) splitting in trie.
inductive IsBST : BinTree → Nat → Nat → Prop
  | leafBST : ∀ lo hi, IsBST .leaf lo hi
  | nodeBST : ∀ l r v lo hi,
      lo ≤ v → v ≤ hi →
      IsBST l lo v → IsBST r v hi →
      IsBST (.node l v r) lo hi

-- Checker mode
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``IsBST [])

-- Generator mode (output = tree at position 0)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``IsBST [0])

----------------------------------------------
-- Advanced: polymorphic type parameter
----------------------------------------------

-- Tests: type parameter α becomes a typeVar node (@α) in the pattern.
inductive Elem (α : Type) : α → List α → Prop
  | here : ∀ x xs, Elem α x (x :: xs)
  | there : ∀ x y xs, Elem α x xs → Elem α x (y :: xs)

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Elem [])

-- Generator with output at position 0 (the element)
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Elem [0])

----------------------------------------------
-- Advanced: instance parameter (DecidableEq)
----------------------------------------------

-- Tests: instance params appear as instParam nodes, not split on.
inductive UniqueList [DecidableEq α] : List α → Prop
  | nil : UniqueList []
  | cons : ∀ x xs, x ∉ xs → UniqueList xs → UniqueList (x :: xs)

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``UniqueList [])

----------------------------------------------
-- Advanced: function applications in conclusion
----------------------------------------------

-- Tests: `xs ++ [x]` in the conclusion becomes a funcApp; cannot be split.
inductive Palindrome : List Nat → Prop
  | nil : Palindrome []
  | single : ∀ x, Palindrome [x]
  | wrap : ∀ x xs, Palindrome xs → Palindrome (x :: xs ++ [x])

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Palindrome [])

----------------------------------------------
-- Advanced: mutual inductives
----------------------------------------------

mutual
inductive MutEven : Nat → Prop
  | zero : MutEven 0
  | succ : ∀ n, MutOdd n → MutEven (n + 1)
inductive MutOdd : Nat → Prop
  | succ : ∀ n, MutEven n → MutOdd (n + 1)
end

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MutEven [])
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``MutOdd [])

----------------------------------------------
-- Advanced: multiple inputs with constructors in several positions
----------------------------------------------

-- Tests: three list arguments, each split by different constructors.
inductive Interleave : List Nat → List Nat → List Nat → Prop
  | nil : Interleave [] [] []
  | left : ∀ x xs ys zs, Interleave xs ys zs → Interleave (x :: xs) ys (x :: zs)
  | right : ∀ y xs ys zs, Interleave xs ys zs → Interleave xs (y :: ys) (y :: zs)

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Interleave [])
#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Interleave [2])

----------------------------------------------
-- Advanced: deep nesting (List (List Nat))
----------------------------------------------

inductive DeepList : List (List Nat) → Prop
  | nil : DeepList []
  | cons : ∀ xs xss, DeepList xss → DeepList (xs :: xss)

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``DeepList [])

----------------------------------------------
-- Advanced: string literals
----------------------------------------------

-- Tests: string literal constructors produce literal nodes that split
-- into individual cases plus an _otherLit catch-all.
inductive Greeting : String → Prop
  | hello : Greeting "hello"
  | hi : Greeting "hi"
  | bye : Greeting "bye"
  | any : ∀ s, Greeting s

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``Greeting [])

----------------------------------------------
-- Advanced: char literals
----------------------------------------------

inductive IsVowel : Char → Prop
  | a : IsVowel 'a'
  | e : IsVowel 'e'
  | i : IsVowel 'i'

#guard_msgs(drop info) in
#eval show TermElabM _ from do IO.println (← testCoverage ``IsVowel [])

----------------------------------------------
-- Scoring strategies: cross-strategy comparison
----------------------------------------------

-- Demonstrates how the same inductive scores differently under each strategy.
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

----------------------------------------------
-- Scoring strategies: DensityScore on generator
----------------------------------------------

-- Tests: DensityScore in generator mode, where lower density is better.
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

----------------------------------------------
-- End-to-end: derive_mutual integration
----------------------------------------------

-- Tests: the full derivation pipeline produces a working generator instance.
deriving instance Plausible.Arbitrary for MyTy
deriving instance DecidableEq for MyTy
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
#guard_msgs(drop info) in
derive_mutual
  (fun a c => ∃ b, MyTyping a b c)

----------------------------------------------
-- End-to-end: inequality-guarded reject-sampling
----------------------------------------------

open Plausible

inductive Op where | o0 | o1 | o2 | o3 | o4 | o5 | o6 | o7
  deriving Repr, DecidableEq, Inhabited

def Op.toU8 : Op → UInt8
  | .o0 => 0 | .o1 => 1 | .o2 => 2 | .o3 => 3
  | .o4 => 4 | .o5 => 5 | .o6 => 6 | .o7 => 7

instance : Arbitrary Op where
  arbitrary := do
    let n ← Plausible.Gen.choose Nat 0 7 (by omega)
    pure (#[Op.o0, Op.o1, Op.o2, Op.o3, Op.o4, Op.o5, Op.o6, Op.o7].getD n.1 Op.o0)

/-- Inequality-guarded: `a`/`b` constrained ONLY by `≠`, which Specimen can
    only reject-sample. -/
inductive HasValidReduceOp : Op → Op → Prop where
  | mk : a.toU8 ≠ 0 → b.toU8 ≠ 0 → a.toU8 ≠ b.toU8 → HasValidReduceOp a b

def validReduce (a b : Op) : Bool :=
  a.toU8 != 0 && b.toU8 != 0 && a.toU8 != b.toU8

/-- Hand-written product producer enumerating valid pairs directly (cheap, always succeeds). -/
public instance a : ArbitrarySizedSuchThat _ (fun (l,r) => HasValidReduceOp l r) where
  arbitrarySizedST _ := do
    let ops := #[Op.o1, Op.o2, Op.o3, Op.o4, Op.o5, Op.o6, Op.o7]
    let i ← Plausible.Gen.choose Nat 0 6 (by omega)
    let j ← Plausible.Gen.choose Nat 0 6 (by omega)
    let a := ops.getD i.1 Op.o1
    let b := ops.getD j.1 Op.o2
    let b := if a == b then ops.getD ((j.1 + 1) % 7) Op.o2 else b
    pure (a, b)

structure R2 where
  op0 : Op
  op1 : Op
  deriving Repr, Inhabited

inductive IsValidR2 : R2 → Prop where
  | mk : HasValidReduceOp op0 op1 → IsValidR2 ⟨op0, op1⟩

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
derive_mutual (∃ (self : _), IsValidR2 self)

def drawIneqStructGen (n : Nat) (sz : Nat := 10) : IO (Nat × Nat × Nat) := do
  let g := @ArbitrarySizedSuchThat.arbitrarySizedST R2 (fun self => IsValidR2 self) _ sz
  let mut ok := 0; let mut got := 0; let mut fuel := 0
  for i in [0:n] do
    try
      let s ← Plausible.Gen.run g (sz + i)
      got := got + 1
      if validReduce s.op0 s.op1 then ok := ok + 1
    catch _ => fuel := fuel + 1
  pure (ok, got, fuel)

#eval do
  let (ok, got, fuel) ← drawIneqStructGen 200
  IO.println s!"INEQ STRUCT + derive_generator: valid={ok}/200  succeeded={got}/200  fuelOut={fuel}/200"
