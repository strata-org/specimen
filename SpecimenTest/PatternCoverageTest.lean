import Specimen.PatternCoverage

open Lean Meta PatternCoverage Schedules

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

inductive MyTyping : List (Nat × MyTy) → MyExp → MyTy → Prop
  | tvar : ∀ Γ x τ, MyTyping Γ (.var x) τ
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

-- Function app in conclusion args (lookup)
inductive HasType (Γ : Nat → Option Nat) : Nat → Nat → Prop
  | found : ∀ x τ, Γ x = some τ → HasType Γ x τ

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

def testCoverage (indName : Name) (outputIndices : List Nat) : MetaM String := do
  let indInfo ← getConstInfoInduct indName
  let mut patterns : List (Name × CovPattern) := []
  for ctorName in indInfo.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let pat ← forallTelescopeReducing ctorInfo.type fun _ conclusion => do
      conclusionToCovPattern indName conclusion outputIndices indInfo.numParams
    patterns := patterns ++ [(ctorName, pat)]

  let mut result := s!"=== Coverage for {indName} (numParams={indInfo.numParams}, numIndices={indInfo.numIndices}, outputs: {outputIndices}) ===\n"
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

  let fakeScores : List (Name × ScheduleScore) := indInfo.ctors.zipIdx.map fun (c, i) =>
    (c, { checks := i % 3, length := 3 + i, unconstrained := i % 2 })
  let annotated := annotateLeaves leaves fakeScores

  result := result ++ s!"\nLeaves ({annotated.length}):\n"
  for leaf in annotated do
    let ctorsStr := ", ".intercalate (leaf.coveringCtors.map fun (r, s) =>
      let shortName := r.componentsRev.head?.getD r |>.toString
      s!"{shortName}({s.checks}chk/{s.length}len/{s.unconstrained}unc)")
    if leaf.coveringCtors.isEmpty then
      result := result ++ s!"  {ppCovPattern leaf.pattern} → UNCOVERED\n"
    else
      result := result ++ s!"  {ppCovPattern leaf.pattern} → [{ctorsStr}]\n"

  let score := aggregateCoverageScore annotated
  result := result ++ s!"\nAggregated SpecScore: checks={score.checks}, unconstrained={score.unconstrained}, backtracking={score.backtracking}\n"
  return result

-- Basic: list structure splitting
#eval show MetaM _ from do IO.println (← testCoverage ``IsSorted [])

-- Nat literals (zero/succ)
#eval show MetaM _ from do IO.println (← testCoverage ``Even [])

-- All-wild (no splitting needed)
#eval show MetaM _ from do IO.println (← testCoverage ``Reach [])

-- Generator mode (output excluded)
#eval show MetaM _ from do IO.println (← testCoverage ``Reach [1])

-- Multiple constructors, uncovered leaf
#eval show MetaM _ from do IO.println (← testCoverage ``MyTyping [])

-- Output position with constructor splitting
#eval show MetaM _ from do IO.println (← testCoverage ``MyTyping [2])

-- Tree structure splitting
#eval show MetaM _ from do IO.println (← testCoverage ``IsBST [])

-- Generator for tree (all inputs wild)
#eval show MetaM _ from do IO.println (← testCoverage ``IsBST [0])

-- Polymorphic type param
#eval show MetaM _ from do IO.println (← testCoverage ``Elem [])

-- Polymorphic with output
#eval show MetaM _ from do IO.println (← testCoverage ``Elem [0])

-- Instance parameter (DecidableEq)
#eval show MetaM _ from do IO.println (← testCoverage ``UniqueList [])

-- Function application in conclusion (xs ++ [x])
#eval show MetaM _ from do IO.println (← testCoverage ``Palindrome [])

-- Mutual inductives
#eval show MetaM _ from do IO.println (← testCoverage ``MutEven [])
#eval show MetaM _ from do IO.println (← testCoverage ``MutOdd [])

-- Multiple inputs with constructors in several positions
#eval show MetaM _ from do IO.println (← testCoverage ``Interleave [])
#eval show MetaM _ from do IO.println (← testCoverage ``Interleave [2])

-- Function app in conclusion (Γ x = some τ)
#eval show MetaM _ from do IO.println (← testCoverage ``HasType [])

-- Deep nesting (List (List Nat))
#eval show MetaM _ from do IO.println (← testCoverage ``DeepList [])

-- String literals
#eval show MetaM _ from do IO.println (← testCoverage ``Greeting [])

-- Char literals
#eval show MetaM _ from do IO.println (← testCoverage ``IsVowel [])
