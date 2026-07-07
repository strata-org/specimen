import Specimen.Schedules
import Lean

/-!
# Modular Scoring Framework

Scores quantify the quality of a derived schedule.  What "better" means is
defined by the active strategy — some rank lower values as better (fewer checks),
others prefer higher values (more density).

The framework is parameterized so that different scoring **strategies** can be
swapped at runtime (via `set_option specimen.scoreType`).

## Key abstractions

- **`Scorable S`** — typeclass for a concrete score type `S`.  Defines how
  scores combine (additive or max-based), compare (`isBetter`), and map to a
  [0,1] badness float for UI coloring.

- **`ScorerBundle`** — a fully type-erased collection of scoring functions,
  built from a concrete `Scorable S` via `mkScorerBundle`.  At runtime only one
  bundle is active; it is resolved by name from the global registry.

- **Scoring layers** (each a function type):
  `StepScorer` → `ScheduleScorer` → `LeafAggregator` → `InductiveAggregator`
  These compose bottom-up: score each schedule step, fold into a per-constructor
  schedule score, aggregate across coverage-trie leaves, then across all leaves
  to produce the final inductive score.

## Built-in strategies

| Name | Key idea |
|------|----------|
| `DefaultScore` | Sum of (checks, length, unconstrained) — original heuristic |
| `WorstLeafScore` | Max (not sum) across leaves — penalizes worst-case paths |
| `DensityScore` | Categorical density (Total/Partial/Backtracking/Checking) from §4 of "Testing Theorems, Fully Automatically" |
-/

namespace Scoring

open Lean Meta Schedules

----------------------------------------------
-- Core typeclass
----------------------------------------------

/-- Typeclass that defines how scores combine and compare.
    The score type is the index — different types enable different strategies.
    - `empty`: identity for `combine` (a zero-step schedule)
    - `combine`: merge two scores (e.g. sum steps, or take max)
    - `isBetter`: strict ordering used by branch-and-bound
    - `bestOf`: pick the best from a list (for leaf: best covering ctor)
    - `uncoveredPenalty`: score assigned to a leaf with no covering constructor
    - `worst`: initial upper bound for branch-and-bound (must lose to any real score)
    - `badness`: map to [0,1] for HSL color (0 = green/good, 1 = red/bad) -/
class Scorable (S : Type) where
  empty : S
  combine : S → S → S
  isBetter : S → S → Bool
  bestOf : List S → S
  uncoveredPenalty : S
  /-- Must be worse than any real schedule under `isBetter`. -/
  worst : S
  badness : S → Float

/-- Laws expected from scoring strategies used by branch-and-bound search.

`Scorable` stays executable and lightweight.  `LawfulScorable` packages the
extra invariants required by proof-carrying uses of scoring strategies. -/
class LawfulScorable (S : Type) [Scorable S] : Prop where
  /-- Adding combined work to a score should not strictly improve it. -/
  not_isBetter_combine_left :
    ∀ a b : S, ¬ Scorable.isBetter (S := S) (Scorable.combine (S := S) a b) a

  /-- Strict score comparison should be transitive. -/
  isBetter_trans :
    ∀ a b c : S,
      Scorable.isBetter (S := S) a b →
      Scorable.isBetter (S := S) b c →
      Scorable.isBetter (S := S) a c

  /-- `empty` is a left identity for `combine`. -/
  empty_combine :
    ∀ a : S, Scorable.combine (S := S) (Scorable.empty (S := S)) a = a

  /-- `empty` is a right identity for `combine`. -/
  combine_empty :
    ∀ a : S, Scorable.combine (S := S) a (Scorable.empty (S := S)) = a

  /-- The initial branch-and-bound sentinel should not beat a real candidate. -/
  not_worst_isBetter :
    ∀ a : S, ¬ Scorable.isBetter (S := S) (Scorable.worst (S := S)) a

  /-- Scores that are better according to `isBetter` should not have worse visual badness. -/
  badness_mono :
    ∀ a b : S,
      Scorable.isBetter (S := S) a b →
      Scorable.badness (S := S) a ≤ Scorable.badness (S := S) b

----------------------------------------------
-- Scorer function types (parameterized by score type)
----------------------------------------------

/-- Scores a single schedule step. Receives:
    - The current spec being derived (inductiveName + outputIndices + deriveSort)
    - The dependency memo (for looking up sub-relation scores)
    - The set of input variables (fixed at schedule start, NOT generated)
    - The step itself -/
abbrev StepScorer (S : Type) := SpecKey → Std.HashMap SpecKey MemoEntry → Std.HashSet Name → ScheduleStep → S

/-- Combines a list of step scores into a schedule-level score. -/
abbrev ScheduleScorer (S : Type) := List S → S

/-- Given a leaf's covering constructors with their scores, produce the leaf score. -/
abbrev LeafAggregator (S : Type) := List (Name × S) → S

/-- Given all leaf scores, produce the final inductive score. -/
abbrev InductiveAggregator (S : Type) := List S → S

----------------------------------------------
-- Type-erased score (Dynamic wrapper)
----------------------------------------------

-- Score is defined in Utils.lean (imported transitively via Schedules)

----------------------------------------------
-- Resolved scorer functions (operate on Score)
----------------------------------------------

/-- A resolved step scorer that produces type-erased scores. -/
abbrev ResolvedStepScorer := SpecKey → Std.HashMap SpecKey MemoEntry → Std.HashSet Name → ScheduleStep → Score

/-- A resolved schedule scorer. -/
abbrev ResolvedScheduleScorer := List Score → Score

/-- A resolved leaf aggregator. -/
abbrev ResolvedLeafAggregator := List (Name × Score) → Score

/-- A resolved inductive aggregator. -/
abbrev ResolvedInductiveAggregator := List Score → Score

----------------------------------------------
-- Default score type
----------------------------------------------

structure DefaultScore where
  checks : Nat := 0
  length : Nat := 0
  unconstrained : Nat := 0
  deriving Repr, BEq, Inhabited

deriving instance TypeName for DefaultScore

instance : Ord DefaultScore where
  compare a b :=
    match compare a.checks b.checks with
    | .eq => match compare a.length b.length with
      | .eq => compare a.unconstrained b.unconstrained
      | r => r
    | r => r

instance : LT DefaultScore := ltOfOrd

instance : Scorable DefaultScore where
  empty := {}
  combine a b := { checks := a.checks + b.checks, length := a.length + b.length, unconstrained := a.unconstrained + b.unconstrained }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { checks := 1 }
  worst := { checks := 1000, length := 1000, unconstrained := 1000 }
  badness s :=
    if s.length == 0 then 0.0
    else
      let checkRatio := Float.ofNat s.checks / Float.ofNat s.length
      let uncRatio := Float.ofNat s.unconstrained / Float.ofNat s.length
      let lengthPenalty := min 1.0 (Float.ofNat s.length / 12.0)
      min 1.0 (checkRatio * 2.0 + uncRatio * 0.5 + lengthPenalty * 0.3)

----------------------------------------------
-- Wrapping/unwrapping helpers
----------------------------------------------

def Score.wrap [TypeName S] [Repr S] (s : S) : Score :=
  { val := Dynamic.mk s, reprFn := fun d => match d.get? S with | some v => reprStr v | none => "<cast failed>" }

/-- Extract typed score from the Dynamic wrapper. Returns `default` on type mismatch. -/
unsafe def Score.unwrapImpl (S : Type) [Inhabited S] [TypeName S] (score : Score) : S :=
  match score.val.get? S with
  | some v => v
  | none => default

@[implemented_by Score.unwrapImpl]
opaque Score.unwrap (S : Type) [Inhabited S] [TypeName S] (score : Score) : S

instance : Inhabited Score where default := Score.wrap ({} : DefaultScore)

/-- Wrap a typed scorer into a ResolvedStepScorer. -/
def wrapStepScorer [Inhabited S] [TypeName S] [Repr S] (f : StepScorer S) : ResolvedStepScorer :=
  fun key memo inputVars step => Score.wrap (f key memo inputVars step)

/-- Wrap a typed schedule scorer into a ResolvedScheduleScorer. -/
def wrapScheduleScorer [Inhabited S] [TypeName S] [Repr S] (f : ScheduleScorer S) : ResolvedScheduleScorer :=
  fun scores => Score.wrap (f (scores.map (Score.unwrap S)))

/-- Wrap a typed leaf aggregator into a ResolvedLeafAggregator. -/
def wrapLeafAggregator [Inhabited S] [TypeName S] [Repr S] (f : LeafAggregator S) : ResolvedLeafAggregator :=
  fun ctors => Score.wrap (f (ctors.map fun (n, s) => (n, Score.unwrap S s)))

/-- Wrap a typed inductive aggregator into a ResolvedInductiveAggregator. -/
def wrapInductiveAggregator [Inhabited S] [TypeName S] [Repr S] (f : InductiveAggregator S) : ResolvedInductiveAggregator :=
  fun scores => Score.wrap (f (scores.map (Score.unwrap S)))

----------------------------------------------
-- Scorer registry
----------------------------------------------

/-- Pruning strategy for the SearchTree. All options use the monadic `searchBestScheduleM`
    path (with on-demand dep derivation). The strategy controls how aggressively branches
    are pruned during exploration.
    - `usePrimary`: prune with this bundle's own stepScorer/scheduleScorer/isBetter.
      Valid when scoring is monotone under variable binding (all built-in strategies).
    - `useAlternate s`: prune with a separate scorer.
    - `noPruning`: explore all branches (no pruning, but still uses monadic path).
    - `legacy`: use the old pure `possibleSchedules` path with structural check-count
      pruning. No on-demand derivation. For backwards compatibility only. -/
inductive PruneStrategy where
  | usePrimary
  | useAlternate (alt : ResolvedStepScorer × ResolvedScheduleScorer × (Score → Score → Bool) × Score)
  | noPruning
  | legacy

/-- A fully resolved scoring bundle: type-erased scorers for steps, schedules,
    leaves, and inductives, plus comparison/display utilities.
    Registered bundles are selected at runtime via `specimen.scoreType` option. -/
structure ScorerBundle where
  scoreTypeName : Name
  stepScorer : ResolvedStepScorer
  scheduleScorer : ResolvedScheduleScorer
  leafAggregator : ResolvedLeafAggregator
  inductiveAggregator : ResolvedInductiveAggregator
  isBetter : Score → Score → Bool
  combineScores : Score → Score → Score
  reprScore : Score → String
  /-- Score of an empty schedule (no steps). Identity for `combineScores`. -/
  emptyScore : Score
  /-- Penalty added to leaf score when no constructor covers it. -/
  penaltyScore : Score
  /-- Absolute worst score — guaranteed worse than any real schedule.
      Used as the initial bound in branch-and-bound search. -/
  worstScore : Score
  /-- Map score to [0,1] for HSL color display (0 = best, 1 = worst). -/
  scoreBadness : Score → Float
  pruneStrategy : PruneStrategy := .usePrimary

/-- Build a complete ScorerBundle from typed scorers. -/
def mkScorerBundle [Inhabited S] [TypeName S] [Repr S] [Scorable S]
    (name : Name)
    (step : StepScorer S)
    (schedule : ScheduleScorer S)
    (leaf : LeafAggregator S)
    (inductive_ : InductiveAggregator S) : ScorerBundle :=
  { scoreTypeName := name
    stepScorer := wrapStepScorer step
    scheduleScorer := wrapScheduleScorer schedule
    leafAggregator := wrapLeafAggregator leaf
    inductiveAggregator := wrapInductiveAggregator inductive_
    isBetter := fun a b => Scorable.isBetter (Score.unwrap S a) (Score.unwrap S b)
    combineScores := fun a b => Score.wrap (Scorable.combine (Score.unwrap S a) (Score.unwrap S b))
    reprScore := fun s => reprStr (Score.unwrap S s)
    emptyScore := Score.wrap (Scorable.empty : S)
    penaltyScore := Score.wrap (Scorable.uncoveredPenalty : S)
    worstScore := Score.wrap (Scorable.worst : S)
    scoreBadness := fun s => Scorable.badness (Score.unwrap S s)
    pruneStrategy := .usePrimary }

instance : Inhabited ScorerBundle where
  default := {
    scoreTypeName := `Scoring.DefaultScore
    stepScorer := fun _ _ _ => default
    scheduleScorer := fun _ => default
    leafAggregator := fun _ => default
    inductiveAggregator := fun _ => default
    isBetter := fun _ _ => false
    combineScores := fun a _ => a
    reprScore := fun _ => "<default>"
    emptyScore := default
    penaltyScore := default
    worstScore := default
    scoreBadness := fun _ => 0.0
    pruneStrategy := .noPruning
  }

/-- Whether this bundle uses the monadic searchBestScheduleM path (all except legacy). -/
def ScorerBundle.usesMonadicPath (b : ScorerBundle) : Bool :=
  match b.pruneStrategy with
  | .legacy => false
  | _ => true

initialize scorerBundles : IO.Ref (Array ScorerBundle) ← IO.mkRef #[]

/-- Register a complete scoring bundle for a score type. -/
def registerScoringBundle (bundle : ScorerBundle) : IO Unit :=
  scorerBundles.modify (·.push bundle)

----------------------------------------------
-- Options
----------------------------------------------

register_option specimen.scoreType : String := {
  defValue := "Scoring.DefaultScore"
  descr := "The score type to use for coverage analysis."
}

----------------------------------------------
-- Resolution
----------------------------------------------

/-- Get the active score type from options. -/
def getActiveScoreType [Monad m] [MonadOptions m] : m Name := do
  let s : String := Lean.Option.get (← getOptions) specimen.scoreType
  return s.toName

/-- Resolve the active scoring bundle. -/
def getActiveScorerBundle : MetaM ScorerBundle := do
  let scoreType ← getActiveScoreType
  let bundles ← scorerBundles.get
  match bundles.find? (·.scoreTypeName == scoreType) with
  | some bundle => return bundle
  | none =>
    -- Fall back to first registered bundle
    match bundles[0]? with
    | some bundle => return bundle
    | none => return default

----------------------------------------------
-- Built-in: default strategy (sum of best)
----------------------------------------------

def defaultStepScorer : StepScorer DefaultScore := fun _key memo _inputVars step =>
  let baseScore : DefaultScore := match step with
    | .Check .. => { checks := 1, length := 1 }
    | .Unconstrained .. => { length := 1, unconstrained := 1 }
    | .SuchThat .. => { length := 1 }
    | .Match .. => { length := 1 }
  let depCost : DefaultScore :=
    let deps := collectNonRecDeps [step]
    deps.foldl (fun acc dep =>
      if dep.kind == .relation || dep.kind == .checker then
        let depKey : SpecKey := { inductiveName := dep.inductiveName, outputIndices := dep.outputIndices, deriveSort := dep.deriveSort }
        match memo[depKey]? with
        | some (.done depSched) =>
          let ds := Score.unwrap DefaultScore depSched.score
          { checks := acc.checks + ds.checks
            length := acc.length
            unconstrained := acc.unconstrained + ds.unconstrained }
        | _ => acc
      else acc) {}
  Scorable.combine baseScore depCost

def defaultScheduleScorer : ScheduleScorer DefaultScore := fun stepScores =>
  stepScores.foldl Scorable.combine Scorable.empty

def defaultLeafAggregator : LeafAggregator DefaultScore := fun ctors =>
  match ctors with
  | [] => Scorable.uncoveredPenalty
  | _ => Scorable.bestOf (ctors.map Prod.snd)

def defaultInductiveAggregator : InductiveAggregator DefaultScore := fun leafScores =>
  leafScores.foldl Scorable.combine Scorable.empty

initialize registerScoringBundle (mkScorerBundle `Scoring.DefaultScore
  defaultStepScorer defaultScheduleScorer defaultLeafAggregator defaultInductiveAggregator)

----------------------------------------------
-- Built-in: worst-leaf strategy
----------------------------------------------

structure WorstLeafScore where
  checks : Nat := 0
  length : Nat := 0
  unconstrained : Nat := 0
  deriving Repr, BEq, Inhabited

deriving instance TypeName for WorstLeafScore

instance : Ord WorstLeafScore where
  compare a b :=
    match compare a.checks b.checks with
    | .eq => match compare a.length b.length with
      | .eq => compare a.unconstrained b.unconstrained
      | r => r
    | r => r

instance : LT WorstLeafScore := ltOfOrd

instance : Scorable WorstLeafScore where
  empty := {}
  combine a b := { checks := max a.checks b.checks, length := max a.length b.length, unconstrained := max a.unconstrained b.unconstrained }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { checks := 1 }
  worst := { checks := 1000, length := 1000, unconstrained := 1000 }
  badness s :=
    if s.length == 0 then 0.0
    else
      let checkRatio := Float.ofNat s.checks / Float.ofNat s.length
      let uncRatio := Float.ofNat s.unconstrained / Float.ofNat s.length
      min 1.0 (checkRatio * 2.0 + uncRatio * 0.5)

def worstLeafStepScorer : StepScorer WorstLeafScore := fun _key _memo _inputVars step =>
  match step with
  | .Check .. => { checks := 1, length := 1 }
  | .Unconstrained .. => { length := 1, unconstrained := 1 }
  | _ => { length := 1 }

def worstLeafScheduleScorer : ScheduleScorer WorstLeafScore := fun stepScores =>
  stepScores.foldl (fun a b => { checks := a.checks + b.checks, length := a.length + b.length, unconstrained := a.unconstrained + b.unconstrained }) {}

def worstLeafLeafAggregator : LeafAggregator WorstLeafScore := fun ctors =>
  match ctors with
  | [] => Scorable.uncoveredPenalty
  | _ => Scorable.bestOf (ctors.map Prod.snd)

def worstLeafInductiveAggregator : InductiveAggregator WorstLeafScore := fun leafScores =>
  leafScores.foldl Scorable.combine Scorable.empty

initialize registerScoringBundle (mkScorerBundle `Scoring.WorstLeafScore
  worstLeafStepScorer worstLeafScheduleScorer worstLeafLeafAggregator worstLeafInductiveAggregator)

----------------------------------------------
-- Built-in: density analysis (from "Testing Theorems, Fully Automatically")
----------------------------------------------

inductive Density
  | Total
  | Partial
  | Backtracking
  | Checking
  deriving Repr, BEq, Inhabited

namespace Density

def toNat : Density → Nat
  | .Total => 0
  | .Partial => 1
  | .Backtracking => 2
  | .Checking => 3

instance : Ord Density where
  compare a b := compare a.toNat b.toNat

instance : LT Density := ltOfOrd
instance : LE Density := leOfOrd

def max (a b : Density) : Density := if a.toNat ≥ b.toNat then a else b
def min (a b : Density) : Density := if a.toNat ≤ b.toNat then a else b

end Density

/-- Density score. `forChecker` flips the ordering:
    - For generators: lower density is better (Total < Partial < Backtracking < Checking)
    - For checkers/enumerators: higher density is better (Checking < Backtracking < Partial < Total) -/
structure DensityScore where
  density : Density := .Total
  varDeps : Nat := 0
  forChecker : Bool := false
  deriving Repr, BEq, Inhabited

deriving instance TypeName for DensityScore

instance : Ord DensityScore where
  compare a b :=
    let da := if a.forChecker then 3 - a.density.toNat else a.density.toNat
    let db := if b.forChecker then 3 - b.density.toNat else b.density.toNat
    match compare da db with
    | .eq => compare a.varDeps b.varDeps
    | r => r

instance : LT DensityScore := ltOfOrd

instance : Scorable DensityScore where
  empty := {}
  combine a b := { density := Density.max a.density b.density, varDeps := a.varDeps + b.varDeps, forChecker := a.forChecker || b.forChecker }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { density := .Partial, varDeps := 0 }
  worst := { density := .Checking, varDeps := 1000 }
  badness s :=
    let rawLevel := s.density.toNat.toFloat / 3.0
    let level := if s.forChecker then 1.0 - rawLevel else rawLevel
    let depPenalty := min 0.2 (s.varDeps.toFloat * 0.05)
    min 1.0 (level + depPenalty)

private def sourceArgs : Source → List ConstructorExpr
  | .NonRec (_, args) => args
  | .Rec _ args => args
  | .MutRec _ args => args

private def countGeneratedVarDeps (inputVars : Std.HashSet Name) (src : Source) : Nat :=
  let args := sourceArgs src
  let allVars := args.flatMap varsInConstructorExpr
  allVars.filter (!inputVars.contains ·) |>.length

/-- Density step scorer (Section 4 of the paper):
    - Unconstrained → Total, 0 deps
    - Check → Checking, #generated-var deps
    - Match → Backtracking, 0 deps
    - SuchThat → dep's density from memo, #generated-var deps
    varDeps counts source args that were generated (not original inputs). -/
def densityStepScorer : StepScorer DensityScore := fun key memo inputVars step =>
  let isChecker := key.deriveSort == .Checker || key.deriveSort == .Enumerator
  match step with
  | .Unconstrained .. => { density := .Total, varDeps := 0, forChecker := isChecker }
  | .Check src _ => { density := .Checking, varDeps := countGeneratedVarDeps inputVars src, forChecker := isChecker }
  | .Match .. => { density := .Backtracking, varDeps := 0, forChecker := isChecker }
  | .SuchThat outputs src _ =>
    let outputNames := Std.HashSet.ofList (outputs.map (·.1))
    let varDeps := countGeneratedVarDeps (inputVars.union outputNames) src
    let depDensity : Density := match src with
      | .Rec .. => .Partial
      | .MutRec .. => .Partial
      | .NonRec (indName, args) =>
        let outputIdxs := outputs.filterMap fun (n, _) =>
          args.findIdx? fun a => match a with | .Unknown v => v == n | _ => false
        let depKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs, deriveSort := key.deriveSort }
        if depKey == key then .Partial
        else match memo[depKey]? with
          | some (.done depSched) => (Score.unwrap DensityScore depSched.score).density
          | _ => .Partial
    { density := depDensity, varDeps := varDeps, forChecker := isChecker }

def densityScheduleScorer : ScheduleScorer DensityScore := fun stepScores =>
  stepScores.foldl Scorable.combine Scorable.empty

def densityLeafAggregator : LeafAggregator DensityScore := fun ctors =>
  match ctors with
  | [] => Scorable.uncoveredPenalty
  | _ => Scorable.bestOf (ctors.map Prod.snd)

def densityInductiveAggregator : InductiveAggregator DensityScore := fun leafScores =>
  leafScores.foldl Scorable.combine Scorable.empty

initialize registerScoringBundle (mkScorerBundle `Scoring.DensityScore
  densityStepScorer densityScheduleScorer densityLeafAggregator densityInductiveAggregator)

----------------------------------------------
-- Built-in: uniform density (no checker inversion)
----------------------------------------------

/-- Like DensityScore but without inverting the ordering for checkers/enumerators.
    Lower density is always better regardless of deriveSort. This avoids the
    extra enumerator/checker derivations that the inverted ordering triggers. -/
structure UniformDensityScore where
  density : Density := .Total
  varDeps : Nat := 0
  deriving Repr, BEq, Inhabited

deriving instance TypeName for UniformDensityScore

instance : Ord UniformDensityScore where
  compare a b :=
    match compare a.density.toNat b.density.toNat with
    | .eq => compare a.varDeps b.varDeps
    | r => r

instance : LT UniformDensityScore := ltOfOrd

instance : Scorable UniformDensityScore where
  empty := {}
  combine a b := { density := Density.max a.density b.density, varDeps := a.varDeps + b.varDeps }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { density := .Partial, varDeps := 0 }
  worst := { density := .Checking, varDeps := 1000 }
  badness s :=
    let level := s.density.toNat.toFloat / 3.0
    let depPenalty := min 0.2 (s.varDeps.toFloat * 0.05)
    min 1.0 (level + depPenalty)

def uniformDensityStepScorer : StepScorer UniformDensityScore := fun _key memo inputVars step =>
  match step with
  | .Unconstrained .. => { density := .Total, varDeps := 0 }
  | .Check src _ => { density := .Checking, varDeps := countGeneratedVarDeps inputVars src }
  | .Match .. => { density := .Backtracking, varDeps := 0 }
  | .SuchThat outputs src _ =>
    let outputNames := Std.HashSet.ofList (outputs.map (·.1))
    let varDeps := countGeneratedVarDeps (inputVars.union outputNames) src
    let depDensity : Density := match src with
      | .Rec .. => .Partial
      | .MutRec .. => .Partial
      | .NonRec (indName, args) =>
        let outputIdxs := outputs.filterMap fun (n, _) =>
          args.findIdx? fun a => match a with | .Unknown v => v == n | _ => false
        let depKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs, deriveSort := _key.deriveSort }
        if depKey == _key then .Partial
        else match memo[depKey]? with
          | some (.done depSched) => (Score.unwrap UniformDensityScore depSched.score).density
          | _ => .Partial
    { density := depDensity, varDeps := varDeps }

def uniformDensityScheduleScorer : ScheduleScorer UniformDensityScore := fun stepScores =>
  stepScores.foldl Scorable.combine Scorable.empty

def uniformDensityLeafAggregator : LeafAggregator UniformDensityScore := fun ctors =>
  match ctors with
  | [] => Scorable.uncoveredPenalty
  | _ => Scorable.bestOf (ctors.map Prod.snd)

def uniformDensityInductiveAggregator : InductiveAggregator UniformDensityScore := fun leafScores =>
  leafScores.foldl Scorable.combine Scorable.empty

initialize registerScoringBundle (mkScorerBundle `Scoring.UniformDensityScore
  uniformDensityStepScorer uniformDensityScheduleScorer uniformDensityLeafAggregator uniformDensityInductiveAggregator)

end Scoring
