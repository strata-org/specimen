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
-- Weight function type and registry
----------------------------------------------

/-- A weight function computes the runtime frequency weight for a constructor.
    Arguments: (scoreBadness, isRec, size, numBase, numRec).
    - scoreBadness: per-constructor quality from the active scorer (0.0 = best, 1.0 = worst)
    - isRec: whether this constructor is recursive
    - size: current generation size parameter
    - numBase/numRec: counts of base vs recursive constructors for this inductive -/
abbrev CtorWeightFn := Float → Bool → Nat → Nat → Nat → Nat

/-- Ignores score; base=1, recursive=numBase*size/numRec. -/
def defaultCtorWeight (_scoreBadness : Float) (isRec : Bool) (size : Nat) (numBase numRec : Nat) : Nat :=
  if isRec then
    if size == 0 then 1
    else max 1 (numBase * size / max 1 numRec)
  else 1

/-- QuickChick-style weight: base=1, recursive=size+1. Ignores score. -/
def quickchickCtorWeight (_scoreBadness : Float) (isRec : Bool) (size : Nat) (_numBase _numRec : Nat) : Nat :=
  if isRec then size + 1 else 1

/-- Flat weight: every constructor gets weight 1. Ignores everything. -/
def flatCtorWeight (_scoreBadness : Float) (_isRec : Bool) (_size : Nat) (_numBase _numRec : Nat) : Nat := 1

/-- Score-aware weight: boosts good constructors (low badness) and deprioritizes
    recursive ones. Quality maps to 1–4, recursive ctors get an additional size-based
    penalty so base cases are preferred at small sizes. -/
def scoreAwareCtorWeight (scoreBadness : Float) (isRec : Bool) (size : Nat) (numBase numRec : Nat) : Nat :=
  let quality := if scoreBadness < 0.25 then 4
    else if scoreBadness < 0.5 then 3
    else if scoreBadness < 0.75 then 2
    else 1
  if isRec then
    if size == 0 then 1
    else max 1 (numBase * size / max 1 numRec) * quality
  else quality

/-- Balanced weight for inductives with many recursive constructors.
    Controls aggregate P(recursive) ≈ size / (size + 4*numBase) by distributing
    size across all recursive ctors (so total rec weight ≈ size * quality).
    Base ctors get a 4x boost so they stay relevant even with many rec branches. -/
def balancedCtorWeight (scoreBadness : Float) (isRec : Bool) (size : Nat) (_numBase numRec : Nat) : Nat :=
  let quality := if scoreBadness < 0.25 then 4
    else if scoreBadness < 0.5 then 3
    else if scoreBadness < 0.75 then 2
    else 1
  if isRec then
    if size == 0 then 0
    else max 1 (size / max 1 numRec) * quality
  else quality * 4

/-- Quality-only weight: no structural bias, budget splitting handles termination. -/
def qualityCtorWeight (scoreBadness : Float) (_isRec : Bool) (_size : Nat) (_numBase _numRec : Nat) : Nat :=
  if scoreBadness < 0.25 then 4
  else if scoreBadness < 0.5 then 3
  else if scoreBadness < 0.75 then 2
  else 1

structure WeightFnEntry where
  name : Name
  fn : CtorWeightFn
  leanName : Name

initialize weightFnRegistry : IO.Ref (Array WeightFnEntry) ← IO.mkRef #[]

def registerWeightFn (name : Name) (fn : CtorWeightFn) (leanName : Name) : IO Unit :=
  weightFnRegistry.modify (·.push { name, fn, leanName })

initialize registerWeightFn `Scoring.defaultCtorWeight defaultCtorWeight ``defaultCtorWeight
initialize registerWeightFn `Scoring.quickchickCtorWeight quickchickCtorWeight ``quickchickCtorWeight
initialize registerWeightFn `Scoring.flatCtorWeight flatCtorWeight ``flatCtorWeight
initialize registerWeightFn `Scoring.scoreAwareCtorWeight scoreAwareCtorWeight ``scoreAwareCtorWeight
initialize registerWeightFn `Scoring.balancedCtorWeight balancedCtorWeight ``balancedCtorWeight
initialize registerWeightFn `Scoring.qualityCtorWeight qualityCtorWeight ``qualityCtorWeight

register_option specimen.weightFn : String := {
  defValue := "Scoring.balancedCtorWeight"
  descr := "The weight function used for constructor frequency in derived generators."
}

/-- Get the active weight function name from options. -/
def getActiveWeightFnName [Monad m] [MonadOptions m] : m Name := do
  let s : String := Lean.Option.get (← getOptions) specimen.weightFn
  return s.toName

/-- Resolve the active weight function entry. -/
def getActiveWeightFn : CoreM WeightFnEntry := do
  let name ← getActiveWeightFnName
  let entries ← weightFnRegistry.get
  match entries.find? (·.name == name) with
  | some entry => return entry
  | none => match entries[0]? with
    | some entry => return entry
    | none => return { name := `Scoring.balancedCtorWeight, fn := balancedCtorWeight, leanName := ``balancedCtorWeight }

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

----------------------------------------------
-- Scorer function types (parameterized by score type)
----------------------------------------------

/-- Scores a single schedule step. Receives:
    - The current spec being derived (inductiveName + outputIndices + deriveSort)
    - The dependency memo (for looking up sub-relation scores)
    - The set of input variables (fixed at schedule start, NOT generated)
    - The step itself -/
abbrev StepScorer (S : Type) := SpecKey → Std.HashMap SpecKey MemoEntry → Std.HashSet Name → ScheduleStep → MetaM S

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
abbrev ResolvedStepScorer := SpecKey → Std.HashMap SpecKey MemoEntry → Std.HashSet Name → ScheduleStep → MetaM Score

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
  fun key memo inputVars step => return Score.wrap (← f key memo inputVars step)

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
    stepScorer := fun _ _ _ _ => return default
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

def defaultStepScorer : StepScorer DefaultScore := fun _key memo _inputVars step => do
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
  return Scorable.combine baseScore depCost

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

def worstLeafStepScorer : StepScorer WorstLeafScore := fun _key _memo _inputVars step => do
  return match step with
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
def densityStepScorer : StepScorer DensityScore := fun key memo inputVars step => do
  let isChecker := key.deriveSort == .Checker || key.deriveSort == .Enumerator
  return match step with
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

def uniformDensityStepScorer : StepScorer UniformDensityScore := fun _key memo inputVars step => do
  return match step with
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

----------------------------------------------
-- Built-in: graded uniform density (two-axis check severity)
----------------------------------------------

inductive CheckSpeed
  | NotACheck
  | Decidable
  | Moderate
  | Expensive
  | Recursive
  deriving Repr, BEq, Inhabited

namespace CheckSpeed

def toNat : CheckSpeed → Nat
  | .NotACheck => 0
  | .Decidable => 1
  | .Moderate => 2
  | .Expensive => 3
  | .Recursive => 4

instance : Ord CheckSpeed where
  compare a b := compare a.toNat b.toNat

def max (a b : CheckSpeed) : CheckSpeed := if a.toNat ≥ b.toNat then a else b

end CheckSpeed

inductive PassLikelihood
  | Certain
  | Likely
  | Moderate
  | Unlikely
  | Desperate
  deriving Repr, BEq, Inhabited

namespace PassLikelihood

def toNat : PassLikelihood → Nat
  | .Certain => 0
  | .Likely => 1
  | .Moderate => 2
  | .Unlikely => 3
  | .Desperate => 4

instance : Ord PassLikelihood where
  compare a b := compare a.toNat b.toNat

def max (a b : PassLikelihood) : PassLikelihood := if a.toNat ≥ b.toNat then a else b

end PassLikelihood

structure GradedUniformDensityScore where
  density        : Density := .Total
  checkSpeed     : CheckSpeed := .NotACheck
  passLikelihood : PassLikelihood := .Certain
  varDeps        : Nat := 0
  deriving Repr, BEq, Inhabited

deriving instance TypeName for GradedUniformDensityScore

instance : Ord GradedUniformDensityScore where
  compare a b :=
    match compare a.density.toNat b.density.toNat with
    | .eq => match compare a.checkSpeed.toNat b.checkSpeed.toNat with
      | .eq => match compare a.passLikelihood.toNat b.passLikelihood.toNat with
        | .eq => compare a.varDeps b.varDeps
        | r => r
      | r => r
    | r => r

instance : LT GradedUniformDensityScore := ltOfOrd

instance : Scorable GradedUniformDensityScore where
  empty := {}
  combine a b :=
    { density := Density.max a.density b.density
      checkSpeed := CheckSpeed.max a.checkSpeed b.checkSpeed
      passLikelihood := PassLikelihood.max a.passLikelihood b.passLikelihood
      varDeps := a.varDeps + b.varDeps }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { density := .Partial, varDeps := 0 }
  worst := { density := .Checking, checkSpeed := .Recursive, passLikelihood := .Desperate, varDeps := 1000 }
  badness s :=
    let varDepPenalty := min 0.05 (s.varDeps.toFloat * 0.01)
    if s.density != .Checking then
      let level := s.density.toNat.toFloat / 4.0
      min 1.0 (level + varDepPenalty)
    else
      let speedVal := match s.checkSpeed with
        | .NotACheck => 0.0 | .Decidable => 0.0 | .Moderate => 0.33
        | .Expensive => 0.66 | .Recursive => 1.0
      let likelVal := match s.passLikelihood with
        | .Certain => 0.0 | .Likely => 0.0 | .Moderate => 0.33
        | .Unlikely => 0.66 | .Desperate => 1.0
      let severity := max speedVal likelVal * 0.7 + min speedVal likelVal * 0.3
      min 1.0 (0.75 + severity * 0.25 + varDepPenalty)

private def estimateTypeCtorCount (indName : Name) : MetaM (Option Nat) := do
  let env ← getEnv
  match env.find? indName with
  | some (.inductInfo val) =>
    let isRecursive ← val.ctors.anyM fun c => do
      let cinfo ← getConstInfo c
      return cinfo.type.find? (fun e => e == .const indName []) |>.isSome
    if isRecursive then return none
    else return some val.ctors.length
  | _ => return none

private def extractEqTypeName : List ConstructorExpr → Option Name
  | [.Ctor n _, _, _] | [.TyCtor n _, _, _] => some n
  | _ => none

private def classifyCheckSpeed (memo : Std.HashMap SpecKey MemoEntry) (key : SpecKey)
    (src : Source) (varDeps : Nat) : CheckSpeed :=
  match src with
  | .Rec .. | .MutRec .. => .Recursive
  | .NonRec (indName, _args) =>
    let depKey : SpecKey := { inductiveName := indName, outputIndices := [], deriveSort := .Checker }
    let depDensity := if depKey == key then Density.Checking
      else match memo[depKey]? with
        | some (.done depSched) => (Score.unwrap GradedUniformDensityScore depSched.score).density
        | _ => .Partial
    let isChecker := key.deriveSort == .Checker || key.deriveSort == .Enumerator
    if isChecker then
      match varDeps with
      | 0 => match depDensity with
        | .Total | .Partial => .Decidable
        | .Backtracking => .Moderate
        | .Checking => .Expensive
      | 1 => match depDensity with
        | .Total | .Partial => .Moderate
        | _ => .Expensive
      | 2 | 3 => .Expensive
      | _ => .Recursive
    else
      match depDensity with
      | .Total | .Partial => .Decidable
      | .Backtracking => .Moderate
      | .Checking => .Expensive

private def classifyPassLikelihood (inputVars : Std.HashSet Name) (key : SpecKey)
    (src : Source) (polarity : Bool) (varDeps : Nat) : MetaM PassLikelihood := do
  if varDeps == 0 then return .Certain
  let isChecker := key.deriveSort == .Checker || key.deriveSort == .Enumerator
  match src with
  | .Rec .. | .MutRec .. =>
    if isChecker then return .Moderate
    else return .Desperate
  | .NonRec (indName, args) =>
    let arity := args.length
    if indName == ``Eq then
      let eqArgs := args.flatMap varsInConstructorExpr
      let genVars := eqArgs.filter (!inputVars.contains ·)
      if genVars.isEmpty then return .Certain
      let ctorCount ← match extractEqTypeName args with
        | some typeName => estimateTypeCtorCount typeName
        | none => pure none
      if polarity then
        match ctorCount with
        | some n => if n ≤ 2 then return .Unlikely else return .Desperate
        | none => return .Desperate
      else
        match ctorCount with
        | some n => if n ≤ 2 then return .Moderate else return .Likely
        | none => return .Likely
    if isChecker then
      return .Certain
    else
      if !polarity && varDeps ≤ 1 then return .Likely
      if varDeps == 1 && arity ≤ 3 then return .Likely
      if varDeps ≤ 3 then return .Moderate
      return .Unlikely

def gradedStepScorer : StepScorer GradedUniformDensityScore := fun key memo inputVars step => do
  match step with
  | .Unconstrained .. => return { density := .Total }
  | .Match .. => return { density := .Backtracking }
  | .Check src polarity =>
    let varDeps := countGeneratedVarDeps inputVars src
    let speed := classifyCheckSpeed memo key src varDeps
    let likelihood ← classifyPassLikelihood inputVars key src polarity varDeps
    return { density := .Checking, checkSpeed := speed, passLikelihood := likelihood, varDeps := varDeps }
  | .SuchThat outputs src prodSort =>
    let outputNames := Std.HashSet.ofList (outputs.map (·.1))
    let varDeps := countGeneratedVarDeps (inputVars.union outputNames) src
    let depDensity : Density := match src with
      | .Rec .. => .Partial
      | .MutRec .. => .Partial
      | .NonRec (indName, args) =>
        let outputIdxs := outputs.filterMap fun (n, _) =>
          args.findIdx? fun a => match a with | .Unknown v => v == n | _ => false
        let depDeriveSort := match prodSort with
          | .Enumerator => DeriveSort.Enumerator
          | .Generator => DeriveSort.Generator
        let depKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs, deriveSort := depDeriveSort }
        if depKey == key then .Partial
        else match memo[depKey]? with
          | some (.done depSched) => (Score.unwrap GradedUniformDensityScore depSched.score).density
          | _ => .Partial
    return { density := depDensity, varDeps := varDeps }

def gradedScheduleScorer : ScheduleScorer GradedUniformDensityScore := fun stepScores =>
  stepScores.foldl Scorable.combine Scorable.empty

def gradedLeafAggregator : LeafAggregator GradedUniformDensityScore := fun ctors =>
  match ctors with
  | [] => Scorable.uncoveredPenalty
  | _ => Scorable.bestOf (ctors.map Prod.snd)

def gradedInductiveAggregator : InductiveAggregator GradedUniformDensityScore := fun leafScores =>
  leafScores.foldl Scorable.combine Scorable.empty

initialize registerScoringBundle (mkScorerBundle `Scoring.GradedUniformDensityScore
  gradedStepScorer gradedScheduleScorer gradedLeafAggregator gradedInductiveAggregator)

----------------------------------------------
-- BoundedGradedScore: refines GradedUniformDensityScore
-- with a Boundedness field that distinguishes finite from
-- potentially-infinite enumeration in SuchThat steps.
----------------------------------------------

inductive Boundedness
  | Finite      -- dep has only base cases (deterministic / bounded enumeration)
  | Bounded     -- dep has rec cases but is structurally decreasing on known input
  | Unbounded   -- dep has rec cases on unknown/generated input (potentially infinite)
  deriving Repr, BEq, Inhabited

namespace Boundedness
def toNat : Boundedness → Nat
  | .Finite => 0
  | .Bounded => 1
  | .Unbounded => 2

def max (a b : Boundedness) : Boundedness :=
  if a.toNat ≥ b.toNat then a else b
end Boundedness

structure BoundedGradedScore where
  density        : Density := .Total
  boundedness    : Boundedness := .Finite
  checkSpeed     : CheckSpeed := .NotACheck
  passLikelihood : PassLikelihood := .Certain
  varDeps        : Nat := 0
  deriving Repr, BEq, Inhabited

deriving instance TypeName for BoundedGradedScore

instance : Ord BoundedGradedScore where
  compare a b :=
    match compare a.density.toNat b.density.toNat with
    | .eq => match compare a.boundedness.toNat b.boundedness.toNat with
      | .eq => match compare a.checkSpeed.toNat b.checkSpeed.toNat with
        | .eq => match compare a.passLikelihood.toNat b.passLikelihood.toNat with
          | .eq => compare a.varDeps b.varDeps
          | r => r
        | r => r
      | r => r
    | r => r

instance : LT BoundedGradedScore := ltOfOrd

instance : Scorable BoundedGradedScore where
  empty := {}
  combine a b :=
    { density := Density.max a.density b.density
      boundedness := Boundedness.max a.boundedness b.boundedness
      checkSpeed := CheckSpeed.max a.checkSpeed b.checkSpeed
      passLikelihood := PassLikelihood.max a.passLikelihood b.passLikelihood
      varDeps := a.varDeps + b.varDeps }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { density := .Checking, boundedness := .Unbounded,
                        checkSpeed := .Recursive, passLikelihood := .Desperate, varDeps := 1000 }
  worst := { density := .Checking, boundedness := .Unbounded,
             checkSpeed := .Recursive, passLikelihood := .Desperate, varDeps := 1000 }
  badness s :=
    let d := s.density.toNat.toFloat / 3.0
    let b := s.boundedness.toNat.toFloat / 2.0
    let c := s.checkSpeed.toNat.toFloat / 4.0
    let p := s.passLikelihood.toNat.toFloat / 3.0
    (d * 0.4 + b * 0.2 + c * 0.2 + p * 0.2)

/-- Extract the `Source.Rec` input args from a schedule's steps (the arguments
    passed to the recursive call). Returns `none` if no rec call is found. -/
private def findRecCallInputArgs (steps : List ScheduleStep) : Option (List ConstructorExpr) :=
  steps.findSome? fun step => match step with
    | .SuchThat _ (.Rec _ args) _ => some args
    | .Check (.Rec _ args) _ => some args
    | .Unconstrained _ (.Rec _ args) _ => some args
    | _ => none

/-- Classify whether a dep's recursion is structurally decreasing on an input.
    Inspects the dep's `recSchedules`: if the recursive call passes a different
    variable at an input position (introduced by a Match step = subterm), it's bounded.
    If all inputs are unchanged, it's unbounded. -/
private def classifyBoundednessFromSchedule (depSched : InductiveSchedule) : Boundedness :=
  if depSched.recSchedules.isEmpty then .Finite
  else
    let outputIdxSet := Std.HashSet.ofList depSched.key.outputIndices
    let inputNames := (List.range depSched.argNames.length).zip depSched.argNames |>.filterMap fun (i, name) =>
      if outputIdxSet.contains i then none else some name
    if inputNames.isEmpty then .Unbounded
    else
      let allRecDecrease := depSched.recSchedules.all fun (_, (steps, _)) =>
        match findRecCallInputArgs steps with
        | none => false
        | some recArgs =>
          inputNames.zip recArgs |>.any fun (origName, recArg) =>
            match recArg with
            | .Unknown name => name != origName
            | _ => true
      if allRecDecrease then .Bounded else .Unbounded

def boundedStepScorer : StepScorer BoundedGradedScore := fun key memo inputVars step => do
  match step with
  | .Unconstrained .. => return { density := .Total }
  | .Match .. => return { density := .Backtracking }
  | .Check src polarity =>
    let varDeps := countGeneratedVarDeps inputVars src
    let speed := classifyCheckSpeed memo key src varDeps
    let likelihood ← classifyPassLikelihood inputVars key src polarity varDeps
    return { density := .Checking, checkSpeed := speed, passLikelihood := likelihood, varDeps := varDeps }
  | .SuchThat outputs src prodSort =>
    let outputNames := Std.HashSet.ofList (outputs.map (·.1))
    let varDeps := countGeneratedVarDeps (inputVars.union outputNames) src
    let depDensity : Density := match src with
      | .Rec .. => .Partial
      | .MutRec .. => .Partial
      | .NonRec (indName, args) =>
        let outputIdxs := outputs.filterMap fun (n, _) =>
          args.findIdx? fun a => match a with | .Unknown v => v == n | _ => false
        let depDeriveSort := match prodSort with
          | .Enumerator => DeriveSort.Enumerator
          | .Generator => DeriveSort.Generator
        let depKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs, deriveSort := depDeriveSort }
        if depKey == key then .Partial
        else match memo[depKey]? with
          | some (.done depSched) => (Score.unwrap BoundedGradedScore depSched.score).density
          | _ => .Partial
    let boundedness := match src with
      | .Rec .. | .MutRec .. => Boundedness.Unbounded
      | .NonRec (indName, args) =>
        let outputIdxs := outputs.filterMap fun (n, _) =>
          args.findIdx? fun a => match a with | .Unknown v => v == n | _ => false
        let depDeriveSort := match prodSort with
          | .Enumerator => DeriveSort.Enumerator
          | .Generator => DeriveSort.Generator
        let depKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs, deriveSort := depDeriveSort }
        if depKey == key then .Unbounded
        else match memo[depKey]? with
          | some (.done depSched) => classifyBoundednessFromSchedule depSched
          | _ => .Bounded
    return { density := depDensity, boundedness := boundedness, varDeps := varDeps }

def boundedScheduleScorer : ScheduleScorer BoundedGradedScore := fun stepScores =>
  stepScores.foldl Scorable.combine Scorable.empty

def boundedLeafAggregator : LeafAggregator BoundedGradedScore := fun ctors =>
  match ctors with
  | [] => Scorable.uncoveredPenalty
  | _ => Scorable.bestOf (ctors.map Prod.snd)

def boundedInductiveAggregator : InductiveAggregator BoundedGradedScore := fun leafScores =>
  leafScores.foldl Scorable.combine Scorable.empty

initialize registerScoringBundle (mkScorerBundle `Scoring.BoundedGradedScore
  boundedStepScorer boundedScheduleScorer boundedLeafAggregator boundedInductiveAggregator)


----------------------------------------------
-- Built-in: InputAwareGradedScore
-- Like GradedUniformDensityScore but with leaf/inductive aggregation
-- that penalizes checks whose generated variables overlap with inputs
-- (i.e. "generate then verify against input" patterns).
----------------------------------------------

structure InputAwareGradedScore where
  density        : Density := .Total
  checkSpeed     : CheckSpeed := .NotACheck
  passLikelihood : PassLikelihood := .Certain
  varDeps        : Nat := 0
  inputCheckDeps : Nat := 0
  deriving Repr, BEq, Inhabited

deriving instance TypeName for InputAwareGradedScore

instance : Ord InputAwareGradedScore where
  compare a b :=
    match compare a.density.toNat b.density.toNat with
    | .eq => match compare a.inputCheckDeps b.inputCheckDeps with
      | .eq => match compare a.checkSpeed.toNat b.checkSpeed.toNat with
        | .eq => match compare a.passLikelihood.toNat b.passLikelihood.toNat with
          | .eq => compare a.varDeps b.varDeps
          | r => r
        | r => r
      | r => r
    | r => r

instance : LT InputAwareGradedScore := ltOfOrd

instance : Scorable InputAwareGradedScore where
  empty := {}
  combine a b :=
    { density := Density.max a.density b.density
      checkSpeed := CheckSpeed.max a.checkSpeed b.checkSpeed
      passLikelihood := PassLikelihood.max a.passLikelihood b.passLikelihood
      varDeps := a.varDeps + b.varDeps
      inputCheckDeps := a.inputCheckDeps + b.inputCheckDeps }
  isBetter a b := a < b
  bestOf scores := scores.foldl (fun acc s => if s < acc then s else acc) (scores.headD {})
  uncoveredPenalty := { density := .Partial, varDeps := 0 }
  worst := { density := .Checking, checkSpeed := .Recursive, passLikelihood := .Desperate, varDeps := 1000, inputCheckDeps := 100 }
  badness s :=
    let varDepPenalty := min 0.05 (s.varDeps.toFloat * 0.01)
    let inputPenalty := min 0.3 (s.inputCheckDeps.toFloat * 0.1)
    if s.density != .Checking then
      let level := s.density.toNat.toFloat / 4.0
      min 1.0 (level + varDepPenalty + inputPenalty)
    else
      let speedVal := match s.checkSpeed with
        | .NotACheck => 0.0 | .Decidable => 0.0 | .Moderate => 0.33
        | .Expensive => 0.66 | .Recursive => 1.0
      let likelVal := match s.passLikelihood with
        | .Certain => 0.0 | .Likely => 0.0 | .Moderate => 0.33
        | .Unlikely => 0.66 | .Desperate => 1.0
      let severity := max speedVal likelVal * 0.7 + min speedVal likelVal * 0.3
      min 1.0 (0.75 + severity * 0.25 + varDepPenalty + inputPenalty)

private def countInputCheckDeps (inputVars : Std.HashSet Name) (src : Source) : Nat :=
  let allVars := match src with
    | .NonRec (_, args) => args.flatMap varsInConstructorExpr
    | .Rec _ args => args.flatMap varsInConstructorExpr
    | .MutRec _ args => args.flatMap varsInConstructorExpr
  let inputArgs := allVars.filter inputVars.contains
  inputArgs.length

def inputAwareStepScorer : StepScorer InputAwareGradedScore := fun key memo inputVars step => do
  match step with
  | .Unconstrained .. => return { density := .Total }
  | .Match .. => return { density := .Backtracking }
  | .Check src polarity =>
    let varDeps := countGeneratedVarDeps inputVars src
    let speed := classifyCheckSpeed memo key src varDeps
    let likelihood ← classifyPassLikelihood inputVars key src polarity varDeps
    let inputDeps := if varDeps > 0 then countInputCheckDeps inputVars src else 0
    return { density := .Checking, checkSpeed := speed, passLikelihood := likelihood, varDeps := varDeps, inputCheckDeps := inputDeps }
  | .SuchThat outputs src prodSort =>
    let outputNames := Std.HashSet.ofList (outputs.map (·.1))
    let varDeps := countGeneratedVarDeps (inputVars.union outputNames) src
    let depDensity : Density := match src with
      | .Rec .. => .Partial
      | .MutRec .. => .Partial
      | .NonRec (indName, args) =>
        let outputIdxs := outputs.filterMap fun (n, _) =>
          args.findIdx? fun a => match a with | .Unknown v => v == n | _ => false
        let depDeriveSort := match prodSort with
          | .Enumerator => DeriveSort.Enumerator
          | .Generator => DeriveSort.Generator
        let depKey : SpecKey := { inductiveName := indName, outputIndices := outputIdxs, deriveSort := depDeriveSort }
        if depKey == key then .Partial
        else match memo[depKey]? with
          | some (.done depSched) => (Score.unwrap InputAwareGradedScore depSched.score).density
          | _ => .Partial
    return { density := depDensity, varDeps := varDeps }

def inputAwareScheduleScorer : ScheduleScorer InputAwareGradedScore := fun stepScores =>
  stepScores.foldl Scorable.combine Scorable.empty

def inputAwareLeafAggregator : LeafAggregator InputAwareGradedScore := fun ctors =>
  match ctors with
  | [] => Scorable.uncoveredPenalty
  | _ => Scorable.bestOf (ctors.map Prod.snd)

def inputAwareInductiveAggregator : InductiveAggregator InputAwareGradedScore := fun leafScores =>
  leafScores.foldl Scorable.combine Scorable.empty

initialize registerScoringBundle (mkScorerBundle `Scoring.InputAwareGradedScore
  inputAwareStepScorer inputAwareScheduleScorer inputAwareLeafAggregator inputAwareInductiveAggregator)


end Scoring
