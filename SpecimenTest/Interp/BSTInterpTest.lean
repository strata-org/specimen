import Specimen.Interp
import SpecimenTest.CommonDefinitions.BinaryTree

/-!
# Scheduling and interpreting `BST` at runtime

End-to-end test of `Specimen.Interp` on the relations from `CommonDefinitions.BinaryTree`:

```lean
inductive Between : Nat → Nat → Nat → Prop where
  | BetweenN : ∀ n m, n ≤ m → Between n (.succ n) (.succ (.succ m))
  | BetweenS : ∀ n m o, Between n m o → Between n (.succ m) (.succ o)

inductive BST : Nat → Nat → BinaryTree → Prop where
  | BstLeaf : BST lo hi .Leaf
  | BstNode : ∀ lo hi x l r, Between lo x hi → BST lo x l → BST x hi r → BST lo hi (.Node x l r)
```

Four things are checked, in increasing order of what they would catch:

1. **`deriveMode` agrees with `derive_mutual`.** The `expected*` schedules below are transcriptions of
   what the compile-time pipeline chooses for `fun lo hi => ∃ t, BST lo hi t` (recovered with
   `set_option specimen.textOutput 3`). Deriving the same mode from the `RelSpec`s at runtime must
   reproduce them step for step. This is the load-bearing assertion: it pins the runtime scheduler to
   the real one.
2. **The values are real.** Generated trees are checked against a hand-written `BST` decision
   procedure, so a wrong interpretation shows up as an unsound value rather than a plausible-looking
   tree.
3. **Reordering premises reinterprets outputs.** Scheduling `BST lo x l` before `Between lo x hi`
   makes that premise produce *both* `x` and `l` — a call to `BST[1,2]`, a mode no compile-time
   derivation produced — and demotes `Between` to a check. `deriveClosure` brings the new mode up and
   the result is still sound.
4. **Discards are attributed, and drive mutation.** A deliberately bad plan that generates the pivot
   blind and then tests it discards a fifth of its attempts; the profiler blames the exact step, and
   `tunePlan` mutates its way back to the zero-discard schedule.
5. **The static estimate agrees with the measurement.** `estimateRisk` reaches the same verdict
   without sampling, following `Scoring.BudgetAwareScore`: a `SuchThat` carries its callee's risk, not
   none, and a cross-mode call is charged for spinning up a separate generator.

Sampling is seeded from `IO`, so the assertions are on invariants — soundness, zero discards, which
plan wins — rather than on exact counts.
-/

open Plausible Schedules Specimen Specimen.Interp

namespace SpecimenTest.InterpBST

/-! ## The relations, as data

    A `RelSpec` is a relation's premises and conclusions before a mode or an ordering has been
    chosen. Everything else in this file is derived from these two declarations. -/

/-- `Between` as data. `n ≤ m` reifies with its `Nat` type argument and its `instLENat` dictionary,
    exactly as `exprToConstructorExpr` produces them. -/
def betweenSpec : RelSpec where
  inductiveName := ``Between
  argNames := [`a_2, `b_2, `c_2]
  recFnName := `aux_between
  ctors :=
    [ { ctorName := ``Between.BetweenN
      , vars := [{ name := `n, ty := (``Nat, []) }, { name := `m, ty := (``Nat, []) }]
      , hypotheses := [(``LE.le, [.TyCtor ``Nat [], .FuncApp ``instLENat [],
          .Unknown `n, .Unknown `m])]
      , conclusionArgs := [.Unknown `n, .Ctor ``Nat.succ [.Unknown `n],
          .Ctor ``Nat.succ [.Ctor ``Nat.succ [.Unknown `m]]] }
    , { ctorName := ``Between.BetweenS
      , vars := [{ name := `n, ty := (``Nat, []) }, { name := `m, ty := (``Nat, []) },
                 { name := `o, ty := (``Nat, []) }]
      , hypotheses := [(``Between, [.Unknown `n, .Unknown `m, .Unknown `o])]
      , conclusionArgs := [.Unknown `n, .Ctor ``Nat.succ [.Unknown `m],
          .Ctor ``Nat.succ [.Unknown `o]] } ]

/-- `BST` as data. -/
def bstSpec : RelSpec where
  inductiveName := ``BST
  argNames := [`a_1, `b_1, `c_1]
  recFnName := `aux_bst
  ctors :=
    [ { ctorName := ``BST.BstLeaf
      , vars := [{ name := `lo, ty := (``Nat, []) }, { name := `hi, ty := (``Nat, []) }]
      , conclusionArgs := [.Unknown `lo, .Unknown `hi, .Ctor ``BinaryTree.Leaf []] }
    , { ctorName := ``BST.BstNode
      , vars := [{ name := `lo, ty := (``Nat, []) }, { name := `hi, ty := (``Nat, []) },
                 { name := `x, ty := (``Nat, []) },
                 { name := `l, ty := (``BinaryTree, []) }, { name := `r, ty := (``BinaryTree, []) }]
      , hypotheses :=
          [ (``Between, [.Unknown `lo, .Unknown `x, .Unknown `hi])
          , (``BST, [.Unknown `lo, .Unknown `x, .Unknown `l])
          , (``BST, [.Unknown `x, .Unknown `hi, .Unknown `r]) ]
      , conclusionArgs := [.Unknown `lo, .Unknown `hi,
          .Ctor ``BinaryTree.Node [.Unknown `x, .Unknown `l, .Unknown `r]] } ]

/-- Both relations, for `deriveClosure` to draw on. -/
def specs : List RelSpec := [betweenSpec, bstSpec]

/-- `Between` generating its middle argument: `fun a c => ∃ b, Between a b c`. -/
def betweenKey : SpecKey :=
  { inductiveName := ``Between, outputIndices := [1], deriveSort := .Generator }

/-- `BST` generating its tree: `fun a b => ∃ c, BST a b c`. -/
def bstKey : SpecKey :=
  { inductiveName := ``BST, outputIndices := [2], deriveSort := .Generator }

/-- `BST.BstNode` as a `CtorSpec`, for the plan-level tests. -/
def node : CtorSpec := (bstSpec.ctors[1]?).getD default

/-! ## Leaves

    The schedules bottom out at three things the interpreter cannot invent: an `Arbitrary Nat`, a
    decision procedure for `≤`, and — once a reordering demotes `Between` to a check — a decision
    procedure for `Between` itself. That last one is worth noticing: reordering premises can demand a
    *checker* for a relation you only have a *generator* for, which is what the compile-time
    pipeline's `DecOpt` derivation supplies. Here it is written by hand, since v1 interprets
    generators only. -/

/-- Decides `Between lo x hi`, standing in for a derived `DecOpt`. -/
def betweenDec (lo x hi : Nat) : Bool := lo < x && x < hi

/-- Everything the schedules bottom out at. The schedules themselves are derived, not registered. -/
def leaves : InterpEnv :=
  (({} : InterpEnv).withArbitrary ``Nat Nat).withDecidable2 ``LE.le (fun a b : Nat => a ≤ b)
    |>.addChecker ``Between (checker3 betweenDec)

/-! ## Ground truth: the schedules `derive_mutual` chooses -/

/-- `Between.BetweenN`, as derived: destructure the upper bound as `succ (succ m)`, check `a₂ ≤ m`,
    return `succ a₂`. -/
def expectedBetweenN : Schedule :=
  ([ .Match .allowImplicit `c_2
       (.CtorPattern ``Nat.succ [.CtorPattern ``Nat.succ [.UnknownPattern `m]])
   , .Check (.NonRec (``LE.le, [.TyCtor ``Nat [], .FuncApp ``instLENat [],
       .Unknown `a_2, .Unknown `m])) true
   ], .ProducerSchedule .Generator [.Ctor ``Nat.succ [.Unknown `a_2]])

/-- `Between.BetweenS`, as derived: destructure as `succ o`, recurse for `m`, return `succ m`. -/
def expectedBetweenS : Schedule :=
  ([ .Match .allowImplicit `c_2 (.CtorPattern ``Nat.succ [.UnknownPattern `o])
   , .SuchThat [(`m, none)] (.Rec `aux_between [.Unknown `a_2, .Unknown `o]) .Generator
   ], .ProducerSchedule .Generator [.Ctor ``Nat.succ [.Unknown `m]])

/-- `BST.BstLeaf`, as derived: no steps at all. -/
def expectedBstLeaf : Schedule :=
  ([], .ProducerSchedule .Generator [.Ctor ``BinaryTree.Leaf []])

/-- `BST.BstNode`, as derived: pick a pivot from `Between`, then recurse into both halves. -/
def expectedBstNode : Schedule :=
  ([ .SuchThat [(`x, none)]
       (.NonRec (``Between, [.Unknown `a_1, .Unknown `x, .Unknown `b_1])) .Generator
   , .SuchThat [(`l, none)] (.Rec `aux_bst [.Unknown `a_1, .Unknown `x]) .Generator
   , .SuchThat [(`r, none)] (.Rec `aux_bst [.Unknown `x, .Unknown `b_1]) .Generator
   ], .ProducerSchedule .Generator
        [.Ctor ``BinaryTree.Node [.Unknown `x, .Unknown `l, .Unknown `r]])

/-- Whether a lowering produced exactly this schedule. Spelled out rather than via `BEq` on
    `Except`, since `PlanError` carries rendered strings that are not worth comparing. -/
def lowersTo (r : Except PlanError Schedule) (s : Schedule) : Bool :=
  match r with
  | .ok s' => s' == s
  | .error _ => false

/-- The schedule `deriveMode` produces for one constructor, for comparison. -/
def derived? (spec : RelSpec) (key : SpecKey) (ctorName : Lean.Name) : Option Schedule :=
  match spec.deriveMode key with
  | .error _ => none
  | .ok rel => rel.ctorSchedule? ctorName

-- Deriving `Between[1]` at runtime reproduces what the compile-time pipeline chose, step for step.
#guard derived? betweenSpec betweenKey ``Between.BetweenN == some expectedBetweenN
#guard derived? betweenSpec betweenKey ``Between.BetweenS == some expectedBetweenS

-- And `BST[2]`. `BstNode`'s three `SuchThat`s are the whole point: which of them is a `Rec` and which
-- is a `NonRec` follows from the ordering, and is recomputed rather than copied.
#guard derived? bstSpec bstKey ``BST.BstLeaf == some expectedBstLeaf
#guard derived? bstSpec bstKey ``BST.BstNode == some expectedBstNode

-- `BstLeaf` is bucketed as non-recursive and `BstNode` as recursive, which is what makes the emitted
-- `match size with | 0 => <base only>` faithful.
/-- info: true -/
#guard_msgs in
#eval match bstSpec.deriveMode bstKey with
  | .error _ => false
  | .ok rel => rel.baseSchedules.map Prod.fst == [``BST.BstLeaf]
      && rel.recSchedules.map Prod.fst == [``BST.BstNode]

/-! ## Ground truth: is the generated tree really a BST? -/

/-- Decides `BST lo hi t` the obvious way, so generated values can be checked independently of the
    interpreter that produced them. -/
def isBST (lo hi : Nat) : BinaryTree → Bool
  | .Leaf => true
  | .Node x l r => lo < x && x < hi && isBST lo x l && isBST x hi r

/-- Reads a `Val` back as a `BinaryTree`. -/
partial def toTree : Val → Except String BinaryTree
  | .ctor ``BinaryTree.Leaf [] => .ok .Leaf
  | .ctor ``BinaryTree.Node [x, l, r] =>
    match x.asNat? with
    | some n => do return .Node n (← toTree l) (← toTree r)
    | none => .error s!"expected a `Nat` label, got `{x}`"
  | v => .error s!"expected a `BinaryTree`, got `{v}`"

/-- Samples `n` trees and counts how many fail `isBST`. A sound interpreter never returns one. -/
def unsoundCount (env : InterpEnv) (lo hi size n : Nat) : IO (Nat × Nat) := do
  let s ← env.sample bstKey size [toVal lo, toVal hi] n n
  let bad := s.samples.filter (fun vals =>
    match vals with
    | [v] => match toTree v with
             | .ok t => !isBST lo hi t
             | .error _ => true
    | _ => true)
  return (s.successes, bad.length)

/-- The environment with every mode `BST[2]` needs derived at runtime. -/
def derivedEnv : Except String InterpEnv :=
  leaves.deriveClosure specs [bstKey]

-- Closing over `BST[2]` brings up exactly the two modes the pipeline derives, and every step of both
-- resolves.
/-- info: (true, "[interp] ok: 2 relation(s) registered, every step resolves") -/
#guard_msgs in
#eval match derivedEnv with
  | .error e => (false, e)
  | .ok env =>
    ((env.relations.toList.map (fun (p : SpecKey × RelSchedule) => renderSpecKey p.1)).all
       (fun s => s == "Between[1] as Generator" || s == "BST[2] as Generator")
     && env.relations.size == 2,
     env.checkReport)

-- Every tree the derived schedules produce for `BST 0 10` really is one, at two sizes.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match derivedEnv with
  | .error _ => return false
  | .ok env => do
    let (n₁, bad₁) ← unsoundCount env 0 10 5 200
    let (n₂, bad₂) ← unsoundCount env 2 20 8 200
    return n₁ == 200 && bad₁ == 0 && n₂ == 200 && bad₂ == 0

-- `Between`'s own outputs land strictly between its bounds.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match derivedEnv with
  | .error _ => return false
  | .ok env => do
    let s ← env.sample betweenKey 6 [toVal 3, toVal 12] 200 200
    let ns := s.samples.filterMap (fun vals =>
      match vals with | [v] => v.asNat? | _ => none)
    return s.successes == 200 && ns.length == 200 && ns.all (fun n => 3 < n && n < 12)

-- `BST 5 6` admits only `Leaf` (no `x` has `5 < x < 6`), so `BstNode` always fails and `BstLeaf`
-- always succeeds: every attempt still produces a value, and it is always `Leaf`.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match derivedEnv with
  | .error _ => return false
  | .ok env => do
    let s ← env.sample bstKey 6 [toVal 5, toVal 6] 200 200
    return s.successes == 200 && s.interpErrors == 0
      && s.samples.all (fun vals => vals == [Val.ctor ``BinaryTree.Leaf []])

/-! ## Reordering premises reinterprets their outputs

    The reason this file schedules from `RelSpec`s rather than holding finished `Schedule`s: a
    different ordering is not a permutation of the same steps. -/

/-- `BST lo x l` scheduled first, before anything has bound `x`. -/
def reorderedNode : Except PlanError Schedule :=
  reschedule bstSpec bstKey node [.use 1, .use 0, .use 2]

/-- What that ordering must produce: the premise now yields both `x` and `l`, so it is a `NonRec` call
    to `BST[1,2]` rather than a `Rec` call to the mode being derived, and `Between` — with nothing
    left to produce — has become a `Check`. -/
def expectedReorderedNode : Schedule :=
  ([ .SuchThat [(`x, none), (`l, none)]
       (.NonRec (``BST, [.Unknown `a_1, .Unknown `x, .Unknown `l])) .Generator
   , .Check (.NonRec (``Between, [.Unknown `a_1, .Unknown `x, .Unknown `b_1])) true
   , .SuchThat [(`r, none)] (.Rec `aux_bst [.Unknown `x, .Unknown `b_1]) .Generator
   ], .ProducerSchedule .Generator
        [.Ctor ``BinaryTree.Node [.Unknown `x, .Unknown `l, .Unknown `r]])

#guard lowersTo reorderedNode expectedReorderedNode

-- The mode it now calls is `BST[1,2]`, which no compile-time derivation produced.
/-- info: ["BST[1,2] as Generator"] -/
#guard_msgs in
#eval match reorderedNode with
  | .error _ => []
  | .ok (steps, _) => (steps.filterMap stepDepKey?).map renderSpecKey

-- `deriveClosure` brings up `BST[1,2]` and, transitively, `Between[1,2]`; the reordered schedule then
-- runs, and is still sound. Note the distinct `recFnName`s: two modes of one relation are two
-- different generators, and sharing a name would silently point one at the other.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match reorderedNode with
  | .error _ => return false
  | .ok sched => do
    let deps := bstKey :: sched.1.filterMap stepDepKey?
    match leaves.deriveClosure specs deps with
    | .error _ => return false
    | .ok closed => do
      let some env := closed.withCtorSchedule bstKey ``BST.BstNode sched | return false
      let fns := env.relations.toList.map (fun (p : SpecKey × RelSchedule) => p.2.recFnName)
      let distinctFns := fns.foldl (fun acc f => if acc.contains f then acc else acc ++ [f]) []
      let (n, bad) ← unsoundCount env 0 10 6 200
      return env.relations.size == 4 && fns.length == distinctFns.length
        && env.check.isEmpty && n == 200 && bad == 0

/-! ## Plans that are not schedules

    Rejection carries a reason, because the reason is what says which plan to try instead. -/

-- Leaving a premise out is not an optimisation: it is a proof obligation left unmet.
/--
info: "the plan leaves 1 premise(s) unscheduled: [Between lo x hi]. Every premise is a proof obligation, so every premise must appear in the plan."
-/
#guard_msgs in
#eval match reschedule bstSpec bstKey node [.use 1, .use 2] with
  | .error e => e.message
  | .ok _ => "unexpectedly lowered"

-- Pre-generating a variable the conclusion already binds is a contradiction, not a choice.
/-- info: "'a_1' is already bound when it is generated unconstrained." -/
#guard_msgs in
#eval match reschedule bstSpec bstKey node [.inst `lo, .use 0, .use 1, .use 2] with
  | .error e => e.message
  | .ok _ => "unexpectedly lowered"

-- The pivot-first plan is the first candidate `plansOf` offers, so a caller taking the head of the
-- list gets what the compile-time pipeline would have chosen.
/-- info: true -/
#guard_msgs in
#eval ((plansOf bstSpec bstKey node (limit := 6)).head?.map
  (fun (_, r) => lowersTo r expectedBstNode)).getD false

/-! ## Where does it discard, and can the discards fix it?

    A schedule that generates a value and then tests it wastes every attempt the test rejects. The
    interpreter attributes each discard to the step that caused it, so the waste is not merely visible
    but addressed to a premise. -/

/-- A deliberately bad plan: generate the pivot blind, then test it. -/
def blindPivot : Plan := [.inst `x, .use 0, .use 1, .use 2]

/-- Which lowers to a generate-and-test schedule. -/
def expectedBlindPivot : Schedule :=
  ([ .Unconstrained `x (.NonRec (``Nat, [])) .Generator
   , .Check (.NonRec (``Between, [.Unknown `a_1, .Unknown `x, .Unknown `b_1])) true
   , .SuchThat [(`l, none)] (.Rec `aux_bst [.Unknown `a_1, .Unknown `x]) .Generator
   , .SuchThat [(`r, none)] (.Rec `aux_bst [.Unknown `x, .Unknown `b_1]) .Generator
   ], .ProducerSchedule .Generator
        [.Ctor ``BinaryTree.Node [.Unknown `x, .Unknown `l, .Unknown `r]])

#guard lowersTo (reschedule bstSpec bstKey node blindPivot) expectedBlindPivot

/-- The blind-pivot schedule, in an environment that can run it. -/
def blindEnv : IO (Option InterpEnv) := do
  match reschedule bstSpec bstKey node blindPivot, derivedEnv with
  | .ok sched, .ok base => return base.withCtorSchedule bstKey ``BST.BstNode sched
  | _, _ => return none

-- The discards land on the `Between` check (step 1) and nowhere else — and they are invisible from
-- the top, where `backtrack` falls through to `BstLeaf` and reports 100% success regardless.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let some env ← blindEnv | return false
  let p ← env.profileCtor bstKey ``BST.BstNode 4 [toVal 0, toVal 6] 300
  let blamedSteps := (p.perStep.filter (fun s => s.discards > 0)).map StepDiscards.stepIdx
  let top ← env.sample bstKey 4 [toVal 0, toVal 6] 300 0
  return p.unattributed == 0 && p.interpErrors == 0 && p.discards > 0
    && blamedSteps == [1] && top.successPerMille == 1000

-- And `Lowered.blame` carries that back to the premise a mutation can move: `Between lo x hi`,
-- premise 0, heaviest and alone.
/-- info: (some 0, true) -/
#guard_msgs in
#eval show IO (Option Nat × Bool) from do
  match rescheduleLowered bstSpec bstKey node blindPivot with
  | .error _ => return (none, false)
  | .ok low => do
    let some env ← blindEnv | return (none, false)
    let p ← env.profileCtor bstKey ``BST.BstNode 4 [toVal 0, toVal 6] 300
    let blamed := low.blame p.stepCounts
    return (blamed.head?.map Prod.fst,
      (blamed.filter (fun q => q.2 > 0)).map Prod.fst == [0])

/-! ### The same conclusion, for free

    `estimateRisk` reaches it without sampling. The model follows `Scoring.BudgetAwareScore`: a step's
    risk is its `Density` (a `SuchThat`'s being its *callee's*, since it fails exactly as often as the
    spec it calls), risks compose by `max` within a constructor and by `min` across a relation's
    constructors, and where a call goes counts too. -/

/-- The relations `deriveClosure` may draw a new mode from, which is what makes a check on one of
    them *avoidable*. -/
def derivable : List Lean.Name := [``Between, ``BST]

-- The mode densities are a fixpoint over the call graph. `Between[1]` is `backtracking`: its
-- `BetweenS` constructor only matches and recurses, and `backtrack` may use it instead of the
-- `BetweenN` that checks — a relation is as strong as its best constructor. `BST[2]` is `total`
-- because `BstLeaf` cannot fail at all.
/-- info: [("Between[1] as Generator", "backtracking"), ("BST[2] as Generator", "total")] -/
#guard_msgs in
#eval match derivedEnv with
  | .error _ => []
  | .ok env => env.modeDensities.toList.map
      (fun (p : SpecKey × Density) => (renderSpecKey p.1, densityRender p.2))

-- The load-bearing correction: `[x] ← Between a_1 x b_1` is *not* risk-free. It inherits
-- `Between[1]`'s `backtracking`, and the estimate says where from.
/-- info: [(0, "backtracking", "Between[1] as Generator"), (1, "partial", "-"), (2, "partial", "-")] -/
#guard_msgs in
#eval match derivedEnv with
  | .error _ => []
  | .ok env =>
    (env.estimateRisk bstKey expectedBstNode specs derivable).steps.map (fun (r : StepRisk) =>
      (r.stepIdx, densityRender r.density, (r.viaCallee.map renderSpecKey).getD "-"))

-- The derived schedule and the blind-pivot one differ where it matters: the blind pivot's worst step
-- is a `check`, which is strictly worse than a match, and it is the one step marked avoidable.
/-- info: (("backtracking", "external", []), "checking", "external", [1]) -/
#guard_msgs in
#eval match derivedEnv with
  | .error _ => (("", "", []), ("", "", []))
  | .ok env =>
    let summarise := fun (sched : Schedule) =>
      let r := env.estimateRisk bstKey sched specs derivable
      (densityRender r.density, r.locality.render,
       (r.steps.filter StepRisk.avoidable).map StepRisk.stepIdx)
    (summarise expectedBstNode, summarise expectedBlindPivot)

-- Reordering into a cross-mode call is penalised on its own axis, after `Scoring.CallLocality`: it
-- spins up a separate generator over the same data rather than sharing the size budget.
/-- info: ("external", "cross-mode") -/
#guard_msgs in
#eval match derivedEnv with
  | .error _ => ("", "")
  | .ok env =>
    ((env.estimateRisk bstKey expectedBstNode specs derivable).locality.render,
     (env.estimateRisk bstKey expectedReorderedNode specs derivable).locality.render)

-- So a static ranking of every ordering puts the schedule the pipeline derives first, before a single
-- sample is drawn — and it does so on density, not on a summed cost.
/-- info: (true, 0, 2, 1) -/
#guard_msgs in
#eval match derivedEnv with
  | .error _ => (false, (0, 0, 0))
  | .ok env =>
    match (rankPlansByRisk env bstSpec bstKey node 24 specs derivable).head? with
    | some (_, r, some risk) =>
      let (sel, den, loc, _) := risk.rank
      (lowersTo r expectedBstNode, (sel, den, loc))
    | _ => (false, (0, 0, 0))

-- Given the measured blame, the tuner mutates its way from the blind-pivot plan to the zero-discard
-- one: stop
-- pre-generating `x` and let `Between` produce it. That is the schedule the compile-time pipeline
-- derives, rediscovered from measurements.
/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  let (best, trace) ← leaves.tunePlan specs bstSpec bstKey ``BST.BstNode 4 [toVal 0, toVal 6]
    (n := 200) (rounds := 3) (start := some blindPivot)
  let startedWorse :=
    match trace.head?.bind (fun t => t.outcome.profile?) with
    | some p => p.discards > 0
    | none => false
  let winner := lowersTo (reschedule bstSpec bstKey node best) expectedBstNode
  let endedClean :=
    match (trace.filter TuneStep.accepted).getLast?.bind (fun t => t.outcome.profile?) with
    | some p => p.discards == 0
    | none => false
  return (startedWorse, winner, endedClean)

end SpecimenTest.InterpBST
