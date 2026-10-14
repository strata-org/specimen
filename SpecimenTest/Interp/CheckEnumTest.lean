import Specimen.Interp
import SpecimenTest.CommonDefinitions.BinaryTree

/-!
# Interpreting checker and enumerator schedules on BST/Between

`Specimen.Interp.CheckEnum` interprets the other two producer sorts. Three claims to pin against
ground truth:

1. **A derived checker decides its predicate.** For `BST 0 10 t`, the interpreter's verdict must agree
   with a hand-written `isBST` on every tree — both trees that are BSTs and trees that are not, so we
   see that refutations really refute.
2. **A derived enumerator produces exactly the solutions.** For `Between 3 b 8`, the enumeration must
   equal the set of `b` satisfying an independent decision procedure. Up to order and duplicates,
   because the emitted enumerator visits every constructor and so `Between 3 4 8` is reachable via
   `BetweenN` and also via `BetweenS` from `Between 3 3 7`.
3. **The mode closure follows `Check` edges.** A checker schedule is *made* of checks, so
   `deriveClosureWith` on a checker root has to follow them or nothing gets derived. This is the
   fixture for that — `BST[]` reaches `Between[]` through a check.
-/

open Plausible Schedules Specimen Specimen.Interp

namespace SpecimenTest.InterpCheckEnum

derive_relspec Between
derive_relspec BST

def specs : List RelSpec := [betweenRelSpec, bstRelSpec]

/-! ## Sample modes

    Three sorts, three keys. A checker mode has no outputs; an enumerator mode has the same output
    positions as the corresponding generator. -/

def bstCheck : SpecKey :=
  { inductiveName := ``BST, outputIndices := [], deriveSort := .Checker }
def betweenCheck : SpecKey :=
  { inductiveName := ``Between, outputIndices := [], deriveSort := .Checker }
def betweenEnum : SpecKey :=
  { inductiveName := ``Between, outputIndices := [1], deriveSort := .Enumerator }

/-! ## Leaves -/

def natEnum : ValEnum := fun size =>
  (LazyList.range (size + 1)).mapLazyList (fun n => .ok (.lit (.natVal n)))

def leaves : InterpEnv :=
  (({} : InterpEnv).withArbitrary ``Nat Nat
    |>.withDecidable2 ``LE.le (fun a b : Nat => a ≤ b))
    |>.addEnum ``Nat natEnum

/-! ## Ground truth -/

def isBST (lo hi : Nat) : BinaryTree → Bool
  | .Leaf => true
  | .Node x l r => lo < x && x < hi && isBST lo x l && isBST x hi r

partial def isBetween : Nat → Nat → Nat → Bool
  | n, .succ b', .succ (.succ c') => (n == b' && n ≤ c') || isBetween n b' (.succ c')
  | _, _, _ => false

def tv : BinaryTree → Val
  | .Leaf => .ctor ``BinaryTree.Leaf []
  | .Node x l r => .ctor ``BinaryTree.Node [.lit (.natVal x), tv l, tv r]

/-! ## Checker derivation -/

-- A checker mode's derived schedule ends in `CheckerSchedule`, not a producer schedule.
/-- info: true -/
#guard_msgs in
#eval match bstRelSpec.deriveMode bstCheck with
  | .error _ => false
  | .ok rel => rel.allSchedules.all (fun (_, (_, sort)) =>
      match sort with | .CheckerSchedule => true | _ => false)

/-! ## Closure follows check edges -/

def checkerEnv : Except String InterpEnv :=
  leaves.deriveClosureWith specs [bstCheck] ({} : PlanBook)

-- Closing over `BST[]` (a checker) brings up `Between[]` (a checker) because `BstNode` checks it.
-- Both are `.Checker` modes, and every step resolves.
/-- info: (true, true, "[interp] ok: 2 relation(s) registered, every step resolves") -/
#guard_msgs in
#eval match checkerEnv with
  | .error e => (false, false, e)
  | .ok env =>
    let sorts := env.relations.toList.map (fun (p : SpecKey × RelSchedule) => p.1.deriveSort)
    (env.relations.size == 2,
     sorts.all (fun s => s == DeriveSort.Checker),
     env.checkReport)

/-! ## Ground truth: the derived checker agrees with `isBST`

    Both directions matter. If `isBST` said `true` and the checker said `false`, or vice versa, we
    would have a soundness bug rather than a completeness one. -/

/-- Trees to check, together with what `isBST 0 10` says about them. -/
def cases : List (BinaryTree × Bool) :=
  let mk := fun (t : BinaryTree) => (t, isBST 0 10 t)
  [ mk .Leaf
  , mk (.Node 5 .Leaf .Leaf)
  , mk (.Node 5 (.Node 2 .Leaf .Leaf) (.Node 8 .Leaf .Leaf))
  , mk (.Node 5 (.Node 8 .Leaf .Leaf) .Leaf)       -- violates: 8 not < 5
  , mk (.Node 5 .Leaf (.Node 2 .Leaf .Leaf))       -- violates: 2 not > 5
  , mk (.Node 1 .Leaf .Leaf)
  , mk (.Node 5 (.Node 2 (.Node 1 .Leaf .Leaf) .Leaf) (.Node 8 .Leaf .Leaf)) ]

-- Every one agrees. `.error` is a failure; only definite verdicts count.
/-- info: (7, 0) -/
#guard_msgs in
#eval match checkerEnv with
  | .error _ => (0, 1)
  | .ok env =>
    cases.foldl (fun (agree, wrong) (t, expected) =>
      match env.decide bstCheck 12 [toVal 0, toVal 10, tv t] with
      | .ok b => if b == expected then (agree + 1, wrong) else (agree, wrong + 1)
      | .error _ => (agree, wrong + 1)) (0, 0)

/-! ## Ground truth: the derived enumerator produces every solution

    "Every" up to duplicates: `Between`'s enumerator concatenates its constructors' contributions
    without deduplicating, and `Between 3 4 8` is reachable via `BetweenN` (`succ 3 = 4`, `3 ≤ 6`)
    and via `BetweenS` from `Between 3 3 7`. So the *set* of enumerated `b`s must equal the set of `b`s
    that satisfy `Between 3 b 8` — which, since `c = succ (succ m)` with `n ≤ m`, is `{4, 5, 6, 7}`. -/

def enumEnv : Except String InterpEnv :=
  leaves.deriveClosureWith specs [betweenEnum] ({} : PlanBook)

/-- info: ([4, 5, 6, 7], true) -/
#guard_msgs in
#eval match enumEnv with
  | .error _ => ([], false)
  | .ok env =>
    let vals := env.enumerateList betweenEnum 8 [toVal 3, toVal 8] 30
    let ns := vals.filterMap (fun (l : List Val) => l.head?.bind Val.asNat?)
    let uniqSorted := (List.range 12).filter (fun n => ns.contains n)
    let truth := (List.range 12).filter (fun b => isBetween 3 b 8)
    (uniqSorted, uniqSorted == truth)

/-! ## The refutation stays definite

    A checker that answered "don't know" on things that are provably false would be useless. The
    interesting case is a *matched* wrong constructor whose recursive check refutes — an inner
    `BstLeaf` cannot fix a `BstNode` whose `x` fails the bounds. -/

/-- info: [(false, false, false), (true, true, true), (false, false, false)] -/
#guard_msgs in
#eval match checkerEnv with
  | .error _ => []
  | .ok env =>
    let ask := fun (t : BinaryTree) =>
      match env.decide bstCheck 12 [toVal 0, toVal 10, tv t] with
      | .ok b => (b, b, isBST 0 10 t)
      | .error _ => (false, true, isBST 0 10 t)   -- the middle bool flags an error
    [ ask (.Node 5 (.Node 8 .Leaf .Leaf) .Leaf)   -- refuted, cleanly
    , ask (.Node 5 .Leaf .Leaf)                   -- accepted
    , ask (.Node 5 (.Node 6 .Leaf .Leaf) .Leaf)  -- refuted (6 not < 5)
    ]

/-! ## What an enumeration costs

    Discards are not the only cost a checker pays. `EnumeratorCombinators.enumeratingOpt` applies the
    check to *every* element of a sub-enumeration, so a step whose enumerator emits a thousand
    candidates before one satisfies costs a thousand check evaluations. Density cannot see this — an
    enumerator that always produces is `Total` whether it yields one candidate or ten thousand — so
    `EnumCost` measures it. -/

def enumEnvCost : Except String InterpEnv :=
  leaves.deriveClosureWith specs [betweenEnum] ({} : PlanBook)

-- The walk grows linearly in the size budget: `Between`'s enumerator recurses once per level, so at
-- size `k` it emits `k + 1` candidates — and walks one entry more, the out-of-fuel entry its size-0
-- level ends in (the emitted enumerator's failsafe: at size 0 the recursive constructors are untried).
/-- info: [(2, 4), (4, 6), (8, 10), (16, 18)] -/
#guard_msgs in
#eval match enumEnvCost with
  | .error _ => []
  | .ok env => [2, 4, 8, 16].map (fun sz =>
      (sz, (env.enumCost betweenEnum sz [toVal 3, toVal 40]).walked))

-- And it saturates once the *size* rather than the interval is the binding constraint: widening
-- `Between 3 . hi` past what size 20 can reach stops adding candidates.
/-- info: (true, true) -/
#guard_msgs in
#eval match enumEnvCost with
  | .error _ => (false, false)
  | .ok env =>
    let at32 := (env.enumCost betweenEnum 20 [toVal 3, toVal 32]).walked
    let at64 := (env.enumCost betweenEnum 20 [toVal 3, toVal 64]).walked
    let at8 := (env.enumCost betweenEnum 20 [toVal 3, toVal 8]).walked
    -- Narrow intervals cost less; wide ones hit the size ceiling and level off.
    (at8 < at32, at32 == at64)

/-! ## A schedule of the wrong sort is refused, not mis-run

    A checker schedule's steps assume `Except GenError Bool` semantics — a non-matching `Match` means
    `.ok false`, not a throw. Running one as a generator would fail somewhere deep for an unrelated
    reason, so `interpRel` checks the sort up front. -/

/-- info: (0, 3, true) -/
#guard_msgs in
#eval show IO (Nat × Nat × Bool) from do
  match checkerEnv with
  | .error _ => return (0, 0, false)
  | .ok env => do
    let s ← env.sample bstCheck 8 [toVal 0, toVal 20] 3 3 (seed := some 1)
    -- Not silently rejected: reported as misconfiguration, with the fix named.
    return (s.rejected, s.interpErrors,
      (s.firstInterpError.getD "").endsWith "for an enumerator")

/-! ## Estimating the width, not just measuring it

    `EnumCost` measures a walk, which costs a walk. For ranking candidate plans the estimate has to be
    free, so `InterpEnv.enumWidthOf` computes it structurally: a constructor's width is the *product* of
    its producing steps' widths (each combination of their outputs is a candidate) and a mode's is the
    **sum** over constructors, because `enumerate` concatenates rather than choosing. That sum-of-products
    is the mirror image of the generator's min-of-max, for the same reason — an enumerator visits every
    alternative, a generator picks one.

    Checks and matches only ever *prune*, by a factor no static pass can know, so they count as neutral
    and the estimate is an **upper bound**. That is the safe direction for a cost. -/

def enumEnvWidth : Except String InterpEnv :=
  leaves.deriveClosureWith specs [betweenEnum] ({} : PlanBook)

-- (Every count below includes the one out-of-fuel entry `Between`'s size-0 level ends in; both the
-- estimate and the walk see it.)
-- On `Between[1]` the estimate is *exact*, because nothing in that schedule draws an unconstrained
-- leaf and — for a wide enough interval — nothing prunes either.
/-- info: [(0, 2, 2), (2, 4, 4), (4, 6, 6), (8, 10, 10), (12, 14, 14)] -/
#guard_msgs in
#eval match enumEnvWidth with
  | .error _ => []
  | .ok env => [0, 2, 4, 8, 12].map (fun sz =>
      (sz, (env.enumWidthOf {} betweenEnum sz).count,
           (env.enumCost betweenEnum sz [toVal 3, toVal 40]).walked))

-- And an upper bound, never an under-estimate, once the `≤` check starts pruning. Narrow intervals
-- walk far less than the bound; a wide one meets it exactly. (`walked` counts list entries: `enumerate`
-- drops definitive failures instead of carrying them as `.error` entries, so the narrow walks read
-- `[1, 4, 12]` rather than `[7, 10, 18]`; the size-0 out-of-fuel entry is inconclusive and survives.)
/-- info: (22, [1, 4, 12, 22], true) -/
#guard_msgs in
#eval match enumEnvWidth with
  | .error _ => (0, [], false)
  | .ok env =>
    let bound := (env.enumWidthOf {} betweenEnum 20).count
    let walks := [5, 8, 16, 32].map (fun hi =>
      (env.enumCost betweenEnum 20 [toVal 3, toVal hi]).walked)
    (bound, walks, walks.all (fun w => decide (w ≤ bound)))

/-! ## The width is inert for generators and decisive for checkers

    A generator's `SuchThat` draws *one* value from its callee, so it pays nothing per candidate; a
    checker's applies the check to all of them. `ScheduleRisk.enumWidth` is therefore `0` for a
    generator schedule and the dominant term for a checker one. -/

/-- `BST[1]` as a checker: with `hi` unbound, the checker has to enumerate candidates for it. -/
def bstCheckEx : SpecKey :=
  { inductiveName := ``BST, outputIndices := [1], deriveSort := .Checker }

/-- info: (0, true) -/
#guard_msgs in
#eval
  let genKey : SpecKey := { inductiveName := ``BST, outputIndices := [2], deriveSort := .Generator }
  match leaves.deriveClosure specs [genKey], leaves.deriveClosureWith specs [bstCheckEx] ({} : PlanBook) with
  | .ok genEnv, .ok chkEnv =>
    let gnode := (ctorSpecOf? specs genKey ``BST.BstNode).getD default
    let cnode := (ctorSpecOf? specs bstCheckEx ``BST.BstNode).getD default
    let gw := match reschedule bstRelSpec genKey gnode [.use 0, .use 1, .use 2] with
      | .ok sc => (genEnv.estimateRisk genKey sc specs [] 8).enumWidth
      | .error _ => 99999
    let cw := match reschedule bstRelSpec bstCheckEx cnode [.use 0, .use 1, .use 2] with
      | .ok sc => (chkEnv.estimateRisk bstCheckEx sc specs [] 8).enumWidth
      | .error _ => 0
    (gw, decide (cw > 0))
  | _, _ => (99999, false)

-- Widening the assumed leaf width widens the estimate proportionally, which is the lever a caller has
-- when they know a domain is large.
/-- info: (73, 577) -/
#guard_msgs in
#eval match leaves.deriveClosureWith specs [bstCheckEx] ({} : PlanBook) with
  | .error _ => (0, 0)
  | .ok env =>
    let cnode := (ctorSpecOf? specs bstCheckEx ``BST.BstNode).getD default
    let widthUnder := fun (m : EnumWidthModel) =>
      match reschedule bstRelSpec bstCheckEx cnode [.use 0, .use 1, .use 2] with
      | .ok sc => (env.estimateRisk bstCheckEx sc specs [] 8 m).enumWidth
      | .error _ => 0
    (widthUnder {}, widthUnder { leaves := [(``Nat, 64)] })

/-! ## An underived mode is expensive, not cheap

    The subtle failure this guards against: a plan calling a mode the closure never derived has an
    *unknown* width, and since the estimate is an upper bound on cost, unknown has to be pessimistic.
    Assuming the default instead made such a plan rank as the cheapest available — exactly backwards,
    because an underived mode is the one most likely to be ruinous. -/

/-- info: (true, true) -/
#guard_msgs in
#eval match leaves.deriveClosureWith specs [bstCheckEx] ({} : PlanBook) with
  | .error _ => (false, false)
  | .ok env =>
    -- `BST[1,2] as Enumerator` is not in this closure.
    let absent : SpecKey :=
      { inductiveName := ``BST, outputIndices := [1, 2], deriveSort := .Enumerator }
    let w := env.enumWidthOf {} absent 8
    ((env.relations[absent]?).isNone, w.saturated && w.count == (({} : EnumWidthModel)).ceiling)

/-! ## The estimate is memoised, and has to be

    Without a memo the recursion is exponential in depth: each mode expands every dependency, which
    expands every one of *its* dependencies. On Cedar's 145-mode closure that did not terminate in ten
    minutes, while the memoised version answers in well under a second. The `ceiling` caps the
    arithmetic, not the recursion — a distinction that is easy to conflate and expensive to get wrong.

    The memo also breaks cycles: the in-progress key is seeded with a saturated placeholder before
    recursing, so a same-size cross-family call reads that instead of looping. -/

-- Asking repeatedly agrees with itself, and a mode reachable by several paths is consistent however it
-- is reached — the property a memo has to preserve to be sound rather than merely fast.
/-- info: true -/
#guard_msgs in
#eval match enumEnvWidth with
  | .error _ => false
  | .ok env =>
    let once := env.enumWidthOf {} betweenEnum 8
    let twice := env.enumWidthOf {} betweenEnum 8
    -- Also stable under a tighter fuel budget, since the memo bounds the work rather than the fuel.
    let tight := env.enumWidthOf {} betweenEnum 8 (fuel := 12)
    once.count == twice.count && once.count == tight.count

/-! ## Leaf widths are measured, not assumed

    The estimate is only as good as its leaf numbers, and a wrong one propagates multiplicatively
    through every product. A `ValEnum` is a function, so its cardinality is discoverable only by walking
    it — but walking every *leaf* once is cheap, and leaves are where the recursion bottoms out. -/

/-- info: ([(`Nat, 2), (`Nat, 5), (`Nat, 9)], [26, 82]) -/
#guard_msgs in
#eval match leaves.deriveClosureWith specs [bstCheckEx] ({} : PlanBook) with
  | .error _ => ([], [])
  | .ok env =>
    let cnode := (ctorSpecOf? specs bstCheckEx ``BST.BstNode).getD default
    let widthAt := fun (sz : Nat) =>
      match reschedule bstRelSpec bstCheckEx cnode [.use 0, .use 1, .use 2] with
      | .ok sc => (env.estimateRisk bstCheckEx sc specs [] sz (env.calibratedWidthModel sz)).enumWidth
      | .error _ => 0
    -- `Nat`'s enumerator yields `size + 1`; the constructor has two producing steps, so the estimate
    -- is that squared.
    ([1, 4, 8].flatMap (fun sz => env.calibrateLeafWidths sz), [widthAt 4, widthAt 8])

end SpecimenTest.InterpCheckEnum
