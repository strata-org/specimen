/-
  Model and property-based verification that (maxDensity, sumVarDeps) is a valid
  lower bound under the SearchTree's insertion-based schedule construction.

  Key insight: when a hypothesis is inserted before existing ones in an ordering,
  it binds additional variables. This causes existing hypotheses to:
  - Have more inputs (varDeps increases)
  - Have fewer outputs (density can only worsen: fewer outputs = harder constraint satisfaction)

  Therefore both components are monotonically non-decreasing under insertion,
  making (maxDensity, sumVarDeps) sound for pruning.
-/

----------------------------------------------
-- Model
----------------------------------------------

inductive Density where
  | Total
  | Partial
  | Backtracking
  | Checking
  deriving Repr, BEq, Inhabited, DecidableEq

namespace Density

def toNat : Density → Nat
  | .Total => 0
  | .Partial => 1
  | .Backtracking => 2
  | .Checking => 3

instance : Ord Density where
  compare a b := compare a.toNat b.toNat

instance : LE Density where
  le a b := a.toNat ≤ b.toNat

instance : LT Density where
  lt a b := a.toNat < b.toNat

instance : DecidableRel (fun (a b : Density) => a ≤ b) :=
  fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance : DecidableRel (fun (a b : Density) => a < b) :=
  fun a b => inferInstanceAs (Decidable (a.toNat < b.toNat))

def max (a b : Density) : Density := if a.toNat ≥ b.toNat then a else b

end Density

/-- A hypothesis has a name, and references a set of variables (by index). -/
structure Hypothesis where
  name : String
  vars : List Nat
  deriving Repr, BEq

/-- Given a hypothesis and the set of already-bound variables, compute what mode it runs in.
    - If all vars are bound → Check (density = Checking, varDeps = all vars)
    - Otherwise → Produce unbound vars (density from lookup, varDeps = bound vars count) -/
structure StepScore where
  density : Density
  varDeps : Nat
  deriving Repr, BEq

/-- Density lookup: given the number of outputs a dep produces, return its density.
    Models the assumption: more outputs = better (lower) density. -/
def depDensity (numOutputs : Nat) (totalVars : Nat) : Density :=
  if numOutputs == totalVars then .Total
  else if numOutputs == 0 then .Checking
  else if numOutputs > totalVars / 2 then .Partial
  else .Backtracking

/-- Score a single hypothesis given the current environment (bound variables). -/
def scoreHypothesis (h : Hypothesis) (boundVars : List Nat) : StepScore :=
  let bound := h.vars.filter (boundVars.contains ·)
  let unbound := h.vars.filter (!boundVars.contains ·)
  if unbound.isEmpty then
    -- Check: all vars already bound
    { density := .Checking, varDeps := h.vars.length }
  else
    -- Produce: unbound vars are outputs, bound vars are inputs (varDeps)
    { density := depDensity unbound.length h.vars.length, varDeps := bound.length }

/-- Score an entire ordering: max density, sum of varDeps. -/
def scoreOrdering (hyps : List Hypothesis) (ordering : List Nat) : Density × Nat := Id.run do
  let mut maxDens := Density.Total
  let mut totalVarDeps := 0
  let mut boundVars : List Nat := []
  for idx in ordering do
    match hyps[idx]? with
    | some h =>
      let score := scoreHypothesis h boundVars
      maxDens := Density.max maxDens score.density
      totalVarDeps := totalVarDeps + score.varDeps
      -- After processing, all vars of this hypothesis become bound
      boundVars := boundVars ++ h.vars
    | none => pure ()
  return (maxDens, totalVarDeps)

----------------------------------------------
-- Property: insertion can only worsen score
----------------------------------------------

/-- Insert element `x` at position `pos` in list `l`. -/
def insertAt (l : List α) (pos : Nat) (x : α) : List α :=
  l.take pos ++ [x] ++ l.drop pos

/-- Check that inserting a hypothesis at any position in an existing ordering
    produces a score ≥ the original (componentwise). -/
def checkInsertionMonotonicity (hyps : List Hypothesis) (ordering : List Nat) (newIdx : Nat) : Bool := Id.run do
  let origScore := scoreOrdering hyps ordering
  let mut allGood := true
  let mut pos := 0
  while pos ≤ ordering.length do
    let newOrdering := insertAt ordering pos newIdx
    let newScore := scoreOrdering hyps newOrdering
    -- Check: density can only increase or stay same
    if newScore.1.toNat < origScore.1.toNat then
      allGood := false
    -- Check: varDeps can only increase or stay same
    if newScore.2 < origScore.2 then
      allGood := false
    pos := pos + 1
  return allGood

----------------------------------------------
-- Random testing infrastructure
----------------------------------------------

private structure Rng where
  state : UInt64

private def Rng.next (rng : Rng) : Rng × UInt64 :=
  let s := rng.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

private def Rng.natBelow (rng : Rng) (n : Nat) : Rng × Nat :=
  if n == 0 then (rng, 0)
  else let (rng', v) := rng.next; (rng', v.toNat % n)

private def genHypotheses (rng : Rng) : Rng × List Hypothesis := Id.run do
  let (rng, numHyps) := rng.natBelow 5
  let numHyps := numHyps + 2  -- 2..6
  let (rng, numVars) := rng.natBelow 5
  let numVars := numVars + 2  -- 2..6
  let mut rng := rng
  let mut hyps : List Hypothesis := []
  let mut i := 0
  while i < numHyps do
    let (rng', numHypVars) := rng.natBelow 3
    rng := rng'
    let numHypVars := numHypVars + 1  -- 1..3
    let mut vars : List Nat := []
    let mut j := 0
    while j < numHypVars do
      let (rng', v) := rng.natBelow numVars
      rng := rng'
      if !vars.contains v then
        vars := vars ++ [v]
      j := j + 1
    hyps := hyps ++ [{ name := s!"H{i}", vars := vars }]
    i := i + 1
  return (rng, hyps)

private def shuffle (rng : Rng) (l : List α) : Rng × List α := Id.run do
  let mut rng := rng
  let mut arr := l.toArray
  let mut i := arr.size
  while i > 1 do
    i := i - 1
    let (rng', j) := rng.natBelow (i + 1)
    rng := rng'
    match arr[i]?, arr[j]? with
    | some vi, some vj =>
      arr := arr.set! i vj |>.set! j vi
    | _, _ => pure ()
  return (rng, arr.toList)

----------------------------------------------
-- Test 1: Insertion monotonicity
-- For random hypothesis sets and random partial orderings,
-- verify that inserting a new hypothesis at any position
-- cannot decrease (maxDensity, sumVarDeps).
----------------------------------------------

private def testInsertionMonotonicity : IO String := do
  let numTrials := 10000
  let mut rng : Rng := { state := 42 }
  let mut violations := 0
  let mut tests := 0
  let mut firstViolation : Option String := none
  let mut trial := 0
  while trial < numTrials do
    let (rng', hyps) := genHypotheses rng
    rng := rng'
    let indices := List.range hyps.length
    -- Generate a random partial ordering (subset + shuffle)
    let (rng', subsetSize) := rng.natBelow hyps.length
    rng := rng'
    let (rng', ordering) := shuffle rng (indices.take (subsetSize + 1))
    rng := rng'
    -- Pick a hypothesis NOT in the ordering to insert
    let remaining := indices.filter (!ordering.contains ·)
    if !remaining.isEmpty then
      let (rng', pickIdx) := rng.natBelow remaining.length
      rng := rng'
      match remaining[pickIdx]? with
      | some newIdx =>
        tests := tests + 1
        if !checkInsertionMonotonicity hyps ordering newIdx then
          violations := violations + 1
          if firstViolation.isNone then
            let origScore := scoreOrdering hyps ordering
            -- Find the violating position
            let mut vPos := 0
            let mut found := false
            while vPos ≤ ordering.length && !found do
              let newOrdering := insertAt ordering vPos newIdx
              let newScore := scoreOrdering hyps newOrdering
              if newScore.1.toNat < origScore.1.toNat || newScore.2 < origScore.2 then
                firstViolation := some s!"hyps={repr hyps}\nordering={ordering}\ninsert H{newIdx} at pos {vPos}\norig=({origScore.1.toNat},{origScore.2}) new=({newScore.1.toNat},{newScore.2})"
                found := true
              vPos := vPos + 1
      | none => pure ()
    trial := trial + 1
  if violations > 0 then
    return s!"FAILED: {violations}/{tests} violations\nFirst:\n{firstViolation.getD ""}"
  else
    return s!"PASSED: {tests} tests — (maxDensity, sumVarDeps) monotonically non-decreasing under insertion"

#eval do IO.println (← testInsertionMonotonicity)

----------------------------------------------
-- Test 2: Full ordering extension (append)
-- For random orderings, verify that appending one more hypothesis
-- to the end only increases the score.
----------------------------------------------

private def permutations (l : List α) : List (List α) :=
  match l with
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap fun perm =>
    (List.range (perm.length + 1)).map fun i => perm.take i ++ [x] ++ perm.drop i

private def testPrefixMonotonicity : IO String := do
  let numTrials := 5000
  let mut rng : Rng := { state := 7777 }
  let mut violations := 0
  let mut tests := 0
  let mut firstViolation : Option String := none
  let mut trial := 0
  while trial < numTrials do
    let (rng', hyps) := genHypotheses rng
    rng := rng'
    if hyps.length ≤ 5 then
      let indices := List.range hyps.length
      let perms := permutations indices
      for perm in perms do
        let mut i := 1
        while i < perm.length do
          let pfx := perm.take i
          let extended := perm.take (i + 1)
          let pfxScore := scoreOrdering hyps pfx
          let extendedScore := scoreOrdering hyps extended
          tests := tests + 1
          if extendedScore.1.toNat < pfxScore.1.toNat || extendedScore.2 < pfxScore.2 then
            violations := violations + 1
            if firstViolation.isNone then
              firstViolation := some s!"hyps={repr hyps}\npfx={pfx} extended={extended}\npfxScore=({pfxScore.1.toNat},{pfxScore.2}) extendedScore=({extendedScore.1.toNat},{extendedScore.2})"
          i := i + 1
    trial := trial + 1
  if violations > 0 then
    return s!"FAILED: {violations}/{tests} violations\nFirst:\n{firstViolation.getD ""}"
  else
    return s!"PASSED: {tests} prefix extensions — score monotonically non-decreasing"

#eval do IO.println (← testPrefixMonotonicity)

----------------------------------------------
-- Test 3: Lower bound validity
-- For complete orderings, verify that the score of any prefix
-- is ≤ the score of the full ordering.
----------------------------------------------

private def testLowerBoundValidity : IO String := do
  let numTrials := 5000
  let mut rng : Rng := { state := 99999 }
  let mut violations := 0
  let mut tests := 0
  let mut firstViolation : Option String := none
  let mut trial := 0
  while trial < numTrials do
    let (rng', hyps) := genHypotheses rng
    rng := rng'
    if hyps.length ≤ 5 then
      let indices := List.range hyps.length
      let perms := permutations indices
      for perm in perms do
        let fullScore := scoreOrdering hyps perm
        let mut i := 0
        while i < perm.length do
          let pfx := perm.take i
          let pfxScore := scoreOrdering hyps pfx
          tests := tests + 1
          if pfxScore.1.toNat > fullScore.1.toNat || pfxScore.2 > fullScore.2 then
            violations := violations + 1
            if firstViolation.isNone then
              firstViolation := some s!"hyps={repr hyps}\nperm={perm} pfx={pfx}\npfxScore=({pfxScore.1.toNat},{pfxScore.2}) fullScore=({fullScore.1.toNat},{fullScore.2})"
          i := i + 1
    trial := trial + 1
  if violations > 0 then
    return s!"FAILED: {violations}/{tests} violations\nFirst:\n{firstViolation.getD ""}"
  else
    return s!"PASSED: {tests} tests — every prefix score ≤ full ordering score (valid lower bound)"

#eval do IO.println (← testLowerBoundValidity)
