import Basalt.Sized
import Specimen.Enum
import Specimen.Enum.Laws

/-!
# Choice among branches at each reading

`Backtrack` and `Pick` run at the samplers, `Finite`, `CostGraded Finite` and `WFinite`, with and
without failures that say why. Ported with `Specimen.Enum` from the `Backtracking` section of
Basalt's `enum-from-gen` branch's enumeration tests.
-/

open Basalt Specimen

/-- Each value's probability, from a `WFinite`'s entries. -/
def distOf [BEq α] (g : WFinite α) : List (α × Rat) := WFinite.dist ((WFinite.entries? g).getD [])

/-- The search's probability of failing, and each value's probability, at `OptionT WFinite`. -/
def failAndDist [BEq α] (g : OptionT WFinite α) : Rat × List (α × Rat) :=
  let es := (WFinite.entries? (g.run : WFinite (Option α))).getD []
  let fail := (es.filter (·.1.isNone)).foldl (fun s (_, w) => s + w) 0
  (fail, WFinite.dist (es.filterMap fun (a, w) => a.map (·, w)))

/-! ## Backtracking -/

namespace Backtracking

/-- A choice among rules: one weighted branch per rule, `fail` where a rule does not apply. -/
def rules [Monad G] [RandomChoice G] [Fail G] [Backtrack G] (n : Nat) : G Nat :=
  Backtrack.backtrack
    [(3, fun _ => pickFrom [1, 2]), (0, fun _ => pure 9), (1, fun _ => if n = 0 then Fail.fail else pure 3)]

-- The union: each branch's values once, the weight-0 branch never.
#guard (rules (G := Specimen.Finite) 1).toList? == some [1, 2, 3]
#guard (rules (G := Specimen.Finite) 0).toList? == some [1, 2]

-- The search, enumerated: an entry per unit of weight.
#guard (rules (G := OptionT Specimen.Finite) 1).run.toList? ==
  some [some 1, some 2, some 1, some 2, some 1, some 2, some 3]

example (n : Nat) : EnumeratesSome (rules (G := Specimen.Finite) n) (rules (G := OptionT SPMF) n) :=
  EnumeratesSome.backtrack (.cons (EnumeratesSome.pickFrom _) (.cons (EnumeratesSome.pure _)
    (.cons (genRel_enumeratesSome.ite (fun _ => EnumeratesSome.fail) fun _ => EnumeratesSome.pure _)
      .nil)))

/-- The same at a size: each branch reads it. -/
def sizedRules [Monad G] [RandomChoice G] [Fail G] [Sized G] [Backtrack G] : G Nat :=
  Sized.sized fun n =>
    Backtrack.backtrack [(1, fun _ => pure n), (1, fun _ => if n = 0 then Fail.fail else pure (n + 10))]

#guard ((sizedRules (G := WithSize Specimen.Finite)).run 2).toList? == some [2, 12]
#guard ((sizedRules (G := WithSize Specimen.Finite)).run 0).toList? == some [0]

/-- The draw without retry: at an enumeration the same union as `backtrack`, where the draw itself,
enumerated, repeats each branch once per unit of weight. -/
def drawn [Monad G] [RandomChoice G] [Fail G] [Pick G] : G Nat :=
  Pick.pick [(3, fun _ => pickFrom [1, 2]), (0, fun _ => pure 9), (1, fun _ => pure 3)]

#guard (drawn (G := Specimen.Finite)).toList? == some [1, 2, 3]
#guard (drawn (G := OptionT Specimen.Finite)).run.toList? ==
  some [some 1, some 2, some 1, some 2, some 1, some 2, some 3]

/-- A draw that cannot fail, so it runs where there is no failure. -/
def drawnTotal [Monad G] [Pick G] : G Nat :=
  Pick.pick [(3, fun _ => pure 1), (0, fun _ => pure 9), (1, fun _ => pure 3)]

-- Where nothing fails, the draw is `frequency`: the same term, sampled.
example : (drawnTotal (G := Plausible.Gen)) =
    (frequency [(3, fun _ => pure 1), (0, fun _ => pure 9), (1, fun _ => pure 3)] : Plausible.Gen Nat) :=
  rfl
#guard (drawnTotal (G := Specimen.Finite)).toList? == some [1, 3]

/-- Weights that can all be `0`: the draw among the positive ones, or the default. -/
def drawnOr [Monad G] [RandomChoice G] [Pick G] (n : Nat) : G Nat :=
  pickOr (fun _ => pure 0) [(n, fun _ => pure 1), (n, fun _ => pure 2)]

#guard (drawnOr (G := Specimen.Finite) 0).toList? == some [0]
#guard (drawnOr (G := Specimen.Finite) 2).toList? == some [1, 2]

-- Graded by cost, tier `n + 1` is each branch's tier `n`: `3` costs the pick alone, `pickFrom`'s
-- values one draw more.
#guard (List.range 4).map (rules (G := CostGraded Specimen.Finite) 1).tier? ==
  [some [], some [3], some [1, 2], some []]

/-- Unbounded recursion through `backtrack`: each bit costs a pick and a draw. -/
def bits [Gen G] [Fail G] [Backtrack G] [MonoBacktrack G] : G (List Bool) :=
  Backtrack.backtrack
    [(1, fun _ => pure []), (1, fun _ => do return (← pickFrom [true, false]) :: (← bits))]
partial_fixpoint

#guard (List.range 6).map (bits (G := CostGraded Specimen.Finite)).card? ==
  [some 0, some 1, some 0, some 2, some 0, some 4]
#guard (bits (G := CostGraded Specimen.Finite)).tier? 3 == some [[true], [false]]

-- The smallest witness, trying tiers in order: `bits` has nothing at cost 0, `[]` at cost 1.
#guard (bits (G := CostGraded Specimen.Finite)).firstUpTo? 5 == some []
#guard (bits (G := CostGraded Specimen.Finite)).firstUpTo? 0 == none

#guard (List.range 4).map (drawn (G := CostGraded Specimen.Finite)).tier? ==
  [some [], some [3], some [1, 2], some []]

-- The exact distribution: each branch's entries weighted by the probability of reaching it.
#guard WFinite.entries? (rules (G := WFinite) 1) == some [(1, 3/8), (2, 3/8), (3, 1/4)]

/-- Three rules, each of which can fail, one always. -/
def failing [Monad G] [RandomChoice G] [Fail G] [Backtrack G] : G Nat :=
  Backtrack.backtrack [
    (2, fun _ => do
      let n := (← RandomChoice.choose 0 2 (by omega)).down.val
      if n = 0 then Fail.fail else pure n),
    (1, fun _ => Fail.fail),
    (3, fun _ => do
      if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then Fail.fail else pure 5)]

def byValue (l : List (Nat × Rat)) : List (Nat × Rat) := l.mergeSort fun a b => a.1 ≤ b.1

-- The search's distribution, and its probability of failing as what the weights leave of `1`.
#guard byValue (distOf (failing (G := WFinite))) ==
  byValue (failAndDist (failing (G := OptionT WFinite))).2
#guard 1 - ((WFinite.entries? (failing (G := WFinite))).getD []).foldl (fun s (_, w) => s + w) 0 ==
  (failAndDist (failing (G := OptionT WFinite))).1

-- An entry per value, where the search has one per order of retries.
#guard (WFinite.entries? (failing (G := WFinite))).map List.length == some 3
#guard (WFinite.entries? (failing (G := OptionT WFinite)).run).map List.length == some 104

/-- Ten rules, each failing half the time. -/
def coins [Monad G] [RandomChoice G] [Fail G] [Backtrack G] : G Nat :=
  Backtrack.backtrack ((List.range 10).map fun k => (k + 1, fun _ => do
    if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then Fail.fail else pure k))

-- The search fails only if every rule does.
#guard ((WFinite.entries? (coins (G := WFinite))).getD []).foldl (fun s (_, w) => s + w) 0 ==
  1 - 1 / 2 ^ 10

-- `pick` at `WFinite`: each branch weighted by its share, failure the weight left over.
#guard WFinite.entries? (drawn (G := WFinite)) == some [(1, 3/8), (2, 3/8), (3, 1/4)]

/-- `failing`'s rules, drawn once: no retry, so it fails more often. -/
def failingOnce [Monad G] [RandomChoice G] [Fail G] [Pick G] : G Nat :=
  Pick.pick [
    (2, fun _ => do
      let n := (← RandomChoice.choose 0 2 (by omega)).down.val
      if n = 0 then Fail.fail else pure n),
    (1, fun _ => Fail.fail),
    (3, fun _ => do
      if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then Fail.fail else pure 5)]

#guard byValue (distOf (failingOnce (G := WFinite))) ==
  byValue (failAndDist (failingOnce (G := OptionT WFinite))).2
#guard 1 - ((WFinite.entries? (failingOnce (G := WFinite))).getD []).foldl (fun s (_, w) => s + w) 0 ==
  (failAndDist (failingOnce (G := OptionT WFinite))).1

/-! ### Failures that say why -/

/-- A rule that refutes and a rule that could not decide. -/
def undecided [Monad G] [RandomChoice G] [Fail G] [FailWith Unit G] [Backtrack G] : G Nat :=
  Backtrack.backtrack [(1, fun _ => Fail.fail), (1, fun _ => FailWith.failWith ())]

/-- The same, with a rule that succeeds. -/
def decided [Monad G] [RandomChoice G] [Fail G] [FailWith Unit G] [Backtrack G] : G Nat :=
  Backtrack.backtrack
    [(1, fun _ => Fail.fail), (1, fun _ => FailWith.failWith ()), (1, fun _ => pure 7)]

-- The search ends with the label, never refuted: some branch could not decide.
#guard ((undecided (G := ExceptT Unit (OptionT Specimen.Finite))).run.run.toList?).map
  (·.all (· == some (Except.error ()))) == some true
-- With a rule that succeeds, the search retries past the label and always succeeds; the union
-- still lists the label, which says only that some branch could not decide.
#guard ((decided (G := ExceptT Unit (OptionT Specimen.Finite))).run.run.toList?).map
  (·.all (· == some (Except.ok 7))) == some true
#guard (decided (G := ExceptT Unit Specimen.Finite)).run.toList? == some [Except.error (), Except.ok 7]
-- Graded by cost, the label and the success each cost the pick alone: tier `1` lists both.
#guard (List.range 3).map (undecided (G := ExceptT Unit (CostGraded Specimen.Finite))).run.tier? ==
  [some [], some [Except.error ()], some []]
#guard (List.range 3).map (decided (G := ExceptT Unit (CostGraded Specimen.Finite))).run.tier? ==
  [some [], some [Except.error (), Except.ok 7], some []]

/-- Rules that refute, fail with a label and succeed, each with its own probabilities; the labels
join by `max`. -/
def labelled [Monad G] [RandomChoice G] [Fail G] [FailWith Nat G] [Backtrack G] : G Nat :=
  Backtrack.backtrack [
    (2, fun _ => do
      let n := (← RandomChoice.choose 0 2 (by omega)).down.val
      if n = 0 then Fail.fail else if n = 1 then FailWith.failWith 1 else pure n),
    (1, fun _ => do
      if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then FailWith.failWith 2 else Fail.fail),
    (3, fun _ => do
      let n := (← RandomChoice.choose 0 3 (by omega)).down.val
      if n = 0 then Fail.fail else if n = 1 then FailWith.failWith 1 else pure (n + 10))]

/-- `labelled`'s rules, drawn once. -/
def labelledOnce [Monad G] [RandomChoice G] [Fail G] [FailWith Nat G] [Pick G] : G Nat :=
  Pick.pick [
    (2, fun _ => do
      let n := (← RandomChoice.choose 0 2 (by omega)).down.val
      if n = 0 then Fail.fail else if n = 1 then FailWith.failWith 1 else pure n),
    (1, fun _ => do
      if (← RandomChoice.choose 0 1 (by omega)).down.val = 0 then FailWith.failWith 2 else Fail.fail),
    (3, fun _ => do
      let n := (← RandomChoice.choose 0 3 (by omega)).down.val
      if n = 0 then Fail.fail else if n = 1 then FailWith.failWith 1 else pure (n + 10))]

/-- Each outcome's probability, `none` for a refutation, which at `ExceptT ε WFinite` is what the
entries leave of `1`. -/
def outcomes [DecidableEq ε] (g : ExceptT ε WFinite Nat) : List (Option (Except ε Nat) × Rat) :=
  let es := (WFinite.entries? g.run).getD []
  WFinite.dist (((none, 1 - es.foldl (fun s (_, w) => s + w) 0) ::
    es.map fun (r, w) => (some r, w)).filter (·.2 != 0))

/-- The same, read off the search enumerated: an entry per path. -/
def searchOutcomes [DecidableEq ε] (g : ExceptT ε (OptionT WFinite) Nat) :
    List (Option (Except ε Nat) × Rat) :=
  WFinite.dist ((WFinite.entries? g.run.run).getD [])

/-- The same distribution, in any order. -/
def sameDist [BEq β] (l₁ l₂ : List (β × Rat)) : Bool := l₁.length == l₂.length && l₁.all l₂.contains

-- At `WFinite`, the search's distribution, labels and refutation included.
#guard sameDist (outcomes (undecided (G := ExceptT Unit WFinite)))
  (searchOutcomes (undecided (G := ExceptT Unit (OptionT WFinite))))
#guard sameDist (outcomes (decided (G := ExceptT Unit WFinite)))
  (searchOutcomes (decided (G := ExceptT Unit (OptionT WFinite))))
#guard sameDist (outcomes (labelled (G := ExceptT Nat WFinite)))
  (searchOutcomes (labelled (G := ExceptT Nat (OptionT WFinite))))
#guard sameDist (outcomes (labelledOnce (G := ExceptT Nat WFinite)))
  (searchOutcomes (labelledOnce (G := ExceptT Nat (OptionT WFinite))))
-- Refuted only if every rule is: `1/3 * 1/2 * 1/4`.
#guard (outcomes (labelled (G := ExceptT Nat WFinite))).lookup none == some (1/24)

-- An entry per outcome, where the search has one per path.
#guard (WFinite.entries? (undecided (G := ExceptT Unit WFinite)).run) == some [(Except.error (), 1)]
#guard (WFinite.entries? (decided (G := ExceptT Unit WFinite)).run) == some [(Except.ok 7, 1)]
#guard (WFinite.entries? (labelled (G := ExceptT Nat WFinite)).run) == some
  [(.ok 2, 7/30), (.ok 12, 13/60), (.ok 13, 13/60), (.error 1, 1/8), (.error 2, 1/6)]
#guard (WFinite.entries? (labelled (G := ExceptT Nat (OptionT WFinite))).run.run).map List.length ==
  some 492

end Backtracking
