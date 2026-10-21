import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import Specimen.DeriveChecker
import SpecimenTest.CommonDefinitions.STLCDefinitions
import Bench.StlcLevels

open StlcLevels

/-!
# Where the derived enumerator's time goes: an ablation ladder from derived code to levels

`GradedVsDerivedSameDiscipline.lean` shows that levels built to the derived enumerator's own budget rule
enumerate the same set much faster. This file attributes that gap. It walks from the derived enumerator
to levels one change at a time, checks that every rung enumerates the same set, and times each:

* **L0** — the enumerator `derive_mutual` emits for STLC `typing`, but derived with an in-order
  concatenating `bind` installed in place of `LazyList`'s round-robin. Comparing L0 with the same-discipline
  file's derived enumerator isolates the round-robin.
* **L1** — a hand copy of L0's emitted `eq_def`, rule for rule (and **L1s**, with `lookup` given
  `Γ.length` instead of the undivided `initSize`).
* **L2** — L1 with the derived `lookup` enumerator replaced by a direct scan of `Γ`.
* **L3** — L2 without `Except`: a failed match is an empty list rather than an inline `.error` entry.
* **L4** — L3 on strict `List`s, same budget rule and recursion.
* **L5** — levels (`lvA`), the same set as disjoint levels with a max convolution.

Measured (compiled, goal `Nat → Nat`, budget 11, all 57 866 terms): the emitted enumerator 693 ms, L0 490,
L1 414, L2 353, L3 123, L4 16, L5 5. No single change dominates: laziness (L3 → L4) is about 8×, `Except`
about 3×, nested budgets against exact levels about 3×, round-robin about 1.4× (it was about 100× before
`LazyList.roundRobinConcat` got a two-list queue). Strict lists win when every term is forced, but not
for the first `k`: the second entry point measures that, with peak memory read from
`/proc/self/status`. At budget 15, the first 1 000 terms cost 333 ms and 235 MB on strict lists (L4)
against about 35 ms and 65 MB on the lazy rungs and on levels.

Not imported by the test suite: it installs high-priority `Enum` and `Monad Enumerator` instances before
deriving, which would leak. Compiled by `lake build Bench`; run with
`lake exe bench-concat-ablation ladder [fun] BUDGET…` or `lake exe bench-concat-ablation RUNG BUDGET K`
(see `bench/README.md`).
-/

/-! ## The restricted leaf universe — must precede `derive_mutual` -/

instance (priority := high) : Enum type where
  enum := fun _ => LazyList.fromList [type.Nat, type.Fun type.Nat type.Nat]
instance (priority := high) : EnumSized type where
  enumSized := fun _ _ => LazyList.fromList [type.Nat, type.Fun type.Nat type.Nat]
instance (priority := high) : Enum Nat where
  enum := fun _ => LazyList.fromList [0]
instance (priority := high) : EnumSized Nat where
  enumSized := fun _ _ => LazyList.fromList [0]

/-! ## ABLATION: bind by in-order concatenation instead of round-robin, installed before deriving -/

def concatBindEnum (e : Enumerator α) (k : α → Enumerator β) : Enumerator β :=
  fun n => LazyList.concat ((e n).mapLazyList fun x => k x n)

instance (priority := high) : Monad Enumerator where
  pure := pureEnum
  bind := concatBindEnum

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

#guard_msgs(drop info) in
derive_mutual enumerator (fun Γ τ => ∃ (e : term), typing Γ e τ)


namespace SameDisciplineConcat

/-- The derived enumerator's set at budget `s`, errors dropped. -/
def derivedAt (Γ : List type) (τ : type) (s : Nat) : LazyList term :=
  ((EnumSizedSuchThat.enumSizedST (fun e => typing Γ e τ) s) s).filter (·.toOption.isSome)
    |>.mapLazyList fun r => match r with | .ok e => e | .error _ => .Const 0


end SameDisciplineConcat

-- The derived set and the levels agree at every budget checked, for both goal types, before anything is
-- timed. If the deriver's schedule for `typing` changes, this fails the build.
open SameDisciplineConcat in
#guard [type.Nat, .Fun .Nat .Nat].all fun τ =>
  (List.range 8).all fun s => sameSet (derivedAt [] τ s).toList (levelsUpTo [] τ s)

namespace SameDisciplineConcat

def timeIt (act : Unit → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0) / 1000000)

/-- Levels upward, stopping once `k` terms are in hand (the `k` lowest-budget terms). -/
partial def firstK (k s : Nat) (lvl : Nat → List term) (n acc : Nat := 0) : Nat :=
  if n > s || acc ≥ k then acc else firstK k s lvl (n + 1) (acc + (lvl n).length)

end SameDisciplineConcat

/-! ## Ablation ladder: derived → levels, one change per rung

Every rung enumerates the same set (checked). Bind is the concatenating one installed above. -/

namespace Ladder
open Plausible

-- **L1** — a hand copy of the emitted `eq_def`, rule for rule.
partial def l1A (fuel initSize size : Nat) (Γ : List type) (τ : type) : ExceptT GenError Enumerator term :=
  match fuel with
  | 0 => throw Gen.outOfFuelError
  | fuel' + 1 =>
    let leaves : List (ExceptT GenError Enumerator term) :=
      [ match τ with
        | .Nat => do let n ← ExceptT.lift (Enum.enum : Enumerator Nat); pure (term.Const n)
        | _ => throw Gen.genericFailure
      , do let x ← EnumSizedSuchThat.enumSizedST (fun x => lookup Γ x τ) initSize; pure (term.Var x) ]
    match size with
    | 0 => EnumeratorCombinators.enumerate (leaves ++ [throw Gen.outOfFuelError])
    | size' + 1 => EnumeratorCombinators.enumerate (leaves ++
      [ match τ with
        | .Nat => do
            let e1 ← l1A fuel' initSize (size' / 2) Γ .Nat
            let e2 ← l1A fuel' initSize (size' / 2) Γ .Nat
            pure (.Add e1 e2)
        | _ => throw Gen.genericFailure
      , match τ with
        | .Fun τ1 τ2 => do let e ← l1A fuel' initSize size' (τ1 :: Γ) τ2; pure (.Abs τ1 e)
        | _ => throw Gen.genericFailure
      , do
          let τ1 ← ExceptT.lift (Enum.enum : Enumerator type)
          let e1 ← l1A fuel' initSize (size' / 2) Γ (.Fun τ1 τ)
          let e2 ← l1A fuel' initSize (size' / 2) Γ τ1
          pure (.App e1 e2) ])

-- **L1s** — L1 with `lookup` given `Γ.length` instead of the undivided `initSize`.
partial def l1sA (fuel initSize size : Nat) (Γ : List type) (τ : type) : ExceptT GenError Enumerator term :=
  match fuel with
  | 0 => throw Gen.outOfFuelError
  | fuel' + 1 =>
    let leaves : List (ExceptT GenError Enumerator term) :=
      [ match τ with
        | .Nat => do let n ← ExceptT.lift (Enum.enum : Enumerator Nat); pure (term.Const n)
        | _ => throw Gen.genericFailure
      , do let x ← EnumSizedSuchThat.enumSizedST (fun x => lookup Γ x τ) Γ.length; pure (term.Var x) ]
    match size with
    | 0 => EnumeratorCombinators.enumerate (leaves ++ [throw Gen.outOfFuelError])
    | size' + 1 => EnumeratorCombinators.enumerate (leaves ++
      [ match τ with
        | .Nat => do
            let e1 ← l1sA fuel' initSize (size' / 2) Γ .Nat
            let e2 ← l1sA fuel' initSize (size' / 2) Γ .Nat
            pure (.Add e1 e2)
        | _ => throw Gen.genericFailure
      , match τ with
        | .Fun τ1 τ2 => do let e ← l1sA fuel' initSize size' (τ1 :: Γ) τ2; pure (.Abs τ1 e)
        | _ => throw Gen.genericFailure
      , do
          let τ1 ← ExceptT.lift (Enum.enum : Enumerator type)
          let e1 ← l1sA fuel' initSize (size' / 2) Γ (.Fun τ1 τ)
          let e2 ← l1sA fuel' initSize (size' / 2) Γ τ1
          pure (.App e1 e2) ])

def run1s (Γ : List type) (τ : type) (s : Nat) : List term :=
  ((l1sA 10000 s s Γ τ) s).toList.filterMap (·.toOption)

def run1 (Γ : List type) (τ : type) (s : Nat) : List term :=
  ((l1A 10000 s s Γ τ) s).toList.filterMap (·.toOption)

-- **L2** — L1 with the derived `lookup` enumerator replaced by a direct scan of `Γ`.
partial def l2A (fuel size : Nat) (Γ : List type) (τ : type) : ExceptT GenError Enumerator term :=
  match fuel with
  | 0 => throw Gen.outOfFuelError
  | fuel' + 1 =>
    let leaves : List (ExceptT GenError Enumerator term) :=
      [ match τ with
        | .Nat => do let n ← ExceptT.lift (Enum.enum : Enumerator Nat); pure (term.Const n)
        | _ => throw Gen.genericFailure
      , fun _ => LazyList.fromList ((StlcLevels.varsAt Γ τ).map .ok) ]
    match size with
    | 0 => EnumeratorCombinators.enumerate (leaves ++ [throw Gen.outOfFuelError])
    | size' + 1 => EnumeratorCombinators.enumerate (leaves ++
      [ match τ with
        | .Nat => do
            let e1 ← l2A fuel' (size' / 2) Γ .Nat
            let e2 ← l2A fuel' (size' / 2) Γ .Nat
            pure (.Add e1 e2)
        | _ => throw Gen.genericFailure
      , match τ with
        | .Fun τ1 τ2 => do let e ← l2A fuel' size' (τ1 :: Γ) τ2; pure (.Abs τ1 e)
        | _ => throw Gen.genericFailure
      , do
          let τ1 ← ExceptT.lift (Enum.enum : Enumerator type)
          let e1 ← l2A fuel' (size' / 2) Γ (.Fun τ1 τ)
          let e2 ← l2A fuel' (size' / 2) Γ τ1
          pure (.App e1 e2) ])

def run2 (Γ : List type) (τ : type) (s : Nat) : List term :=
  ((l2A 10000 s Γ τ) s).toList.filterMap (·.toOption)

-- **L3** — L2 without `Except`: a failed match is an empty list, not an inline `.error` entry. Still lazy.
partial def l3A (size : Nat) (Γ : List type) (τ : type) : LazyList term :=
  let leaves := (match τ with | .Nat => LazyList.fromList [term.Const 0] | _ => .lnil).append
    (LazyList.fromList (StlcLevels.varsAt Γ τ))
  match size with
  | 0 => leaves
  | size' + 1 =>
    let m := size' / 2
    let add := match τ with
      | .Nat => LazyList.concat ((l3A m Γ .Nat).mapLazyList fun e1 =>
          (l3A m Γ .Nat).mapLazyList fun e2 => term.Add e1 e2)
      | _ => .lnil
    let abs := match τ with
      | .Fun τ1 τ2 => (l3A size' (τ1 :: Γ) τ2).mapLazyList (term.Abs τ1)
      | _ => .lnil
    let app := LazyList.concat ((LazyList.fromList StlcLevels.tyLeaves).mapLazyList fun τ1 =>
      LazyList.concat ((l3A m Γ (.Fun τ1 τ)).mapLazyList fun e1 =>
        (l3A m Γ τ1).mapLazyList fun e2 => term.App e1 e2))
    leaves.append (add.append (abs.append app))

-- **L4** — L3 with strict `List`s. Same budget rule and recursion as the derived code; the only
--     difference left from levels is nested budgets vs exact levels.
partial def l4A (size : Nat) (Γ : List type) (τ : type) : List term :=
  let leaves := (match τ with | .Nat => [term.Const 0] | _ => []) ++ StlcLevels.varsAt Γ τ
  match size with
  | 0 => leaves
  | size' + 1 =>
    let m := size' / 2
    let add := match τ with
      | .Nat => (l4A m Γ .Nat).flatMap fun e1 => (l4A m Γ .Nat).map fun e2 => term.Add e1 e2
      | _ => []
    let abs := match τ with
      | .Fun τ1 τ2 => (l4A size' (τ1 :: Γ) τ2).map (term.Abs τ1)
      | _ => []
    let app := StlcLevels.tyLeaves.flatMap fun τ1 =>
      (l4A m Γ (.Fun τ1 τ)).flatMap fun e1 => (l4A m Γ τ1).map fun e2 => term.App e1 e2
    leaves ++ add ++ abs ++ app

end Ladder

-- Every rung enumerates the derived set.
open SameDisciplineConcat Ladder in
#guard [type.Nat, .Fun .Nat .Nat].all fun g => (List.range 8).all fun s =>
  let d := (derivedAt [] g s).toList
  sameSet d (run1s [] g s) && sameSet d (run1 [] g s) && sameSet d (run2 [] g s) &&
    sameSet d (l3A s [] g).toList && sameSet d (l4A s [] g)

open SameDisciplineConcat Ladder in
def ladder (args : List String) : IO Unit := do
  let goal := if args.head? == some "fun" then type.Fun .Nat .Nat else type.Nat
  let z ← IO.rand 0 0
  IO.println s!"ladder, goal {repr goal}"
  for s0 in (args.drop 1).filterMap String.toNat? do
    let s := s0 + z
    let (n0, t0) ← timeIt fun _ => (derivedAt [] goal s).length
    let (_, t1) ← timeIt fun _ => (run1 [] goal s).length
    let (_, t1s) ← timeIt fun _ => (run1s [] goal s).length
    IO.println s!"  budget {s}: L1 with lookup at |Γ| {t1s}ms"
    let (_, t2) ← timeIt fun _ => (run2 [] goal s).length
    let (_, t3) ← timeIt fun _ => (l3A s [] goal).length
    let (_, t4) ← timeIt fun _ => (l4A s [] goal).length
    let (_, t5) ← timeIt fun _ => (levelsUpTo [] goal s).length
    IO.println s!"  budget {s} ({n0} terms): L0 derived {t0}ms  L1 copy {t1}ms  L2 -lookup {t2}ms  \
      L3 -Except {t3}ms  L4 strict {t4}ms  L5 levels {t5}ms"

/-! ## Does the carrier survive a big budget, and how fast is the FIRST k?

The ladder above forced every term, which is the one workload a strict list is good at. Property testing
wants the first `k`. A strict `List` must build the whole enumeration first; a lazy one need not; levels
need only the levels that hold the first `k`. -/

open SameDisciplineConcat Ladder in
def firstOf (args : List String) : IO Unit := do
  let goal := type.Fun .Nat .Nat
  let z ← IO.rand 0 0
  let rung := (args.headD "")
  let s := ((args.drop 1).head?.bind String.toNat?).getD 9 + z
  let k := ((args.drop 2).head?.bind String.toNat?).getD 100
  let n ← match rung with
    | "L0" => pure ((derivedAt [] goal s).take k).length
    | "L1" => pure (((l1A 10000 s s [] goal) s).take k).length
    | "L2" => pure (((l2A 10000 s [] goal) s).take k).length
    | "L3" => pure ((l3A s [] goal).take k).length
    | "L4" => pure ((l4A s [] goal).take k).length
    | "L5" => pure (firstK k s (lvA [] goal))
    | "all4" => pure (l4A s [] goal).length
    | "all5" => pure (levelsUpTo [] goal s).length
    | _ => pure 0
  -- Peak resident memory, read from the kernel rather than inferred.
  let hwm := (← IO.FS.readFile "/proc/self/status").splitOn "\n"
    |>.find? (·.startsWith "VmHWM") |>.getD "VmHWM: ?"
  IO.println s!"{rung} budget {s}: got {n}   {hwm.trimAscii}"

def main (args : List String) : IO Unit :=
  if args.headD "" == "ladder" then ladder (args.drop 1) else firstOf args
