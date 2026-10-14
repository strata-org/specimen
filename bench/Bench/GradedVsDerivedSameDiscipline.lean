import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import Specimen.DeriveChecker
import SpecimenTest.CommonDefinitions.STLCDefinitions
import Bench.StlcLevels

open StlcLevels

/-!
# The derived enumerator vs levels, under the DERIVED enumerator's own budget rule

Comparing the derived enumerator with graded levels is only meaningful if both enumerate the same set at
each budget; with different budget rules the speed gap mixes the rule with the machinery. This file keeps
the derived enumerator exactly as emitted and builds *levels* that follow its rule, so only the machinery
differs.

## The derived enumerator, read off its emitted code (`#check @….eq_def`)

`Enumerator α := Nat → LazyList α`, "everything up to this budget", in one mode (the term, given `Γ τ`).
At budget `s`:

* leaves — `Const n` from `Enum Nat`, `Var x` from the `lookup` enumerator at the *undivided* `initSize` —
  at every budget, including 0;
* `Abs`: the body at `s - 1`, the annotation taken from the goal type;
* `Add`: both children at `(s - 1) / 2` — `Nat.div size' 2`, the even budget split;
* `App`: the argument type `τ1` from `Enum type`, then `e1 : τ1 → τ` and `e2 : τ1`, both at `(s - 1) / 2`.

If the deriver's schedule for `typing` changes, the levels below stop matching it; the `#guard`s that
compare the two sets then fail the build.

Each call returns everything that fits, so budgets are nested and every call re-enumerates the smaller ones.
Branches are concatenated in order by `enumerate`, a failed `match` appears inline as an `.error` entry, and
`bind` is `LazyList`'s round-robin.

## The same rule, as levels

A term's **level** is the smallest budget at which the derived enumerator produces it: leaves 0,
`Abs` `1 + body`, `Add`/`App` `1 + 2·max(children)`. Levels are then disjoint, so `⋃_{n ≤ s} level n` must
be *exactly* the derived set at budget `s` — checked below before anything is timed. Combining two
children is a **max** convolution, `x(m) × y(≤ m) ∪ x(< m) × y(m)`, not the sum `pair`: the derived rule
charges a binary node by its deeper child.

Not imported by the test suite: it re-derives under restricted leaf instances, which would leak. Compiled
by `lake build Bench`; run with `lake exe bench-same-discipline [fun] BUDGET…` (see `bench/README.md`).
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

set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

#guard_msgs(drop info) in
derive_mutual enumerator (fun Γ τ => ∃ (e : term), typing Γ e τ)


namespace SameDiscipline

/-- The derived enumerator's set at budget `s`, errors dropped. -/
def derivedAt (Γ : List type) (τ : type) (s : Nat) : LazyList term :=
  ((EnumSizedSuchThat.enumSizedST (fun e => typing Γ e τ) s) s).filter (·.toOption.isSome)
    |>.mapLazyList fun r => match r with | .ok e => e | .error _ => .Const 0


end SameDiscipline

-- The derived set and the levels agree at every budget checked, for both goal types, before anything is
-- timed.
open SameDiscipline in
#guard [type.Nat, .Fun .Nat .Nat].all fun τ =>
  (List.range 8).all fun s => sameSet (derivedAt [] τ s).toList (levelsUpTo [] τ s)

namespace SameDiscipline

def timeIt (act : Unit → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0) / 1000000)

/-- Levels upward, stopping once `k` terms are in hand (the `k` lowest-budget terms). -/
partial def firstK (k s : Nat) (lvl : Nat → List term) (n acc : Nat := 0) : Nat :=
  if n > s || acc ≥ k then acc else firstK k s lvl (n + 1) (acc + (lvl n).length)

end SameDiscipline

open SameDiscipline in
def main (args : List String) : IO Unit := do
  let goal := if args.head? == some "fun" then type.Fun .Nat .Nat else type.Nat
  let z ← IO.rand 0 0   -- runtime value, so nothing is evaluated at elaboration
  IO.println s!"goal {repr goal}"
  for s0 in (args.drop 1).filterMap String.toNat? do
    let s := s0 + z
    let (d, td) ← timeIt fun _ => (derivedAt [] goal s).length
    let (l, tl) ← timeIt fun _ => (levelsUpTo [] goal s).length
    let (d0, td0) ← timeIt fun _ =>
      (((EnumSizedSuchThat.enumSizedST (fun e => typing [] e goal) s) 0).filter (·.toOption.isSome)).length
    IO.println s!"  budget {s}: leaf budget 0 → terms {d0}, {td0}ms"
    let (_, fd) ← timeIt fun _ => ((derivedAt [] goal s).take 1000).length
    let (_, fl) ← timeIt fun _ => firstK 1000 s (lvA [] goal)
    IO.println s!"  budget {s}: terms {d}/{l}  all: derived {td}ms  levels {tl}ms  | first 1000: derived {fd}ms  levels {fl}ms"
