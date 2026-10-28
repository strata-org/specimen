import Specimen.DecOpt
import Specimen.Enumerators
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import Specimen.DeriveChecker
import Specimen.BasaltClasses
import Specimen.Enum.BacktrackWith
import SpecimenTest.CommonDefinitions.STLCDefinitions
import Bench.StlcLevels

open StlcLevels

/-!
# The derived enumerator against the same enumerator run at Basalt's `Finite`

`typE` is STLC `typing`'s enumerator written the way an emitter targeting Basalt would write it:
polymorphic in its monad, one `Specimen.Backtrack` branch per constructor, `Fail` where a constructor
does not apply, and the derived enumerator's own budget rule (leaves at every budget, `Abs` at
`s - 1`, `Add`/`App` both at `(s - 1) / 2`). Run at `Finite`, where `backtrack` is the union, it
enumerates exactly the derived enumerator's set at each budget, checked below before anything is timed,
so only the machinery differs. `ExceptT Exhaustion Finite` is timed too, the monad an emitted
enumerator with labelled failures runs at.

Run with `lake exe bench-enum-interp [fun] BUDGET…` (see `bench/README.md`).
-/

/-! ## The restricted leaf universe, as in the other benchmarks — must precede `derive_mutual` -/

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

namespace EnumInterp

open Basalt Specimen

/-- The derived enumerator's set at budget `s`, errors dropped. -/
def derivedAt (Γ : List type) (τ : type) (s : Nat) : LazyList term :=
  ((EnumSizedSuchThat.enumSizedST (fun e => typing Γ e τ) s) s).filter (·.toOption.isSome)
    |>.mapLazyList fun r => match r with | .ok e => e | .error _ => .Const 0

variable {G : Type → Type} [Monad G] [RandomChoice G] [Fail G] [Specimen.Backtrack G]

/-- `typing`'s enumerator over any monad that can fail and backtrack, under the derived rule. -/
def typE : Nat → List type → type → G term
  | s, Γ, τ =>
    let leaves : List (Nat × (Unit → G term)) :=
      [(1, fun _ => match τ with
          | .Nat => term.Const <$> pickFrom natLeaves
          | _ => Fail.fail),
       (1, fun _ => pickFrom (varsAt Γ τ))]
    match s with
    | 0 => Backtrack.backtrack leaves
    | s' + 1 => Backtrack.backtrack (leaves ++
      [(1, fun _ => match τ with
          | .Fun τ1 τ2 => term.Abs τ1 <$> typE s' (τ1 :: Γ) τ2
          | .Nat => Fail.fail),
       (1, fun _ => match τ with
          | .Nat => do
            let a ← typE (s' / 2) Γ .Nat
            let b ← typE (s' / 2) Γ .Nat
            pure (term.Add a b)
          | _ => Fail.fail),
       (1, fun _ => do
          let τ1 ← pickFrom tyLeaves
          let e1 ← typE (s' / 2) Γ (.Fun τ1 τ)
          let e2 ← typE (s' / 2) Γ τ1
          pure (term.App e1 e2))])
termination_by s => s
decreasing_by all_goals omega

/-- `typE` with every `<$>` written as a `bind`, as `ExceptT`'s `map` is. -/
def typEb : Nat → List type → type → G term
  | s, Γ, τ =>
    let leaves : List (Nat × (Unit → G term)) :=
      [(1, fun _ => match τ with
          | .Nat => do let n ← pickFrom natLeaves; pure (term.Const n)
          | _ => Fail.fail),
       (1, fun _ => pickFrom (varsAt Γ τ))]
    match s with
    | 0 => Backtrack.backtrack leaves
    | s' + 1 => Backtrack.backtrack (leaves ++
      [(1, fun _ => match τ with
          | .Fun τ1 τ2 => do let e ← typEb s' (τ1 :: Γ) τ2; pure (term.Abs τ1 e)
          | .Nat => Fail.fail),
       (1, fun _ => match τ with
          | .Nat => do
            let a ← typEb (s' / 2) Γ .Nat
            let b ← typEb (s' / 2) Γ .Nat
            pure (term.Add a b)
          | _ => Fail.fail),
       (1, fun _ => do
          let τ1 ← pickFrom tyLeaves
          let e1 ← typEb (s' / 2) Γ (.Fun τ1 τ)
          let e2 ← typEb (s' / 2) Γ τ1
          pure (term.App e1 e2))])
termination_by s => s
decreasing_by all_goals omega

/-! ### Candidate interpretations, local to this benchmark -/

/-- `Finite` with `bind` flattening into a balanced union tree, so an index costs `O(log n)` unions
rather than walking a right-nested chain of `n`. -/
def FB (α : Type) : Type := Specimen.Finite α

partial def balancedFlatten : List (Specimen.Finite α) → Specimen.Finite α
  | [] => Specimen.Finite.empty
  | [x] => x
  | xs =>
    let k := xs.length / 2
    Specimen.Finite.union (balancedFlatten (xs.take k)) (balancedFlatten (xs.drop k))

instance : Monad FB where
  pure a := Specimen.Finite.singleton a
  bind x f := match (x : Specimen.Finite _) with
    | .undef => .undef
    | .mk _ idx => balancedFlatten (List.ofFn fun i => (f (idx i) : Specimen.Finite _))
  map f x := Specimen.Finite.map f (x : Specimen.Finite _)
instance : RandomChoice FB := ⟨fun lo hi h => (RandomChoice.choose lo hi h : Specimen.Finite _)⟩
instance : Fail FB := ⟨fun {α} => (Specimen.Finite.empty : Specimen.Finite α)⟩
instance : Specimen.Backtrack FB where
  backtrack gs := balancedFlatten (gs.filterMap fun p => if p.1 = 0 then none else some (p.2 () : Specimen.Finite _))

/-- A plain list of entries: `bind` is `flatMap`, `backtrack` concatenation. -/
def ListE (α : Type) : Type := List α
instance : Monad ListE where
  pure a := [a]
  bind x f := List.flatMap (fun a => (f a : List _)) (x : List _)
  map f x := List.map f (x : List _)
instance : RandomChoice ListE := ⟨fun lo hi h =>
  ((List.range (hi - lo + 1)).attach.map fun ⟨i, hi'⟩ =>
    ULift.up ⟨lo + i, by simp only [List.mem_range] at hi'; omega⟩ : List _)⟩
instance : Fail ListE := ⟨fun {α} => ([] : List α)⟩
instance : Specimen.Backtrack ListE where
  backtrack gs := (gs.filter (·.1 ≠ 0)).flatMap fun p => (p.2 () : List _)

/-- The terms at `Finite`, all of them. -/
def finiteAll (Γ : List type) (τ : type) (s : Nat) : List term :=
  ((typE (G := Finite) s Γ τ).toList?).getD []

/-- The terms at `ExceptT Exhaustion Finite`, successes only. -/
def finiteExAll (Γ : List type) (τ : type) (s : Nat) : List term :=
  (((typE (G := ExceptT Specimen.Exhaustion Finite) s Γ τ).run.toList?).getD []).filterMap
    (·.toOption)

/-- The first `k` terms at `Finite`, by index: FEAT's indexing, no value visited before its turn. -/
def finiteFirstK (Γ : List type) (τ : type) (s k : Nat) : List term :=
  let x := typE (G := Finite) s Γ τ
  (List.range (min k ((x.card?).getD 0))).filterMap x.get?

end EnumInterp

-- `typE` at `Finite` is exactly the derived set, with no duplicates, at every budget checked.
open EnumInterp in
#guard [type.Nat, .Fun .Nat .Nat].all fun τ =>
  (List.range 8).all fun s => sameSet (derivedAt [] τ s).toList (finiteAll [] τ s)

open EnumInterp in
#guard [type.Nat, .Fun .Nat .Nat].all fun τ =>
  (List.range 6).all fun s => sameSet (finiteAll [] τ s) (finiteExAll [] τ s)

namespace EnumInterp

def timeIt (act : Unit → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0) / 1000000)

/-- Levels upward, stopping once `k` terms are in hand. -/
partial def levelsFirstK (k s : Nat) (lvl : Nat → List term) (n acc : Nat := 0) : Nat :=
  if n > s || acc ≥ k then acc else levelsFirstK k s lvl (n + 1) (acc + (lvl n).length)

end EnumInterp

open EnumInterp in
def main (args : List String) : IO Unit := do
  let goal := if args.head? == some "fun" then type.Fun .Nat .Nat else type.Nat
  let z ← IO.rand 0 0   -- runtime value, so nothing is evaluated at elaboration
  IO.println s!"goal {repr goal}"
  for s0 in (args.drop 1).filterMap String.toNat? do
    let s := s0 + z
    let (d, td) ← timeIt fun _ => (derivedAt [] goal s).length
    let (f, tf) ← timeIt fun _ => (finiteAll [] goal s).length
    let (fe, tfe) ← timeIt fun _ => (finiteExAll [] goal s).length
    let (fb, tfb) ← timeIt fun _ => (((typEb (G := Specimen.Finite) s [] goal).toList?).getD []).length
    IO.println s!"  budget {s} all:     Finite, maps as binds {fb} in {tfb}ms"
    let (bb, tbb) ← timeIt fun _ => ((((typEb (G := FB) s [] goal) : Specimen.Finite _).toList?).getD []).length
    let (lb, tlb) ← timeIt fun _ => (((typEb (G := ListE) s [] goal) : List _)).length
    IO.println s!"  budget {s} all:     balanced Finite, maps as binds {bb} in {tbb}ms | list {lb} in {tlb}ms"
    let (l, tl) ← timeIt fun _ => (levelsUpTo [] goal s).length
    IO.println s!"  budget {s} all:     derived {d} in {td}ms | Finite {f} in {tf}ms | ExceptT Finite {fe} in {tfe}ms | levels {l} in {tl}ms"
    let (_, kd) ← timeIt fun _ => ((derivedAt [] goal s).take 1000).length
    let (_, kf) ← timeIt fun _ => (finiteFirstK [] goal s 1000).length
    let (_, kl) ← timeIt fun _ => levelsFirstK 1000 s (lvA [] goal)
    IO.println s!"  budget {s} first 1000: derived {kd}ms | Finite (indexed) {kf}ms | levels {kl}ms"
