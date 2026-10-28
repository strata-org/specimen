import Specimen.Enum.BacktrackWith
import Basalt.OptionT
import Basalt.PlausibleGen
import Plausible.Arbitrary
import Plausible.ArbitraryFueled
import Specimen.ArbitrarySizedSuchThat
import Specimen.Enumerators
import Specimen.GeneratorCombinators
import Specimen.BasaltClasses

/-!
# Running Basalt-derived generators through Specimen's Plausible machinery

Under `specimen.emitBasalt`, a derived generator is a `BacktrackGenFor` instance whose body is
polymorphic in its generator monad. Everything in Specimen that consumes generators — the `specimen` and
`specimen_test` tactics, `Plausible.Testable`, `ArbitrarySizedSuchThat.printSamples`, and every
derived generator emitted *without* the flag — looks up `ArbitrarySizedSuchThat` instead. This
module connects the two with one blanket instance, plus the equality leaves the Basalt path needs.

Import it through `Specimen.Basalt`.
-/

open Plausible

namespace Specimen

/-- The monad a Basalt-derived generator runs at under Plausible: a refutation is `none`, a failure
that is not one is a labelled `.error`, and `Specimen.Backtrack` retries past both. -/
abbrev BasaltSampler := ExceptT Exhaustion (OptionT Plausible.Gen)

/-- Run at `Plausible.Gen`, throwing `Gen.genericFailure` for a refutation and `Gen.outOfFuel` for a
labelled failure, so a caller that classifies Plausible's errors can still tell them apart. -/
def BasaltSampler.toPlausibleGen (x : BasaltSampler α) : Plausible.Gen α := do
  match ← x.run.run with
  | some (.ok a) => pure a
  | none => throw Plausible.Gen.genericFailure
  | some (.error _) => throw Plausible.Gen.outOfFuel

end Specimen

/-- A Basalt-derived generator runs as an `ArbitrarySizedSuchThat` by instantiating its generator monad
at `Specimen.BasaltSampler` and turning its failures into Plausible's errors.

`priority := low`, so a hand-written or Plausible-path `ArbitrarySizedSuchThat` for the same relation
still wins; this only fills in where none exists.

The conversion squeezes the refuted/exhausted distinction into a thrown `GenError`, which Specimen
recovers from the message (`Gen.GenError.isInconclusive` treats Plausible's out-of-fuel error as
inconclusive). Inside the Basalt path the distinction is in the type; it becomes a string only here, at
the boundary. -/
instance (priority := low) {α : Type} {P : α → Prop} [BacktrackGenFor α P] :
    ArbitrarySizedSuchThat α P where
  arbitrarySizedST size :=
    (BacktrackGenFor.gen (P := P) (G := Specimen.BasaltSampler) size).toPlausibleGen

/-- A Basalt unconstrained generator is a Plausible one at `Plausible.Gen`. Low priority, so a native
Plausible instance keeps winning and an existing test's distribution is unchanged. -/
instance (priority := low) [Basalt.Arbitrary α] : Plausible.Arbitrary α where
  arbitrary := Basalt.Arbitrary.arbitrary (G := Plausible.Gen)

/-- Plausible's own `ArbitraryFueled → Arbitrary` instance then takes the fuel from its size. -/
instance (priority := low) [Basalt.ArbitraryFueled α] : Plausible.ArbitraryFueled α where
  arbitraryFueled n := Basalt.ArbitraryFueled.arbitraryFueled (G := Plausible.Gen) n

/-- A Basalt-derived enumerator's run at `ExceptT Exhaustion Finite`, as the lazy list Specimen's
enumerator consumers read: each success, and each label as `Gen.outOfFuelError`, which a checker reads
as inconclusive. An undefined run (infinite, which a derived enumerator over `EnumFueled` leaves is not)
is one inconclusive entry. -/
def Specimen.toEnumeratorEntries (x : Specimen.Finite (Except Specimen.Exhaustion α)) :
    LazyList (Except GenError α) :=
  match x.toList? with
  | none => LazyList.fromList [.error Gen.outOfFuelError]
  | some l => LazyList.fromList (l.map fun
      | .ok a => .ok a
      | .error _ => .error Gen.outOfFuelError)

/-- A Basalt-derived enumerator runs as an `EnumSizedSuchThat`, read at `ExceptT Exhaustion Finite`:
everything up to the size, by its law exactly what the enumerator can succeed with. A derived
checker's premise is enumerated this way, at the checker's budget. Low priority, as above. -/
instance (priority := low) {α : Type} {P : α → Prop} [EnumFor α P] : EnumSizedSuchThat α P where
  enumSizedST size := fun _ =>
    Specimen.toEnumeratorEntries
      (EnumFor.enum (P := P) (G := ExceptT Specimen.Exhaustion Specimen.Finite) size).run

/-- A Basalt unconstrained enumeration is one of Specimen's, read at `Finite`: the values up to the
size. A derived checker draws an unconstrained value this way. Low priority, as above. -/
instance (priority := low) [Specimen.EnumFueled α] : Enum α where
  enum size := LazyList.fromList
    ((Specimen.EnumFueled.enumFueled (G := Specimen.Finite) size).toList?.getD [])

/-! ## Leaf instances for equality constraints

Derived schedules bottom out in premises `x = e` (or `e = x`) whenever an output is determined by
unification rather than generated. Specimen supplies these for `ArbitrarySizedSuchThat`; the Basalt
path needs the same, or any relation with a determined output fails to resolve a sub-producer. -/

/-- An output determined by a right-hand equality is produced directly. Named, so a proof about a
derived generator that delegated to it can unfold it. -/
instance instBacktrackGenForEqRight {α : Type} {val : α} : BacktrackGenFor α (fun x => x = val) where
  gen _ := pure val

/-- As above, for `val = x`. Both orientations occur: the deriver does not normalise the direction of
an equality premise. -/
instance instBacktrackGenForEqLeft {α : Type} {val : α} : BacktrackGenFor α (fun x => val = x) where
  gen _ := pure val

instance instEnumForEqRight {α : Type} {val : α} : EnumFor α (fun x => x = val) where
  enum _ := pure val

instance instEnumForEqLeft {α : Type} {val : α} : EnumFor α (fun x => val = x) where
  enum _ := pure val

/-- A pair constrained to be equal: generate one value and duplicate it. The counterpart of Specimen's
`ArbitrarySizedSuchThat (α × α) (fun (l, r) => l = r)`. -/
instance instBacktrackGenForEqPair {α : Type} [Basalt.Arbitrary α] :
    BacktrackGenFor (α × α) (fun (l, r) => l = r) where
  gen _ := do
    let a ← Basalt.Arbitrary.arbitrary
    pure (a, a)

instance instEnumForEqPair {α : Type} [Specimen.EnumFueled α] :
    EnumFor (α × α) (fun (l, r) => l = r) where
  enum n := do
    let a ← Specimen.EnumFueled.enumFueled n
    pure (a, a)
