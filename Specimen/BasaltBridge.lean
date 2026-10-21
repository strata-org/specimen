import Basalt.Arbitrary
import Basalt.PlausibleBridge
import Specimen.ArbitrarySizedSuchThat

/-!
# Running Basalt-derived generators through Specimen's Plausible machinery

Under `specimen.emitBasalt`, a derived generator is a `BacktrackGenFor` instance whose body is
polymorphic in Basalt's `Gen`. Everything in Specimen that consumes generators — the `specimen` and
`specimen_test` tactics, `Plausible.Testable`, `ArbitrarySizedSuchThat.printSamples`, and every
derived generator emitted *without* the flag — looks up `ArbitrarySizedSuchThat` instead. This
module connects the two with one blanket instance, plus the equality leaves the Basalt path needs.

Import it through `Specimen.Basalt`.
-/

open Plausible

/-- A Basalt-derived generator runs as an `ArbitrarySizedSuchThat` by instantiating its generator monad
at `Plausible.Gen` and turning its `Outcome` into Plausible's errors (`BacktrackGen.toPlausibleGen`).

`priority := low`, so a hand-written or Plausible-path `ArbitrarySizedSuchThat` for the same relation
still wins; this only fills in where none exists.

The conversion squeezes `Outcome`'s refuted/exhausted distinction into a thrown `GenError`, which
Specimen recovers from the message (`Gen.GenError.isInconclusive` treats Plausible's out-of-fuel
error as inconclusive). Inside the Basalt path the distinction is in the type; it becomes a string
only here, at the boundary. -/
instance (priority := low) {α : Type} {P : α → Prop} [BacktrackGenFor α P] :
    ArbitrarySizedSuchThat α P where
  arbitrarySizedST size :=
    BacktrackGen.toPlausibleGen (BacktrackGenFor.gen (P := P) (G := Plausible.Gen) size)

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

/-- A pair constrained to be equal: generate one value and duplicate it. The counterpart of Specimen's
`ArbitrarySizedSuchThat (α × α) (fun (l, r) => l = r)`. -/
instance instBacktrackGenForEqPair {α : Type} [Basalt.Arbitrary α] :
    BacktrackGenFor (α × α) (fun (l, r) => l = r) where
  gen _ := do
    let a ← BacktrackGen.liftGen Basalt.Arbitrary.arbitrary
    pure (a, a)
