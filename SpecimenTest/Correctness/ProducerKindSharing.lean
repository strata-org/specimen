import Specimen.Correctness.GenInterpSPMF
import Basalt.Enumeration

/-!
# `Producer` is shared across kinds, and the kinds stay distinct

Generators and enumerators are the same structure — `m (Outcome α)` — over different carriers, so
`Producer` is stated once and indexed by a phantom `ProducerKind`. This file pins the two properties
that arrangement exists to provide, because both are easy to lose silently in a refactor.

**Sharing.** Everything depending only on `Monad` — the `Outcome` algebra and the whole fuel-iteration
interpreter with its soundness, completeness and monotonicity theorems — is `{k}`-polymorphic. The
`example`s below apply the *generator* leg's theorems verbatim to an `enum`-kind step. If someone
re-pins those statements to `.gen`, these stop compiling.

**Distinctness.** The kind index is phantom, so it would be tempting to drop it and discriminate by
capability class instead (`Gen` for random choice, `Choice` for union). That fails exactly where it
matters: nothing stops a carrier from having both instances — public Basalt gives `SPMF` only
`RandomChoice`, so the enum step below *assumes* `[Choice SPMF]`, which is all it takes for a
wrong-leg combinator to resolve happily under the capability-class design. The final `#guard_msgs`
pins that `backtrack` at the `enum` kind is a **type** error even then. It also pins the error text,
which is the fragile part — if `Producer`'s elaboration changes, expect to update the expected
message rather than the claim.
-/

open Basalt Specimen.Correctness

section
variable [Choice SPMF]

/-- An `enum`-kind step: alternatives are *unioned*, not sampled. Note this uses
`Enumeration.enumerate`, which requires `[Choice m]` — `backtrack` would be a type error here. -/
noncomputable def evenEnumStep : SProducerStep .enum Unit Nat :=
  fun prev sz _ =>
    Enumeration.enumerate
      [ pure 0,
        (do let n ← prev (sz - 1) (); pure (n + 2)) ]

def evenSpec : Unit → Nat → Prop := fun _ n => n % 2 = 0

-- The generator leg's theorems, applied verbatim at the enumerator kind.
example (h : StepGenSoundB evenEnumStep evenSpec) :
    ∀ x, semGenRelB evenEnumStep () x → evenSpec () x :=
  genRelB_sound h ()

example {φ σ} (h : StepGenCompleteB evenEnumStep evenSpec φ σ) (n : Nat) (hn : evenSpec () n) :
    Produces (genRelB evenEnumStep (φ () n + 1) (σ () n) ()) n :=
  genRelB_complete' h () n hn

example (h : StepGenMono evenEnumStep) :
    ∀ f f', f ≤ f' → ∀ sz i x,
      Produces (genRelB evenEnumStep f sz i) x → Produces (genRelB evenEnumStep f' sz i) x :=
  genRelB_fuel_mono h

-- And the `.gen`-only combinator is rejected at the `enum` kind, as intended.
/-- error: Application type mismatch: The argument
  gs
has type
  List (ℕ × (Unit → SProducer ProducerKind.enum ℕ))
but is expected to have type
  List (ℕ × (Unit → BacktrackGen ?m.1 ?m.3))
in the application
  BacktrackGen.backtrack gs
-/
#guard_msgs in
example (gs : List (Nat × (Unit → SProducer .enum Nat))) : SProducer .enum Nat :=
  BacktrackGen.backtrack gs

end
