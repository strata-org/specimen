import Specimen.Correctness.Semantics
import Specimen.GeneratorCombinators

/-!
# QuickChick-style support axioms for the real `Plausible.Gen`

Generator **completeness** — that a value is producible for *some* seed — is not provable about
Plausible's opaque `StdGen`: `split`/`next` expose no surjectivity, so the "bind support = union"
law has no proof there (a deterministic PRNG does not, in fact, cover the full product of outcomes).
Exactly as QuickChick builds into its `Gen` semantics, we therefore take the support laws as
**documented axioms**, justified by idealized RNG split-independence.

These are the *only* axioms in the correctness development; everything else is `[propext,
Classical.choice, Quot.sound]`.

**Read them as an idealization, not as facts about `StdGen`.** `genSupportAt` is defined concretely,
by running the generator from a seed, so if Plausible's PRNG fails to cover some product of outcomes
these axioms are false of it, and anything depending on them proves nothing about the code as it runs.
Only the `Ev` slice's generator theorems (`genEvG_sound`, `genEvG_complete` in `EvSlice`) use them;
`#print axioms` on any other result shows they are absent. The generator results that matter are
proved without them, at Basalt's `SPMF` (`GenInterpSPMF`, built from the `SpecimenTest.Proofs` root).
The `⊆`/soundness directions are in principle provable from the `Gen` monad definition — stating the full equations mirrors QuickChick's `semGenSize` lemmas and
keeps the generator proofs free of monad-transformer plumbing. `genSupportAt`/`genSupport` are the
real-`Gen` support predicates from `Semantics.lean`.
-/

open Plausible

namespace Specimen.Correctness

/-- Support of `pure` is a singleton. (Provable from `Gen.runPure`; kept with the support algebra.) -/
theorem genSupportAt_pure {α : Type} (a x : α) (sz : Nat) :
    genSupportAt (pure a) sz x ↔ x = a := by
  unfold genSupportAt
  have key : ∀ seed, Gen.runPure (pure a) seed sz = Except.ok a := fun _ => rfl
  constructor
  · rintro ⟨seed, h⟩; rw [key] at h; exact (Except.ok.inj h).symm
  · rintro rfl; exact ⟨mkStdGen 0, key _⟩

/-- **QuickChick bind support law** (`semBindSize`): the support of a monadic bind is the union of
    the continuation's supports over the first generator's support. Axiom (RNG split-independence). -/
axiom genSupportAt_bind {α β : Type} (m : Gen α) (k : α → Gen β) (sz : Nat) (x : β) :
    genSupportAt (m >>= k) sz x ↔ ∃ a, genSupportAt m sz a ∧ genSupportAt (k a) sz x

/-- **QuickChick backtrack support law**: for positively-weighted branches, `backtrack`'s support is
    the union of the branch supports (it tries each branch once, any can be chosen first). Axiom. -/
axiom genSupportAt_backtrack {α : Type} (gs : List (Nat × Gen α))
    (hpos : ∀ p ∈ gs, 0 < p.1) (sz : Nat) (x : α) :
    genSupportAt (GeneratorCombinators.backtrack gs) sz x ↔ ∃ p ∈ gs, genSupportAt p.2 sz x

end Specimen.Correctness
