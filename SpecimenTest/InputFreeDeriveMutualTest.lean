import Specimen

/-!
# Regression: `derive_mutual` on relations with **no inputs**

`derive_mutual` has two weight-emission paths. The primary one goes through
`compileWeightedProducer`; a second is taken when the target relation has no lambda-bound inputs, so
every argument is an output. The second path has to pass the weight function the same arguments as the
first, down to their types: a `Float` where the per-mille `scoreBadness` parameter expects a `Nat` fails
every such derive with `failed to synthesize OfScientific Nat`.

Nothing else in the suite reaches it, since `derive_generator` uses a different path and every other
`derive_mutual` call site passes a relation that *has* inputs (`lookup Γ x τ`, `typing Γ e τ`,
`BST lo hi t`). The two shapes below are the minimum that pin the path down: one purely recursive, one
whose only constructor carries a side condition, so the schedule has to draw-and-check rather than
construct.
-/

open Plausible

/-- Purely recursive, no inputs: exercises the recursive-branch weight emission. -/
inductive InputFreeEven : Nat → Prop where
  | z  : InputFreeEven 0
  | ss : ∀ n, InputFreeEven n → InputFreeEven (n + 2)

/-- One constructor with a side condition: forces a draw-and-check schedule rather than a
    constructed output, which is the other shape this path has to handle. -/
inductive InputFreeIsFive : Nat → Prop where
  | mk : ∀ n, n = 5 → InputFreeIsFive n

#guard_msgs(drop info) in
derive_mutual generator (∃ n, InputFreeEven n)

#guard_msgs(drop info) in
derive_mutual generator (∃ n, InputFreeIsFive n)

-- The derived generators are not merely well-typed — they run and produce values satisfying their
-- relation. Only *properties* of the samples are pinned, never the samples themselves: sampling goes
-- through `ArbitrarySizedSuchThat`, whose instance differs flag-on vs flag-off, so pinning concrete
-- draws here would be a latent build break.
/-- info: even: nonempty=true allEven=true
five: allFive=true
-/
#guard_msgs in
#eval (do
  let evens ← Gen.sampleWithSeed 40
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => InputFreeEven n) 4) 6 20260910
  let fives ← Gen.sampleWithSeed 40
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => InputFreeIsFive n) 4) 6 20260910
  let evenOk := (evens.filterMap id).all (fun n => n % 2 == 0)
  let fiveOk := (fives.filterMap id).all (fun n => n == 5)
  IO.println s!"even: nonempty={!(evens.filterMap id).isEmpty} allEven={evenOk}"
  IO.println s!"five: allFive={fiveOk}"
  : IO Unit)
