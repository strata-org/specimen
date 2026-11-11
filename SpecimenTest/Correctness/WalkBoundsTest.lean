import Specimen.Correctness.MeanWalk

/-! `tot_walk`, `sok_walk` and `mean_walk` on small generators. -/

open Basalt Specimen.Correctness

/-- A draw and a map lose no mass. -/
example : Tot (do let i ← chooseNat 0 3 (by omega); pure (i + 1) : SGen Nat) := by
  tot_walk []

/-- …and succeed surely. -/
example : sok (do let i ← chooseNat 0 3 (by omega); pure (i + 1) : SGen Nat) = 1 := by
  sok_walk []

/-- A failure is total, though it never succeeds. -/
example : Tot (Specimen.Fail.fail : SGen Nat) := by
  tot_walk []

/-- A mean over a search's branches, each a `pure`: at most the largest. -/
example : MeanLe (Specimen.Backtrack.backtrack [(1, fun _ => pure 1), (2, fun _ => pure 2)] : SGen Nat)
    (fun n => n) 2 := by
  rw [← meanLeW_iff_meanLe]
  mean_walk []
  all_goals mean_close []
