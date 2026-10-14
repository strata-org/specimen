import Specimen.GeneratorCombinators

/-!
# Seeded generator runs are reproducible

`Gen.runWithSeed` and `Gen.sampleWithSeed` exist so a statistical test is a regression test rather than a
coin flip. Pinned: the same seed gives the same samples, and one seeded stream gives varied draws — the
property a loop of per-iteration seeds lacks (`mkStdGen` on consecutive seeds correlates the first draw).
-/

open Plausible

private def draws (seed : Nat) : IO (List Nat) := do
  let xs ← Gen.sampleWithSeed 20 (fun _ => (Subtype.val <$> Gen.choose Nat 0 100 (by omega) : Gen Nat)) 10 seed
  return xs.toList.filterMap id

-- Same seed, same samples.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do return (← draws 42) == (← draws 42)

-- One stream, varied draws: more than a handful of distinct values among 20.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do return decide ((← draws 42).eraseDups.length > 10)

-- `runWithSeed` is reproducible too.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let g : Gen Nat := Subtype.val <$> Gen.choose Nat 0 1000000 (by omega)
  return (← Gen.runWithSeed g 10 7) == (← Gen.runWithSeed g 10 7)
