import Specimen.Enum.Fail
import Specimen.Enum.ExceptT
import Specimen.Enum.Finite
import Specimen.Enum.Weighted
import Specimen.Enum.Backtrack
import Specimen.Enum.Pick
import Specimen.Enum.Search
import Specimen.Enum.BacktrackWith
import Specimen.Enum.Graded
import Specimen.Enum.GradedWith

/-!
# Enumeration as an interpretation of a generator

Readings of a generator written once over Basalt's `Gen`, and the choice and failure classes derived
code needs, hosted here until Basalt has a stable API for them:

* `Fail` and `FailWith`: a refutation, and a failure that says why (`Specimen.Enum.Fail`); `ExceptT ε G`
  carries the labels (`Specimen.Enum.ExceptT`).
* `Backtrack` and `Pick`: a weighted choice among branches with and without retry, the search at a
  sampler and the union at an enumeration (`Specimen.Enum.Backtrack`, `Specimen.Enum.Pick`,
  `Specimen.Enum.BacktrackWith` over labels).
* `Finite`: every value, one entry per path, with counts by arithmetic (`Specimen.Enum.Finite`);
  `WFinite`, the same with each path's probability (`Specimen.Enum.Weighted`); `CostGraded`, tiered by
  the number of choices (`Specimen.Enum.Graded`, `Specimen.Enum.GradedWith`).

Their laws, which need Mathlib, are in `Specimen.Enum.Laws`.
-/
