import Specimen.Enum.Laws.Backtrack
import Specimen.Enum.Laws.BacktrackCost
import Specimen.Enum.Laws.BacktrackWeight
import Specimen.Enum.Laws.BacktrackWith
import Specimen.Enum.Laws.BacktrackWithCost
import Specimen.Enum.Laws.BacktrackWithWeight
import Specimen.Enum.Laws.Search
import Specimen.Enum.Laws.Basic
import Specimen.Enum.Laws.Cost
import Specimen.Enum.Laws.Fail
import Specimen.Enum.Laws.GenRel
import Specimen.Enum.Laws.Weight
import Specimen.Enum.WeightedBacktrack
import Specimen.Enum.WeightedBacktrackWith

/-!
# The laws of `Specimen.Enum`'s readings

Each reading's run is related to the generator's `SPMF` meaning by a `GenRel`, so `walk` (or
`walk fixpoint`) proves the relation per generator: the enumeration is the support (`Basic`), the
weights are the probabilities (`Weight`), the cost tiers are `SPMF.Cost`'s support (`Cost`), and, for a
generator that fails and backtracks, the same at `OptionT SPMF` and `ExceptT ε (OptionT SPMF)` (`Fail`,
`Backtrack*`). A search's answers are related to the enumeration's entries the same way (`Search`).
They need Mathlib, so they build from the proofs root, not with `Specimen`.
-/
