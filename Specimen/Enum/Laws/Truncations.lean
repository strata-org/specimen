/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Laws.BacktrackWithCost
public import Specimen.Enum.Laws.BacktrackWithWeight
public import Specimen.Enum.Laws.Search

/-!
# `truncations` under the labelled readings

A derived generator's `size = 0` pool runs its recursive rules' truncations as one branch,
`truncations`, which fails with their labels joined. Under each reading with labels it is what the
sampler's is: by cases on the joined label, a refutation or that label's failure on both sides.
-/

@[expose] public section

namespace Specimen

variable {ε α : Type} [Max ε] (ls : List (ExceptT ε (OptionT Id) α))

@[gen_rule]
theorem EnumeratesWith.truncations [Preorder ε] :
    EnumeratesWith (Specimen.truncations ls : ExceptT ε Finite α)
      (Specimen.truncations ls : ExceptT ε (OptionT SPMF) α) := by
  unfold Specimen.truncations
  cases joinLabels ls with
  | none => exact EnumeratesWith.fail
  | some e => exact EnumeratesWith.failWith e

@[gen_rule]
theorem WeighsWith.truncations :
    WeighsWith (Specimen.truncations ls : ExceptT ε WFinite α)
      (Specimen.truncations ls : ExceptT ε (OptionT SPMF) α) := by
  unfold Specimen.truncations
  cases joinLabels ls with
  | none => exact WeighsWith.fail
  | some e => exact WeighsWith.failWith e

@[gen_rule]
theorem CostEnumeratesWith.truncations [Preorder ε] :
    CostEnumeratesWith (Specimen.truncations ls : ExceptT ε (CostGraded Finite) α)
      (Specimen.truncations ls : ExceptT ε (OptionT SPMF.Cost) α) := by
  unfold Specimen.truncations
  cases joinLabels ls with
  | none => exact CostEnumeratesWith.fail
  | some e => exact CostEnumeratesWith.failWith e

@[gen_rule]
theorem SearchesAs.truncations :
    SearchesAs (Specimen.truncations ls : ExceptT ε Finite α) (Specimen.truncations ls : Search α) := by
  unfold Specimen.truncations
  cases joinLabels ls with
  | none => exact SearchesAs.fail
  | some e => exact SearchesAs.failWith e

end Specimen
