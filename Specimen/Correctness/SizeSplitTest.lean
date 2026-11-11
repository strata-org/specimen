import Specimen
import Specimen.Basalt
import Specimen.Correctness.SoundOf

/-! `specimen.sizeSplit`: a rule with two recursive calls draws how to split its size. -/

namespace Specimen.Correctness.SizeSplitTest

inductive Tree where
  | leaf
  | node (l r : Tree)
  deriving Repr

inductive WT : Tree → Prop where
  | leaf : WT .leaf
  | node : ∀ l r, WT l → WT r → WT (.node l r)

set_option specimen.emitBasalt true in
set_option specimen.emitSound true in
set_option specimen.sizeSplit true in
set_option specimen.richOutput false in
derive_mutual
  generator (∃ t, WT t)

#print axioms specimen_gen_Specimen_Correctness_SizeSplitTest_WT_0__Specimen_Correctness_SizeSplitTest_Specimen_Correctness_SizeSplitTest.sound

end Specimen.Correctness.SizeSplitTest

open Specimen.Correctness.SizeSplitTest in
#print specimen_gen_Specimen_Correctness_SizeSplitTest_WT_0__Specimen_Correctness_SizeSplitTest_Specimen_Correctness_SizeSplitTest
