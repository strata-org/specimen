import Specimen
import Specimen.Basalt
import Specimen.Correctness.CompleteOf

namespace Specimen.Correctness.CompleteOfTest
open Basalt Specimen.Correctness

inductive Tree where
  | leaf
  | node (l r : Tree)

inductive WT : Tree → Prop where
  | leaf : WT .leaf
  | node : ∀ l r, WT l → WT r → WT (.node l r)

namespace Div
set_option specimen.emitBasalt true in
set_option specimen.richOutput false in
scoped derive_mutual generator (∃ t, WT t)
end Div

namespace Split
set_option specimen.emitBasalt true in
set_option specimen.sizeSplit true in
set_option specimen.richOutput false in
scoped derive_mutual generator (∃ t, WT t)
end Split

#specimen_complete [Div.specimen_gen_Specimen_Correctness_CompleteOfTest_WT_0__Specimen_Correctness_CompleteOfTest_Specimen_Correctness_CompleteOfTest_Div for WT outputs [0]]
#specimen_complete [Split.specimen_gen_Specimen_Correctness_CompleteOfTest_WT_0__Specimen_Correctness_CompleteOfTest_Specimen_Correctness_CompleteOfTest_Split for WT outputs [0]]
#check @Split.specimen_gen_Specimen_Correctness_CompleteOfTest_WT_0__Specimen_Correctness_CompleteOfTest_Specimen_Correctness_CompleteOfTest_Split.complete
#print axioms Split.specimen_gen_Specimen_Correctness_CompleteOfTest_WT_0__Specimen_Correctness_CompleteOfTest_Specimen_Correctness_CompleteOfTest_Split.complete

end Specimen.Correctness.CompleteOfTest
