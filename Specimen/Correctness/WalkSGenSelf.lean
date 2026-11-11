import Specimen.Correctness.WalkSGen

/-!
# A last-resort soundness leaf

Opt-in: a derived generator calls many sub-generators whose values its property does not depend on.
Without a fact about each, `walk` stops at the first. With this leaf it bounds an unknown generator by
asking for the postcondition everywhere, which a continuation that ignores the value meets trivially.
Imported only where wanted, since it turns a missing fact from an error into a goal.
-/

namespace Specimen.Correctness

@[obs_leaf self]
theorem le_always_self {α : Type} {x : SPMF α} {p : α → Prop} :
    (∀ a, p a) ≤ SPMF.alwaysObs.spec x p := fun h a _ => h a

end Specimen.Correctness
