import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Regression test for `derive_generator` bug fixes. -/

-- reproduces issue 24

inductive ListConstr : List Nat → Prop where
| empty : ListConstr []
| cons₁ : ListConstr l → 2 ≤ x → ListConstr (x :: x :: l)
| cons₂ : ListConstr l → x < 2 → ListConstr (x :: l)

derive_generator (fun _ => ∃ (l : List Nat), ListConstr l)

-- reproduces issue 39

inductive Total {α} : α → Prop where
| any a : Total a

derive_generator ∃ a, Total a

inductive Bar where
| bar

-- reproduces issue 29

inductive Baz : Bar → Bar → Prop where
| isBar2 : Baz .bar .bar

derive_generator (fun b => ∃ a, Baz a b)
