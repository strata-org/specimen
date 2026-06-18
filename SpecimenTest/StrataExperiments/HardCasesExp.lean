import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: the cases I suspect are genuine *feasibility* blockers,
    not just efficiency problems. -/

open Plausible

set_option guard_msgs.diff true

/-! ### Experiment 6: a non-syntax-directed / subsumption-style rule.
    `tinst`/`tgen`/`talias` in Strata recurse on the SAME expression with no
    structural decrease and no shape constraint on the conclusion. Model: -/

inductive Ty where
  | base : Ty
  | arr : Ty → Ty → Ty
  deriving Repr, BEq

deriving instance Arbitrary for Ty

-- `HasT e τ`: constructor `inst` recurses on the same `e`, just changing the type.
inductive HasT : Nat → Ty → Prop where
  | lit  : ∀ n, HasT n .base
  | inst : ∀ e τ τ', HasT e τ → HasT e τ'   -- non-syntax-directed, no decrease

derive_generator (fun (τ : Ty) => ∃ (e : Nat), HasT e τ)


/-! ### Experiment 7: a disjunctive hypothesis (`∨`), like Strata's
    `o = none ∨ ∃ t, o = some t ∧ ...` in `tabs`. -/

inductive WantsDisj : Nat → Prop where
  | mk : ∀ n, (n = 0 ∨ n = 1) → WantsDisj n

derive_generator (fun _u : Unit => ∃ (n : Nat), WantsDisj n)
