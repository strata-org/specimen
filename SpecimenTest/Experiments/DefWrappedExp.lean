import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

open Plausible
set_option guard_msgs.diff true

/-! Strata's `tabs` uses `LExpr.fresh x e`, which is a `def : Prop := x ∉ freeVars e`,
    NOT an inlined `∉`. Does the def wrapper matter? -/

def myFreeVars (l : List Nat) : List Nat := l
def freshDef (x : Nat) (l : List Nat) : Prop := x ∉ myFreeVars l   -- def-wrapped, Prop

inductive WantsFreshDef : List Nat → Nat → Prop where
  | mk : ∀ l x, freshDef x l → WantsFreshDef l x

-- Does Specimen unfold `freshDef`, or demand an instance for it?
derive_generator (fun (l : List Nat) => ∃ (x : Nat), WantsFreshDef l x)
