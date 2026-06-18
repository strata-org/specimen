import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: is a freshness / non-membership side-condition really a
    different kind of issue from a Bool-valued function side-condition like
    `isMonoType`?  Strata's `LExpr.fresh x e` is defined as `x ∉ freeVars e`. -/

open Plausible

set_option guard_msgs.diff true

/-! ### Experiment 4a: non-membership as `∉` (a Prop, like `LExpr.fresh`). -/

inductive WantsFresh : List Nat → Nat → Prop where
  | mk : ∀ l x, x ∉ l → WantsFresh l x

derive_generator (fun (l : List Nat) => ∃ (x : Nat), WantsFresh l x)


/-! ### Experiment 4b: the exact shape of `LExpr.fresh` — a Bool-valued
    helper that computes a list and checks (non-)membership. -/

def myFreeVars (l : List Nat) : List Nat := l   -- stand-in for `freeVars e`
def isFresh (x : Nat) (l : List Nat) : Bool := x ∉ (myFreeVars l)

inductive WantsFresh2 : List Nat → Nat → Prop where
  | mk : ∀ l x, isFresh x l = true → WantsFresh2 l x

derive_generator (fun (l : List Nat) => ∃ (x : Nat), WantsFresh2 l x)
