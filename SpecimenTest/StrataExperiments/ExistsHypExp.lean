import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: an existential buried inside a hypothesis, like Strata's
    `AnnotCompat aliases ann xty := ∃ σ, AliasEquiv aliases (subst σ ann) xty`.
    This is the one shape I'm unsure Specimen can handle as a side-condition. -/

open Plausible

set_option guard_msgs.diff true

def related (a b k : Nat) : Bool := a + k == b

-- `Compat a b := ∃ k, related a b k`  (existential side condition)
def Compat (a b : Nat) : Prop := ∃ k, related a b k = true

inductive WantsCompat : Nat → Nat → Prop where
  | mk : ∀ a b, Compat a b → WantsCompat a b

-- Generate `b` given `a` such that `Compat a b` (i.e. ∃ k, a + k = b).
derive_generator (fun (a : Nat) => ∃ (b : Nat), WantsCompat a b)
