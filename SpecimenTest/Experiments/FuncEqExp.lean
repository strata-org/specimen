import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: can Specimen derive generators for relations whose hypotheses
    are function-call equalities or boolean-valued function applications?

    We want to test the user's hypothesis that Specimen *can* handle these,
    but does so inefficiently (generate-and-check). -/

open Plausible

set_option guard_msgs.diff true

/-! ### Experiment 1: a Bool-valued function applied to a generated output.

    `isSmall n = true` where `isSmall` is a Bool function. This mirrors
    `LTy.isMonoType x_ty = true` from Strata's `tabs`. -/

def isSmall (n : Nat) : Bool := n < 3

inductive WantsSmall : Nat → Prop where
  | mk : ∀ n, isSmall n = true → WantsSmall n

-- Can we generate an `n` with `WantsSmall n`?
-- The hypothesis `isSmall n = true` constrains the *output* `n`.
derive_generator (fun _u : Unit => ∃ (n : Nat), WantsSmall n)


/-! ### Experiment 2: a Bool-valued function used directly (no `= true`). -/

inductive WantsSmall2 : Nat → Prop where
  | mk : ∀ n, isSmall n → WantsSmall2 n

derive_generator (fun _u : Unit => ∃ (n : Nat), WantsSmall2 n)


/-! ### Experiment 3: container membership as a hypothesis.
    This mirrors `Γ.types.find? x = some ty` from Strata's `tvar`:
    we have a fixed list/container and want to produce an element/key from it. -/

def lookupNat (l : List (Nat × Nat)) (k : Nat) : Option Nat := l.lookup k

inductive InMap : List (Nat × Nat) → Nat → Nat → Prop where
  | mk : ∀ l k v, lookupNat l k = some v → InMap l k v

-- Given a fixed map `l`, generate a key `k` and value `v` that are in it.
derive_generator (fun (l : List (Nat × Nat)) => ∃ (k : Nat) (v : Nat), InMap l k v)
