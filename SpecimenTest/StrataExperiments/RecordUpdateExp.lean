import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import Plausible.Attr

open Plausible
set_option guard_msgs.diff true

/-! Experiment: record-update syntax `{ Γ with types := ... }` in a recursive
    hypothesis, as in Strata's `tabs`:
      HasType C { Γ with types := Γ.types.insert x.fst x_ty } (varOpen 0 x e) e_ty
    The claim in LExprGen.lean was that this appears only in an INPUT position of
    the recursive call (needs constructing, not inverting) and should work. Test. -/

structure Ctx where
  vals : List Nat
  deriving Repr, BEq

-- A relation that, in its recursive constructor, extends the context with a
-- record-update before recursing. `n` counts how deep we've extended.
inductive Stk : Ctx → Nat → Prop where
  | base : ∀ Γ, Stk Γ 0
  | push : ∀ Γ n,
      Stk { Γ with vals := 0 :: Γ.vals } n →
      Stk Γ (n + 1)

set_option specimen.autoDeriveDeps true in
derive_generator (fun (Γ : Ctx) => ∃ (n : Nat), Stk Γ n)
