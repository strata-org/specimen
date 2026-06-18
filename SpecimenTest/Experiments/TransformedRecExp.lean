import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import Plausible.Attr

/-! Experiment: the genuinely-novel part of Strata's `tabs`/`tquant`:
    a recursive hypothesis applied to a *transformed* output
    (`HasType ... (varOpen 0 x e) ...`) rather than to the sub-term `e` directly. -/

open Plausible

set_option guard_msgs.diff true

/-! ### Experiment 5a: recursive call on a function-application of the output.

    `Good (f e)` in the hypothesis, where `e` is what we recurse to build,
    and `f` transforms it. In Strata: `HasType C Γ' (varOpen 0 x e) e_ty`.
    We model `f` as an arbitrary structural transform. -/

inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
  deriving Repr, BEq

def wrap (t : Tree) : Tree := .node t .leaf

deriving instance Arbitrary for Tree

-- `Good` over trees; the recursive constructor recurses on `wrap inner`.
inductive Good : Tree → Prop where
  | gleaf : Good .leaf
  | gwrap : ∀ inner, Good (wrap inner) → Good (.node (wrap inner) .leaf)

-- Hand-written decision procedure for `Good` (the auto-derived checker hits an
-- unrelated bug), so we can supply the `DecOpt` instance the generator needs.
def decGood : Tree → Bool
  | .leaf => true
  | .node (.node t .leaf) .leaf => decGood (wrap t)  -- matches `node (wrap inner) leaf`
  | _ => false

instance : DecOpt (Good t) where
  decOpt := fun _ => .ok (decGood t)

derive_generator (fun _u : Unit => ∃ (t : Tree), Good t)

-- Sample to confirm the generator actually produces values.
#eval! show IO Unit from do
  let mut i := 0
  while i < 5 do
    let s ← (Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => Good t) 4) 4)
    IO.println (repr s)
    i := i + 1
