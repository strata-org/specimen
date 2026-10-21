import Specimen
import Specimen.Basalt

/-!
# Under `specimen.emitBasalt`, a dependency needs a `BacktrackGenFor`

A derived generator calls its sub-producers through `BacktrackGenFor` when Basalt emission is on. A
dependency that has only a hand-written Plausible `ArbitrarySizedSuchThat` instance therefore cannot
serve that call. The deriver derives the dependency instead, and warns which hand-written instance it
bypassed; a dependency with a `BacktrackGenFor` instance is used as is.
-/

open Plausible

set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true

namespace BasaltDependencyLookupTest

inductive Op where | o0 | o1 | o2
  deriving Repr, DecidableEq, Inhabited

instance : Arbitrary Op where
  arbitrary := do
    let n ← Plausible.Gen.choose Nat 0 2 (by omega)
    pure (#[Op.o0, Op.o1, Op.o2].getD n.1 Op.o0)

deriving instance Basalt.ArbitrarySized for Op

inductive Differ : Op → Op → Prop where
  | mk : a ≠ b → Differ a b

/-- A hand-written Plausible producer only, with no `BacktrackGenFor` counterpart. -/
instance : ArbitrarySizedSuchThat (Op × Op) (fun (a, b) => Differ a b) where
  arbitrarySizedST _ := pure (.o1, .o2)

inductive Pair : Op × Op → Prop where
  | mk : Differ a b → Pair (a, b)

/-- warning: BasaltDependencyLookupTest.Differ has an `ArbitrarySizedSuchThat` instance but no
`BacktrackGenFor` instance, which generators derived under `specimen.emitBasalt` call. Deriving one
instead; to keep the hand-written generator, give it a `BacktrackGenFor` counterpart. -/
#guard_msgs(warning, drop info, whitespace := lax) in
derive_mutual (∃ p, Pair p)

example : BacktrackGenFor (Op × Op) (fun (a, b) => Differ a b) := inferInstance

/-- With a `BacktrackGenFor` counterpart the dependency is used as is, and nothing is reported. -/
inductive Same : Op → Op → Prop where
  | mk : Same a a

instance : BacktrackGenFor (Op × Op) (fun (a, b) => Same a b) where
  gen _ _ := pure (.o0, .o0)

inductive SamePair : Op × Op → Prop where
  | mk : Same a b → SamePair (a, b)

#guard_msgs(warning, drop info) in
derive_mutual (∃ p, SamePair p)

end BasaltDependencyLookupTest
