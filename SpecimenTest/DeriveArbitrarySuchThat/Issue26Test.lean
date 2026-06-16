/-
  Regression test for issue #26:
  derive_mutual + autoDeriveDeps re-derives a joint-output dependency and
  ignores the user's ArbitrarySizedSuchThat (A × B) instance (runtime fuel-out).
-/
import Specimen.DeriveConstrainedProducer
import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat

open Plausible

inductive Op where | o0 | o1 | o2 | o3 | o4 | o5 | o6 | o7
  deriving Repr, DecidableEq, Inhabited

def Op.toU8 : Op → UInt8
  | .o0 => 0 | .o1 => 1 | .o2 => 2 | .o3 => 3
  | .o4 => 4 | .o5 => 5 | .o6 => 6 | .o7 => 7

instance : Arbitrary Op where
  arbitrary := do
    let n ← Plausible.Gen.choose Nat 0 7 (by omega)
    pure (#[Op.o0, Op.o1, Op.o2, Op.o3, Op.o4, Op.o5, Op.o6, Op.o7].getD n.1 Op.o0)

inductive HasValidReduceOp : Op → Op → Prop where
  | mk : a.toU8 ≠ 0 → b.toU8 ≠ 0 → a.toU8 ≠ b.toU8 → HasValidReduceOp a b

def validReduce (a b : Op) : Bool :=
  a.toU8 != 0 && b.toU8 != 0 && a.toU8 != b.toU8

/-- Hand-written product producer that enumerates valid pairs directly. -/
instance : ArbitrarySizedSuchThat (Op × Op) (fun (l, r) => HasValidReduceOp l r) where
  arbitrarySizedST _ := do
    let ops := #[Op.o1, Op.o2, Op.o3, Op.o4, Op.o5, Op.o6, Op.o7]
    let i ← Plausible.Gen.choose Nat 0 6 (by omega)
    let j ← Plausible.Gen.choose Nat 0 6 (by omega)
    let a := ops.getD i.1 Op.o1
    let b := ops.getD j.1 Op.o2
    let b := if a == b then ops.getD ((j.1 + 1) % 7) Op.o2 else b
    pure (a, b)

structure R2 where
  op0 : Op
  op1 : Op
  deriving Repr, Inhabited

inductive IsValidR2 : R2 → Prop where
  | mk : HasValidReduceOp op0 op1 → IsValidR2 ⟨op0, op1⟩

set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
derive_mutual (∃ (self : _), IsValidR2 self)

-- Verify the derived generator uses the hand-written instance (no fuel-out).
-- With the fix, the hand-written instance is used: 200/200 valid, 0 fuel-out.
-- Without the fix, the re-derived rejection sampler fuels out: 0/200 valid, 200 fuel-out.
def testIssue26 : IO Unit := do
  let g := @ArbitrarySizedSuchThat.arbitrarySizedST R2 (fun self => IsValidR2 self) _ 10
  let mut ok := (0 : Nat)
  let mut fuel := (0 : Nat)
  let mut i := (0 : Nat)
  while i < 200 do
    try
      let s ← Plausible.Gen.run g (10 + i)
      if validReduce s.op0 s.op1 then ok := ok + 1
    catch _ => fuel := fuel + 1
    i := i + 1
  if ok != 200 || fuel != 0 then
    throw <| IO.userError s!"Issue 26 regression: valid={ok}/200 fuelOut={fuel}/200"

#eval testIssue26
