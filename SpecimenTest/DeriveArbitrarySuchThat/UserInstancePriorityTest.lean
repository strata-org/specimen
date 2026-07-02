/-
  Test that autoDeriveDeps finds pre-existing ArbitrarySizedSuchThat instances
  for multi-output dependencies. When a dep has ≥2 outputs, the generated code
  projects results out of a Prod — using mkAppM ``Prod.fst for this projection
  triggers a universe-unification failure that makes instanceExists return false,
  causing the system to re-derive a rejection sampler that shadows the user instance.
-/
import Specimen.DeriveConstrainedProducer
import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat

open Plausible

inductive Sums : Nat → Nat → Nat → Prop where
  | mk : a + b = n → Sums a b n

/-- Hand-written instance: pick a ∈ [0,10], return (a, 10-a). -/
instance : ArbitrarySizedSuchThat (Nat × Nat) (fun (a, b) => Sums a b n) where
  arbitrarySizedST _ := do
    let a ← Gen.choose Nat 0 n (by omega)
    pure (a.1, n - a.1)

structure NatPair where
  x : Nat
  y : Nat
  deriving Repr, Inhabited

inductive HasSum10 : NatPair → Prop where
  | mk : Sums x y 10 → HasSum10 ⟨x, y⟩

#guard_msgs(drop info) in
set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
derive_mutual (∃ (self : _), HasSum10 self)

def testUserInstancePriority : IO Unit := do
  let g := @ArbitrarySizedSuchThat.arbitrarySizedST NatPair (fun self => HasSum10 self) _ 10
  let mut ok := (0 : Nat)
  let mut fuel := (0 : Nat)
  let mut i := (0 : Nat)
  while i < 100 do
    try
      let s ← Gen.run g (10 + i)
      if s.x + s.y == 10 then ok := ok + 1
    catch _ => fuel := fuel + 1
    i := i + 1
  if ok != 100 || fuel != 0 then
    throw <| IO.userError s!"UserInstancePriority: valid={ok}/100 fuelOut={fuel}/100"

#eval testUserInstancePriority
