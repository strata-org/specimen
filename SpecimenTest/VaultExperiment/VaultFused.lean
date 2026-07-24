import SpecimenTest.VaultExperiment.VaultBaseline

open Plausible

namespace Vault

/-!
# Perfect-square "ticket vault" experiment — FUSED (1-step lookahead)

We reuse the vault machine from `VaultBaseline` but derive a generator for a
*fused* trace relation `VTrace2`, whose `IssueRedeem` constructor inlines an
`Issue` immediately followed by a `Redeem`.

The point: `IssueRedeem` brings the issued ticket `t`, the redeemed root `k`,
and the linking equation `t = sq k` into a *single constructor scope*. Now the
scheduler can bind `k` (a fresh Nat) and *compute* `t = sq k` forward, instead
of committing an arbitrary `t` at `Issue` time and then failing to invert it.

The fusion adds no solver — it only widens the scheduler's premise-reordering
window so the free variable is bound from the forward-computable direction.

Prediction: `DoRedeem` now fires reliably (Redeem count >> 0), in contrast to
the baseline's 0 / 1000.
-/

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

inductive VTrace2 : Vault → VTraceT → Vault → Prop where
| Nil : ∀ s, VTrace2 s [] s
-- A lone single step, exactly as in the baseline `VTrace.Cons`.
| Step : ∀ s s' s'' c r ps,
    VStep s c r s' →
    VTrace2 s' ps s'' →
    VTrace2 s ((c, r) :: ps) s''
-- The fused pair: Issue t then Redeem k, with the cross-step equation `t = sq k`
-- inlined here so `t` and `k` share this constructor's scope.
| IssueRedeem : ∀ t k s'' ps,
    t = sq k →
    VTrace2 none ps s'' →
    VTrace2 none
      ((VCmd.Issue t, VResult.IssueOk) :: (VCmd.Redeem k, VResult.RedeemOk) :: ps) s''

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun i => ∃ t s, VTrace2 i t s)

def countRedeems2 (numTraces : Nat := 1000) : IO (Nat × Nat) := do
  let mut tracesWithRedeem := 0
  let mut totalRedeems := 0
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VTrace2 none t s) 10) (i + 5)
    let redeems := trace.foldl (fun acc (_, r) =>
      match r with
      | .RedeemOk => acc + 1
      | _ => acc) 0
    totalRedeems := totalRedeems + redeems
    if redeems > 0 then
      tracesWithRedeem := tracesWithRedeem + 1
  return (tracesWithRedeem, totalRedeems)

#eval do
  let (withRedeem, total) ← countRedeems2 1000
  IO.println s!"[fused] traces containing >=1 Redeem: {withRedeem} / 1000"
  IO.println s!"[fused] total Redeem operations generated: {total}"

-- Confirm the redeemed tickets are genuinely well-formed perfect squares, i.e.
-- the generator is producing *valid* IssueRedeem pairs rather than junk.
def sampleValidRedeems (numTraces : Nat := 20) : IO Unit := do
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VTrace2 none t s) 10) (i + 5)
    if trace.any (fun (_, r) => r == VResult.RedeemOk) then
      IO.println s!"{repr trace}"

#eval sampleValidRedeems 20

end Vault
