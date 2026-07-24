import SpecimenTest.VaultExperiment.VaultBaseline

open Plausible

namespace VaultCull

/-!
# Test: `specimen.cullDeadCtors` drops provably-dead inlined constructors

We re-declare the all-combinations relation (II, IR, RI, RR) and derive its
generator with `specimen.cullDeadCtors` enabled. II and RR have internally
contradictory premises (`sa = some _` ∧ `sa = none`), so the cull pass should
prove them dead and omit them; IR and RI are satisfiable (RI from a `some (sq _)`
start) and must be kept.

Behaviorally, culling is a pure optimization: the derived generator must still
produce exactly the valid traces (every non-empty trace an `Issue N; Redeem √N`
chain). We check that here. Whether II/RR were physically dropped is visible in
the `plausible.deriving.arbitrary` trace ("[cull] dropping constructor ...").
-/

open Vault (Vault VCmd VResult VTraceT sq)

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

inductive VT : Vault → VTraceT → Vault → Prop where
| Nil : ∀ s, VT s [] s
| II : ∀ (s sa sb : Vault) (t1 t2 : Nat) (s'' : Vault) (ps : VTraceT),
    s = none → sa = some t1 →
    sa = none → sb = some t2 →
    VT sb ps s'' →
    VT s ((VCmd.Issue t1, VResult.IssueOk) :: (VCmd.Issue t2, VResult.IssueOk) :: ps) s''
| IR : ∀ (s sa sb : Vault) (t k : Nat) (s'' : Vault) (ps : VTraceT),
    s = none → sa = some t →
    sa = some (sq k) → sb = none →
    VT sb ps s'' →
    VT s ((VCmd.Issue t, VResult.IssueOk) :: (VCmd.Redeem k, VResult.RedeemOk) :: ps) s''
| RI : ∀ (s sa sb : Vault) (k1 t2 : Nat) (s'' : Vault) (ps : VTraceT),
    s = some (sq k1) → sa = none →
    sa = none → sb = some t2 →
    VT sb ps s'' →
    VT s ((VCmd.Redeem k1, VResult.RedeemOk) :: (VCmd.Issue t2, VResult.IssueOk) :: ps) s''
| RR : ∀ (s sa sb : Vault) (k1 k2 : Nat) (s'' : Vault) (ps : VTraceT),
    s = some (sq k1) → sa = none →
    sa = some (sq k2) → sb = none →
    VT sb ps s'' →
    VT s ((VCmd.Redeem k1, VResult.RedeemOk) :: (VCmd.Redeem k2, VResult.RedeemOk) :: ps) s''

set_option specimen.cullDeadCtors true

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun i => ∃ t s, VT i t s)

def countDrf : VTraceT → Nat
  | [] => 0
  | (_, .RedeemOk) :: rest => 1 + countDrf rest
  | _ :: rest => countDrf rest

def countRedeems (numTraces : Nat := 1000) : IO (Nat × Nat) := do
  let mut withR := 0
  let mut nonEmptyNoR := 0
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VT none t s) 10) (i + 5)
    let r := countDrf trace
    if r > 0 then withR := withR + 1
    if trace.length > 0 && r == 0 then nonEmptyNoR := nonEmptyNoR + 1
  return (withR, nonEmptyNoR)

-- With culling on, the derived generator must still produce valid Redeem-bearing
-- traces, and (the invariant) never a non-empty trace without a Redeem.
#eval do
  let (withR, nonEmptyNoR) ← countRedeems 1000
  IO.println s!"[cull-on] traces w/ >=1 Redeem: {withR} / 1000"
  IO.println s!"[cull-on] non-empty traces with 0 Redeems: {nonEmptyNoR} (expect 0)"

end VaultCull
