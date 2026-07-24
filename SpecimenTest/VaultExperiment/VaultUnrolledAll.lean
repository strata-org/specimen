import SpecimenTest.VaultExperiment.VaultBaseline

open Plausible

namespace Vault

/-!
# Perfect-square vault — MECHANICAL ALL-COMBINATIONS INLINING

`VaultFused`'s `IssueRedeem` constructor hardcoded the `Issue`-then-`Redeem`
sequence. This variant tests whether the sequence can be *discovered* mechanically
instead — without telling the scheduler which commands to use.

A mechanical k=2 unroller that inlines the callee relation `VStep` cannot leave
the command choice as one free premise (a Lean constructor commits to one rule).
What it emits is one specialized constructor **per combination** of `VStep`'s
constructors — here 2×2 = 4: II, IR, RI, RR. Every 2-command sequence is thus
represented across the constructor set, and *which* sequence is viable is left
for the generator to work out. State bookkeeping is fully explicit (no pre-solved
`none`s): `DoIssue` requires input `= none` and outputs `some t`; `DoRedeem`
requires input `= some (sq k)` and outputs `none`.

From an empty start (`none`), only IR is realizable:
  * II: 2nd Issue needs input `= none`, but 1st Issue left `some t`. Internally
        inconsistent (`sa = some _` ∧ `sa = none`), regardless of start.
  * RR: likewise internally inconsistent.
  * RI: internally consistent, but its `s = some (sq k)` contradicts the `none`
        start (and every recursion point is `none`, since IR resets to `none`).
  * IR: Issue (`none`→`some t`), then Redeem needs `t = sq k`, then →`none`.

No static pruning happens: `derive_mutual` emits code for all four constructors.
The infeasible ones fail *at generation time* and provoke backtracking, so every
non-empty trace is a valid `Issue N; Redeem √N` chain. Counts fluctuate run to
run (`Gen.run` uses real IO randomness); the stable invariant is
non-empty ⟺ contains-Redeem.
-/

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

inductive VTrace2all : Vault → VTraceT → Vault → Prop where
| Nil : ∀ s, VTrace2all s [] s
-- II: DoIssue ; DoIssue
| II : ∀ (s sa sb : Vault) (t1 t2 : Nat) (s'' : Vault) (ps : VTraceT),
    s = none → sa = some t1 →
    sa = none → sb = some t2 →
    VTrace2all sb ps s'' →
    VTrace2all s ((VCmd.Issue t1, VResult.IssueOk) :: (VCmd.Issue t2, VResult.IssueOk) :: ps) s''
-- IR: DoIssue ; DoRedeem
| IR : ∀ (s sa sb : Vault) (t k : Nat) (s'' : Vault) (ps : VTraceT),
    s = none → sa = some t →
    sa = some (sq k) → sb = none →
    VTrace2all sb ps s'' →
    VTrace2all s ((VCmd.Issue t, VResult.IssueOk) :: (VCmd.Redeem k, VResult.RedeemOk) :: ps) s''
-- RI: DoRedeem ; DoIssue
| RI : ∀ (s sa sb : Vault) (k1 t2 : Nat) (s'' : Vault) (ps : VTraceT),
    s = some (sq k1) → sa = none →
    sa = none → sb = some t2 →
    VTrace2all sb ps s'' →
    VTrace2all s ((VCmd.Redeem k1, VResult.RedeemOk) :: (VCmd.Issue t2, VResult.IssueOk) :: ps) s''
-- RR: DoRedeem ; DoRedeem
| RR : ∀ (s sa sb : Vault) (k1 k2 : Nat) (s'' : Vault) (ps : VTraceT),
    s = some (sq k1) → sa = none →
    sa = some (sq k2) → sb = none →
    VTrace2all sb ps s'' →
    VTrace2all s ((VCmd.Redeem k1, VResult.RedeemOk) :: (VCmd.Redeem k2, VResult.RedeemOk) :: ps) s''

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun i => ∃ t s, VTrace2all i t s)

def countRedeemsAll (numTraces : Nat := 1000) : IO (Nat × Nat × Nat) := do
  let mut tracesWithRedeem := 0
  let mut totalRedeems := 0
  let mut totalIssues := 0
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VTrace2all none t s) 10) (i + 5)
    let redeems := trace.foldl (fun acc (_, r) =>
      match r with
      | .RedeemOk => acc + 1
      | _ => acc) 0
    let issues := trace.foldl (fun acc (_, r) =>
      match r with
      | .IssueOk => acc + 1
      | _ => acc) 0
    totalRedeems := totalRedeems + redeems
    totalIssues := totalIssues + issues
    if redeems > 0 then
      tracesWithRedeem := tracesWithRedeem + 1
  return (tracesWithRedeem, totalRedeems, totalIssues)

#eval do
  let (withRedeem, totalR, totalI) ← countRedeemsAll 1000
  IO.println s!"[all-combos inlined] traces w/ >=1 Redeem: {withRedeem} / 1000"
  IO.println s!"[all-combos inlined] total Redeem: {totalR}, total Issue: {totalI}"

-- Diagnostic: is the 188/1000 explained by empty traces (immediate Nil)?
-- Since from a `none` start only IR is a viable step (II/RR internally
-- inconsistent; RI needs a `some` start, and the state is `none` at every
-- recursion point), *every* non-empty trace must contain a Redeem. So we expect
-- nonEmpty == tracesWithRedeem, and the rest are empty (chose Nil first).
def traceStatsAll (numTraces : Nat := 1000) : IO Unit := do
  let mut nonEmpty := 0
  let mut withRedeem := 0
  let mut nonEmptyNoRedeem := 0
  let mut maxLen := 0
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VTrace2all none t s) 10) (i + 5)
    let redeems := trace.foldl (fun acc (_, r) =>
      match r with | .RedeemOk => acc + 1 | _ => acc) 0
    if trace.length > 0 then nonEmpty := nonEmpty + 1
    if redeems > 0 then withRedeem := withRedeem + 1
    if trace.length > 0 && redeems == 0 then nonEmptyNoRedeem := nonEmptyNoRedeem + 1
    if trace.length > maxLen then maxLen := trace.length
  IO.println s!"non-empty traces: {nonEmpty} / {numTraces}"
  IO.println s!"traces with >=1 Redeem: {withRedeem} / {numTraces}"
  IO.println s!"non-empty traces with 0 Redeems: {nonEmptyNoRedeem} (expect 0)"
  IO.println s!"max trace length: {maxLen}"

#eval traceStatsAll 1000

-- Show a few traces to confirm which combinations actually survive.
def sampleAll (numTraces : Nat := 25) : IO Unit := do
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VTrace2all none t s) 10) (i + 5)
    if !trace.isEmpty then
      IO.println s!"{repr trace}"

#eval sampleAll 25

end Vault
