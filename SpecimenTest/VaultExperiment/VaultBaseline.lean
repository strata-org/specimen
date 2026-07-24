import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators

open Plausible

namespace Vault

/-!
# Perfect-square "ticket vault" experiment — BASELINE (0-step lookahead)

A deliberately tiny state machine that captures the multi-step-constraint
challenge without any of KVStore's incidental complexity.

The vault is either empty or holding a single ticket `t`. You may:
  * `Issue t` into an empty vault (any `t`), landing in `some t`;
  * `Redeem k` a held ticket, but ONLY by presenting a root `k` such that the
    held ticket `t = sq k` (i.e. the ticket is the perfect square `k*k`).

The `DoRedeem` precondition `t = sq k` is the crux:
  * It is imposed *retroactively* — nothing at `Issue` time forces `t` to be a
    perfect square, so a 0-lookahead forward generator picks `t` blind.
  * It cannot be satisfied by reading the store — the vault holds `t`, but the
    root `k = √t` must be *synthesized*, and Specimen can only guess-and-check
    `k` against `t = sq k`, which for an arbitrary committed `t` essentially
    never hits.

So we predict: a derived forward generator started from `none` will fire
`DoIssue` freely but almost never fire `DoRedeem`, because by the time it needs
a root the ticket is already an arbitrary (non-square) number.
-/

abbrev Vault := Option Nat

inductive VCmd where
| Issue (t : Nat)
| Redeem (k : Nat)
deriving Repr, DecidableEq

inductive VResult where
| IssueOk
| RedeemOk
deriving Repr, DecidableEq

abbrev VTraceT := List (VCmd × VResult)

def sq (k : Nat) : Nat := k * k

-- Single-step semantics: the labeled edges of the machine.
inductive VStep : Vault → VCmd → VResult → Vault → Prop where
| DoIssue : ∀ t,
    VStep none (VCmd.Issue t) VResult.IssueOk (some t)
| DoRedeem : ∀ t k,
    t = sq k →
    VStep (some t) (VCmd.Redeem k) VResult.RedeemOk none

-- Multi-step traces.
inductive VTrace : Vault → VTraceT → Vault → Prop where
| Nil : ∀ s, VTrace s [] s
| Cons : ∀ s s' s'' c r ps,
    VStep s c r s' →
    VTrace s' ps s'' →
    VTrace s ((c, r) :: ps) s''

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

-- Hand-written generator for the perfect-square property, since Specimen
-- cannot invert `sq`. Its synthesizer should pick this up wherever it needs to
-- produce a value related by `sq`.
instance : ArbitrarySizedSuchThat Nat (fun t => ∃ k, t = sq k) where
  arbitrarySizedST size := do
    let k ← Gen.choose Nat 0 size (by omega)
    return sq k

-- An unconstrained `Arbitrary VCmd`, mirroring the BoundedBuffer setup.
deriving instance Arbitrary for VCmd

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun i => ∃ t s, VTrace i t s)

-- Sample forward traces from the empty vault and measure how often the derived
-- generator manages to fire `DoRedeem`.
def countRedeems (numTraces : Nat := 1000) : IO (Nat × Nat) := do
  let mut tracesWithRedeem := 0
  let mut totalRedeems := 0
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VTrace none t s) 10) (i + 5)
    let redeems := trace.foldl (fun acc (_, r) =>
      match r with
      | .RedeemOk => acc + 1
      | _ => acc) 0
    totalRedeems := totalRedeems + redeems
    if redeems > 0 then
      tracesWithRedeem := tracesWithRedeem + 1
  return (tracesWithRedeem, totalRedeems)

#eval do
  let (withRedeem, total) ← countRedeems 1000
  IO.println s!"traces containing >=1 Redeem: {withRedeem} / 1000"
  IO.println s!"total Redeem operations generated: {total}"

-- Sanity check that the generator is actually exercising the machine (firing
-- Issue and producing non-trivial traces), so the Redeem=0 result above is
-- "never fires Redeem" and not "never generates anything".
def traceStats (numTraces : Nat := 1000) : IO Unit := do
  let mut totalIssues := 0
  let mut totalLen := 0
  let mut maxLen := 0
  let mut nonEmpty := 0
  for i in List.range numTraces do
    let (trace, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (t, s) => VTrace none t s) 10) (i + 5)
    let issues := trace.foldl (fun acc (_, r) =>
      match r with
      | .IssueOk => acc + 1
      | _ => acc) 0
    totalIssues := totalIssues + issues
    totalLen := totalLen + trace.length
    if trace.length > maxLen then maxLen := trace.length
    if trace.length > 0 then nonEmpty := nonEmpty + 1
  IO.println s!"non-empty traces: {nonEmpty} / {numTraces}"
  IO.println s!"total Issue operations: {totalIssues}"
  IO.println s!"total trace length: {totalLen}, max length: {maxLen}"

#eval traceStats 1000

end Vault
