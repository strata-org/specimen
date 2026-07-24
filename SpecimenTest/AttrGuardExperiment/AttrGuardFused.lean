import SpecimenTest.AttrGuardExperiment.AttrGuardBaseline

open Plausible

namespace AttrGuard

/-!
# Guarded-dereference experiment — FUSED (1-step lookahead)

We reuse the `WT` machine but derive a generator for a *fused* typing relation
`WT2`, whose `DrfChk` constructor inlines the two nodes that must cooperate: a
`chk (sq k)` establishing a guard, immediately dereferenced by `drf k`.

`DrfChk` brings the check code `sq k`, the dereference root `k`, and the guard
`sq k ∈ (sq k :: g')` into a single constructor scope. The scheduler can bind a
fresh `k`, compute the check code `sq k` forward, and the membership is then
immediate (`sq k` is the head of the guard set) — instead of committing arbitrary
check codes and later failing to invert `sq`.

Prediction: `drf` now appears reliably, in contrast to the baseline's ~0 / 1000.
-/

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

inductive WT2 : Guards → Expr → Guards → Prop where
| TLit : ∀ g n,
    WT2 g (Expr.lit n) g
| TChk : ∀ g c e g',
    WT2 g e g' →
    WT2 g (Expr.chk c e) (c :: g')
| TDrf : ∀ g k e g',
    WT2 g e g' →
    sq k ∈ g' →
    WT2 g (Expr.drf k e) g'
-- Fused: drf k (chk (sq k) e). The check code and the deref root are the same
-- `k`, brought into one scope, so `sq k` is computed forward and the membership
-- `sq k ∈ sq k :: g'` holds by construction.
| DrfChk : ∀ g k e g',
    WT2 g e g' →
    WT2 g (Expr.drf k (Expr.chk (sq k) e)) (sq k :: g')

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun g => ∃ e g', WT2 g e g')

def countDerefs2 (numTraces : Nat := 1000) : IO (Nat × Nat) := do
  let mut exprsWithDrf := 0
  let mut totalDrf := 0
  for i in List.range numTraces do
    let (e, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, g') => WT2 [] e g') 10) (i + 5)
    let d := countDrf e
    totalDrf := totalDrf + d
    if d > 0 then exprsWithDrf := exprsWithDrf + 1
  return (exprsWithDrf, totalDrf)

#eval do
  let (withDrf, total) ← countDerefs2 1000
  IO.println s!"[fused] expressions containing >=1 drf: {withDrf} / 1000"
  IO.println s!"[fused] total drf nodes generated: {total}"

-- Confirm the generated derefs are genuinely well-guarded (each `drf k` sits
-- over a `chk (sq k)`), rather than junk.
def sampleValidDerefs (numTraces : Nat := 30) : IO Unit := do
  for i in List.range numTraces do
    let (e, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, g') => WT2 [] e g') 10) (i + 5)
    if countDrf e > 0 then
      IO.println s!"{repr e}"

#eval sampleValidDerefs 30

end AttrGuard
