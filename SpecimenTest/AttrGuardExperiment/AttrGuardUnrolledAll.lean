import SpecimenTest.AttrGuardExperiment.AttrGuardBaseline

open Plausible

namespace AttrGuard

/-!
# Guarded-dereference experiment — MECHANICAL ALL-COMBINATIONS INLINING

`AttrGuardFused` hardcoded the cooperating pair (`drf k (chk (sq k) e)`). This
variant tests whether the pairing is *discovered* mechanically by inlining the
`drf` node over the constructors of the relations its premise depends on.

Note the key wrinkle vs. the vault: `drf`'s cross-node link is a **membership**
`sq k ∈ g'`, not an equality. Inlining `drf` over the inner expression's `WT`
rule alone is *not enough* — it leaves `sq k ∈ c :: g0` as a residual membership
premise, which the scheduler can only guess-and-check (~never hits). So inlining
must **compose across relations**: we also inline the membership `∈` via its two
`List.Mem` constructors. That yields the combinations below (inner `WT` rule ×
membership constructor):

  * `drf` over `lit`, `sq k ∈ g` (inner `lit` leaves guards `= g`): from an empty
    start `g = []`, impossible; never fires from `[]`.
  * `drf` over `chk`, **head** (`sq k = c`): substituting `c := sq k` gives
    `drf k (chk (sq k) e0)` — the forward-functional case, `sq k` computed from a
    fresh `k`. This is the pairing `AttrGuardFused` hardcoded, now *discovered*.
  * `drf` over `chk`, **tail** (`sq k ∈ g0`): needs the guard already deeper — a
    pre-existing guard, rarely available from `[]`.
  * `drf` over `drf`, needing `sq k ∈ g0`: likewise needs a pre-existing guard.

No static pruning happens: `derive_mutual` emits code for all constructors, and
infeasible instantiations fail at generation time and backtrack. Counts fluctuate
run to run (`Gen.run` uses IO randomness).
-/

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

inductive WT3 : Guards → Expr → Guards → Prop where
| TLit : ∀ g n,
    WT3 g (Expr.lit n) g
| TChk : ∀ g c e g',
    WT3 g e g' →
    WT3 g (Expr.chk c e) (c :: g')
-- drf over lit, membership in `g` (only tail form possible; `lit` yields `g`).
| DrfLit : ∀ g k n,
    sq k ∈ g →
    WT3 g (Expr.drf k (Expr.lit n)) g
-- drf over chk, membership HEAD: sq k = c, so substitute c := sq k. Fully
-- forward-functional — `sq k` computed from a fresh `k`, no residual membership.
| DrfChkHead : ∀ g k e0 g0,
    WT3 g e0 g0 →
    WT3 g (Expr.drf k (Expr.chk (sq k) e0)) (sq k :: g0)
-- drf over chk, membership TAIL: sq k ∈ g0 (guard established deeper).
| DrfChkTail : ∀ g k c e0 g0,
    WT3 g e0 g0 →
    sq k ∈ g0 →
    WT3 g (Expr.drf k (Expr.chk c e0)) (c :: g0)
-- drf over drf, needing sq k ∈ g0 (inner drf leaves guards = g0).
| DrfDrf : ∀ g k k0 e0 g0,
    WT3 g (Expr.drf k0 e0) g0 →
    sq k ∈ g0 →
    WT3 g (Expr.drf k (Expr.drf k0 e0)) g0

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun g => ∃ e g', WT3 g e g')

def countDerefs3 (numTraces : Nat := 1000) : IO (Nat × Nat) := do
  let mut exprsWithDrf := 0
  let mut totalDrf := 0
  for i in List.range numTraces do
    let (e, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, g') => WT3 [] e g') 10) (i + 5)
    let d := countDrf e
    totalDrf := totalDrf + d
    if d > 0 then exprsWithDrf := exprsWithDrf + 1
  return (exprsWithDrf, totalDrf)

#eval do
  let (withDrf, total) ← countDerefs3 1000
  IO.println s!"[all-combos] expressions containing >=1 drf: {withDrf} / 1000"
  IO.println s!"[all-combos] total drf nodes generated: {total}"

def sampleValidDerefs3 (numTraces : Nat := 30) : IO Unit := do
  for i in List.range numTraces do
    let (e, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, g') => WT3 [] e g') 10) (i + 5)
    if countDrf e > 0 then
      IO.println s!"{repr e}"

#eval sampleValidDerefs3 30

end AttrGuard
