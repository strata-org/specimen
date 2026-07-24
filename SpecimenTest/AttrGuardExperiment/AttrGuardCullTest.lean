import SpecimenTest.AttrGuardExperiment.AttrGuardBaseline

open Plausible

namespace AttrGuardCull

/-!
# Test: culling on the guarded-dereference all-combinations relation

`WT`'s inlined all-combinations rules are all individually satisfiable (each
`sq k ∈ …` premise can hold from *some* guard set), so the "never satisfiable"
cull must drop **nothing** here — a good check that the pass is not over-eager.
We include one deliberately-dead constructor (`DeadHead`, whose premises force
`0 = 1`) to confirm the pass still fires when a genuine contradiction exists.
-/

open AttrGuard (Expr Guards sq countDrf)

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

inductive WTc : Guards → Expr → Guards → Prop where
| TLit : ∀ g n, WTc g (Expr.lit n) g
| TChk : ∀ g c e g', WTc g e g' → WTc g (Expr.chk c e) (c :: g')
| DrfChkHead : ∀ g k e0 g0,
    WTc g e0 g0 →
    WTc g (Expr.drf k (Expr.chk (sq k) e0)) (sq k :: g0)
-- Genuinely dead: premises force 0 = 1, unsatisfiable regardless of state.
| DeadHead : ∀ g k e0 g0 (h : (0 : Nat) = 1),
    WTc g e0 g0 →
    WTc g (Expr.drf k e0) g0

set_option specimen.cullDeadCtors true

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun g => ∃ e g', WTc g e g')

-- Culling is a pure optimization: generation must still produce valid derefs.
def countDerefs (numTraces : Nat := 1000) : IO Nat := do
  let mut withDrf := 0
  for i in List.range numTraces do
    let (e, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, g') => WTc [] e g') 10) (i + 5)
    if countDrf e > 0 then withDrf := withDrf + 1
  return withDrf

#eval do
  let withDrf ← countDerefs 1000
  IO.println s!"[cull-on] exprs w/ >=1 drf: {withDrf} / 1000"

end AttrGuardCull
