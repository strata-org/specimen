import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators

open Plausible

namespace AttrGuard

/-!
# Guarded-dereference experiment — BASELINE (0-step lookahead)

A Cedar-shaped analog of the vault experiment. Where the vault was a *flat*
command trace (a Step/Trace pair), this is a **single self-recursive typing
relation over an expression tree**, threading a "guard set" state through
subexpression outputs — the structure of Cedar's `HasType`, which threads a
`PathSet` from an expression into its subexpressions (`TCondTrue`, `THasAttr`, …).

The language:
  * `lit n`      — a literal; leaves the guard set unchanged.
  * `chk c e`    — a "has-attribute" check: records guard code `c`, so its output
                   guard set is `c :: (guards of e)`.
  * `drf k e`    — a "dereference": legal ONLY if the guard code `sq k` is already
                   present in `e`'s output guard set. You must present a root `k`
                   whose square is an established guard.

`WT g e g'` reads "in guard set `g`, expression `e` is well-typed and yields guard
set `g'`". The output `g'` of a subexpression flows to its parent — the Cedar
PathSet threading, in miniature.

The crux mirrors the vault:
  * A `drf k` is enabled only if an earlier `chk (sq k)` established the guard —
    a precondition set up by a *different* node in the tree.
  * The guard set stores *squares*; the root `k` cannot be read back from it, so
    a forward generator can only guess `k` and check `sq k ∈ g'` — which for
    arbitrary stored codes ~never hits.

Prediction: the derived forward generator fires `chk` freely but almost never
produces a `drf`, because by the time it needs a root the guard codes are
arbitrary (non-squares, or squares of un-guessable roots).
-/

def sq (k : Nat) : Nat := k * k

inductive Expr where
| lit (n : Nat)
| chk (c : Nat) (e : Expr)
| drf (k : Nat) (e : Expr)
deriving Repr, DecidableEq

abbrev Guards := List Nat

inductive WT : Guards → Expr → Guards → Prop where
| TLit : ∀ g n,
    WT g (Expr.lit n) g
| TChk : ∀ g c e g',
    WT g e g' →
    WT g (Expr.chk c e) (c :: g')
| TDrf : ∀ g k e g',
    WT g e g' →
    sq k ∈ g' →
    WT g (Expr.drf k e) g'

set_option specimen.multiOutput true
set_option specimen.autoDeriveDeps true
set_option match.ignoreUnusedAlts true

-- Hand-written generator for the perfect-square property, since Specimen cannot
-- invert `sq`. (Dead code in the forward baseline — `chk` picks its code freely —
-- but the synthesizer should pick it up once a square must be produced.)
instance : ArbitrarySizedSuchThat Nat (fun t => ∃ k, t = sq k) where
  arbitrarySizedST size := do
    let k ← Gen.choose Nat 0 size (by omega)
    return sq k

deriving instance Arbitrary for Expr

#guard_msgs(drop info, drop warning) in
derive_mutual
  (fun g => ∃ e g', WT g e g')

-- Count `drf` nodes in a generated expression.
def countDrf : Expr → Nat
  | .lit _ => 0
  | .chk _ e => countDrf e
  | .drf _ e => 1 + countDrf e

def countDerefs (numTraces : Nat := 1000) : IO (Nat × Nat) := do
  let mut exprsWithDrf := 0
  let mut totalDrf := 0
  for i in List.range numTraces do
    let (e, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, g') => WT [] e g') 10) (i + 5)
    let d := countDrf e
    totalDrf := totalDrf + d
    if d > 0 then exprsWithDrf := exprsWithDrf + 1
  return (exprsWithDrf, totalDrf)

#eval do
  let (withDrf, total) ← countDerefs 1000
  IO.println s!"expressions containing >=1 drf: {withDrf} / 1000"
  IO.println s!"total drf nodes generated: {total}"

-- Sanity check: the generator IS exercising the tree (firing chk, building
-- depth), so the drf=0 result is "never derefs" not "never generates".
def countChk : Expr → Nat
  | .lit _ => 0
  | .chk _ e => 1 + countChk e
  | .drf _ e => countChk e

def exprSize : Expr → Nat
  | .lit _ => 1
  | .chk _ e => 1 + exprSize e
  | .drf _ e => 1 + exprSize e

def exprStats (numTraces : Nat := 1000) : IO Unit := do
  let mut totalChk := 0
  let mut nonTrivial := 0
  let mut maxSize := 0
  for i in List.range numTraces do
    let (e, _) ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, g') => WT [] e g') 10) (i + 5)
    totalChk := totalChk + countChk e
    if exprSize e > 1 then nonTrivial := nonTrivial + 1
    if exprSize e > maxSize then maxSize := exprSize e
  IO.println s!"non-trivial exprs (size>1): {nonTrivial} / {numTraces}"
  IO.println s!"total chk nodes: {totalChk}, max expr size: {maxSize}"

#eval exprStats 1000

end AttrGuard
