import Plausible.Gen
import Specimen.DecOpt
import Plausible.Arbitrary
import Specimen.DeriveArbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer

/-! Experiment: SUPPLYING a Bucket-1 factory producer flips factory-call rate
    from ~0% to a non-trivial majority.

    ## What this tests

    `FactoryDrawExp.lean` showed that a derived generator for an Indir-style
    `call` rule emits ~0% factory calls: the lookup hypothesis `F[i]? = some sig`
    (with `i` an output) is inverted by GUESS-AND-CHECK — Specimen guesses an index
    and checks — which almost never hits, so the branch backtracks to the trivial
    base case.

    Here we hand-supply the producer that `Docs/Factory-directed-generation.md`
    (need 1) and `Docs/Delegated-producer-synthesis.md` (bucket 1) call for: given
    the factory and a demanded result type, SCAN the factory and return a matching
    `(index, signature)`. This reads the argument types off the matched signature
    instead of guessing them — the producer realization of Pałka et al.'s "Indir"
    rule. The pattern mirrors `ModeDirectedExp.lean` (supply the instance; codegen
    is unchanged).

    ## Observed results (Lean v4.30.0-rc1)

    Factory `F0 = [ () → base0,  base0 → base1,  base0 → base1 → base2 ]`.
    200 samples per cell. The 0% column is the SAME relation with the lookup left
    as a raw conjunction Specimen inverts itself (a separate scratch run; see
    `FactoryDrawExp.lean` for the un-producered measurement).

    | mode                                   | no producer | with producer(s) |
    |----------------------------------------|-------------|------------------|
    | type-directed @ base2 (only call fits) |     0%      | 80–91% (mostly depth≥2) |
    | type-directed @ base0 (lit competes)   |     0%      | 80–85%           |
    | synthesis (result type is an output)   |     0%      | ~40–52%          |

    Three findings:

    1. **The producer flips 0% → high, end to end.** At `base2` (whose only
       producer is the binary factory fn) the majority of samples are depth≥2 —
       i.e. the FULL Indir chain (binary call whose base1 arg is a unary call whose
       base0 arg is a literal) is generated reliably. So container inversion +
       pointwise typed-argument recursion really does realize Indir.

    2. **Synthesis mode needs the BY-KEY projection too** (a sharp confirmation of
       `Factory-directed-generation.md` need 1). With only the type-directed
       producer `(+F,+t) → (-i,-sig)` in scope, synthesis mode `(+F) → (-t,…)`
       FAILS TO SYNTHESIZE AN INSTANCE — the scheduler demands
       `ArbitrarySizedSuchThat (Ty × Nat × FnSig) …` because the result type `t` is
       now also an output. Supplying the by-key projection (enumerate all entries,
       take `resTy` as output) fixes it. Both projections of the one container
       producer are needed: by-value for type-directed, by-key for synthesis.

    3. **Weighting (bucket 2) is a smaller, mode-dependent lever.** In
       type-directed mode the producer ALONE gives high call rates even when the
       trivial `lit` rule also satisfies the target (base0: 77–87%). In synthesis
       mode the rate settles around ~52% — the base case competes more when the
       type is not pinned — so per-rule weighting is what would push that higher,
       but the producer already makes calls the common case, not a rarity.

    NOTE: `derive_mutual` prints "No schedule found for factoryEntryAt[…]" warnings
    — these are the OTHER (non-supplied) modes of the opaque predicate for which no
    producer exists; the supplied modes are used and generation works. -/

open Plausible
open ArbitrarySizedSuchThat
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

namespace FactoryProducerExp

inductive Ty where
  | base : Nat → Ty
  deriving DecidableEq, Repr, Inhabited, Arbitrary

structure FnSig where
  argTys : List Ty
  resTy : Ty
  deriving DecidableEq, Repr, Inhabited

abbrev Factory := List FnSig

inductive Expr where
  | lit  : Nat → Ty → Expr
  | call : Nat → List Expr → Expr
  deriving Repr, Inhabited

/-- Opaque (def-wrapped) factory-lookup obligation of the `call` rule: "entry `i`
    of `F` is `sig`, and its result type is `t`." Written as a bare `def` so
    Specimen emits a mode-directed producer call rather than inverting it. -/
def factoryEntryAt (F : Factory) (t : Ty) (i : Nat) (sig : FnSig) : Prop :=
  F[i]? = some sig ∧ sig.resTy = t

/-- BY-VALUE projection (type-directed mode `(+F, +t) → (-i, -sig)`): scan the
    factory for entries whose result type is `t`, pick one. Reads the matching
    signature off the table instead of guessing an index. -/
instance instTypeDirected (F : Factory) (t : Ty) :
    ArbitrarySizedSuchThat (Nat × FnSig) (fun p => factoryEntryAt F t p.1 p.2) where
  arbitrarySizedST _ := do
    let cands : List (Nat × FnSig) :=
      (F.zipIdx).filterMap (fun (sig, i) => if sig.resTy = t then some (i, sig) else none)
    match cands with
    | [] => return (0, default)          -- no match; downstream check discards
    | c :: cs => Gen.elements (c :: cs) (by simp)

/-- BY-KEY projection (synthesis mode `(+F) → (-t, -i, -sig)`): enumerate ALL
    entries and take each result type as the output `t`. Synthesis mode REQUIRES
    this projection — see finding 2 in the header. -/
instance instSynthesis (F : Factory) :
    ArbitrarySizedSuchThat (Ty × Nat × FnSig) (fun p => factoryEntryAt F p.1 p.2.1 p.2.2) where
  arbitrarySizedST _ := do
    let cands : List (Ty × Nat × FnSig) :=
      (F.zipIdx).map (fun (sig, i) => (sig.resTy, i, sig))
    match cands with
    | [] => return (default, 0, default)
    | c :: cs => Gen.elements (c :: cs) (by simp)

mutual
inductive HasTy (F : Factory) : Expr → Ty → Prop where
  | lit : ∀ n t, HasTy F (.lit n t) t
  | call : ∀ (i : Nat) (sig : FnSig) (args : List Expr),
      factoryEntryAt F t i sig →
      HasTyList F args sig.argTys →
      HasTy F (.call i args) t
inductive HasTyList (F : Factory) : List Expr → List Ty → Prop where
  | nil  : HasTyList F [] []
  | cons : ∀ e es t ts, HasTy F e t → HasTyList F es ts → HasTyList F (e :: es) (t :: ts)
end

-- Type-directed: produce a term AT a demanded type (uses instTypeDirected).
#guard_msgs(drop info, drop warning) in
derive_mutual (fun (F : Factory) (t : Ty) => ∃ (e : Expr), HasTy F e t)

-- Synthesis: produce a term and its type (uses instSynthesis).
#guard_msgs(drop info, drop warning) in
derive_mutual (fun (F : Factory) => ∃ (e : Expr) (t : Ty), HasTy F e t)

def F0 : Factory :=
  [ { argTys := [],                  resTy := .base 0 },
    { argTys := [.base 0],           resTy := .base 1 },
    { argTys := [.base 0, .base 1],  resTy := .base 2 } ]

partial def hasCall : Expr → Bool
  | .lit _ _ => false
  | .call _ _ => true

partial def depth : Expr → Nat
  | .lit _ _ => 0
  | .call _ args => 1 + (args.foldl (fun m e => Nat.max m (depth e)) 0)

/-- Type-directed @ a target type. -/
def measureTD (target : Ty) (sz : Nat) : IO Unit := do
  let s ← Gen.run (Gen.listOf (arbitrarySizedST (fun (e : Expr) => HasTy F0 e target) sz)) 200
  let calls := (s.filter hasCall).length
  let deep  := (s.filter (fun e => depth e ≥ 2)).length
  IO.println s!"  type-directed, size={sz}: {s.length} samples, {calls} calls ({100*calls/(max 1 s.length)}%), {deep} depth≥2"

/-- Synthesis (result type is an output). -/
def measureSynth (sz : Nat) : IO Unit := do
  let s ← Gen.run (Gen.listOf (arbitrarySizedST (fun (et : Expr × Ty) => HasTy F0 et.1 et.2) sz)) 200
  let calls := (s.filter (fun (et : Expr × Ty) => hasCall et.1)).length
  IO.println s!"  synthesis, size={sz}: {s.length} samples, {calls} calls ({100*calls/(max 1 s.length)}%)"

#eval IO.println "type-directed @ base2 (only the binary fn produces base2):"
#eval measureTD (.base 2) 4
#eval measureTD (.base 2) 6
#eval IO.println "type-directed @ base0 (the trivial `lit` rule also competes):"
#eval measureTD (.base 0) 4
#eval IO.println "synthesis (result type is an output):"
#eval measureSynth 4
#eval measureSynth 6

end FactoryProducerExp
