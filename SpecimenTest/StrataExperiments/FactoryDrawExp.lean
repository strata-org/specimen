import Plausible.Gen
import Specimen.DecOpt
import Plausible.Arbitrary
import Specimen.DeriveArbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer

/-! Experiment: generating well-typed terms by DRAWING FROM A FACTORY.

    ## Motivation (see `Docs/Factory-directed-generation.md` and
    `Docs/Cmd-generator-analysis.md`)

    Strata's `Factory` (`Strata/DL/Lambda/Factory.lean`) is a table of function
    signatures (`Array (LFunc T)` + a name→index map). "Drawing from a Factory
    during generation" means: when building an `LExpr`, pick a function `f` from
    the factory and emit a FULLY-APPLIED call `f e₁ … eₙ`, where each `eᵢ` is
    generated AT THE TYPE read off `f`'s signature.

    A lesson from hand-writing an `LExpr` generator explains why this matters:
    the naive `App` rule

        Γ ⊢ e₁ : τ' → τ    Γ ⊢ e₂ : τ'
        ------------------------------- App
              Γ ⊢ e₁ e₂ : τ

    forces the generator to GUESS the argument type `τ'`. For an n-ary library
    function `f : σ₁ → … → σₙ → τ`, naive `App` must guess all of σ₁…σₙ correctly
    (and nest `App` n times) — vanishingly unlikely, so factory calls are almost
    never generated. Pałka et al. (AST '11) add a logically-redundant but
    operationally-essential "Indir" generation rule that reads the argument types
    straight off the function signature:

        f : σ₁ → σ₂ → τ ∈ Γ    Γ ⊢ e₁ : σ₁    Γ ⊢ e₂ : σ₂
        --------------------------------------------------- Indir
                       Γ ⊢ f e₁ e₂ : τ

    ## What this experiment isolates

    A minimal, structure-parameter-free model (bucket 0 is orthogonal — see
    `StructParamCmdShapeExp.lean`) of the Indir rule, to find out what Specimen
    needs to derive a generator that draws from a factory. It exercises THREE
    things at once:

      1. **Container inversion over a generator INPUT.** The factory `F` is a
         *parameter* (a fixed input), not a global. The `call` rule looks it up:
         `F[i]? = some sig`. Drawing a function = inverting this lookup
         (mode `(+F, −i, −sig)`).
      2. **The n-ary heterogeneous argument list (the Indir core).** A function's
         arg types are a LIST `sig.argTys`; the args are a LIST `args` generated
         pointwise, each element AT A DIFFERENT looked-up type. This is the
         `HasTyList` (Forall2-shaped) relation, mode (+types, −exprs).
      3. **Type-directed sub-expression generation.** `HasTyList.cons` recurses
         `HasTy F e t` with `t` an INPUT (from the signature) — i.e. generate an
         expression AT a given type. This is the harder, type-directed mode the
         `HasType` analysis flags.

    ## Observed behaviour (Lean v4.30.0-rc1)

    All three `derive_*` calls below **SUCCEED** — feasibility is NOT the blocker.
    But sampling the derived generators (a scratch `#eval` harness, not kept in
    this file) reproduces, on a derived generator, the distribution failure
    previously seen when hand-writing an `LExpr` generator:

      - **Synthesis mode**, factory `[() →base0, base0→base1, base0→base1→base2]`,
        200 samples each at size 3/5/7: **0% contained a factory call.** The
        always-applicable trivial base rule `lit : HasTy F (.lit n t) t` (a literal
        at *any* type) dominates every choice point, so the container-inversion
        `call` rule — though derived correctly — is essentially never taken.
      - **Type-directed mode** asking for type `base 2` (whose only producer is the
        binary factory function): again **0 factory calls** — only `lit`s of type
        `base 2`, because `lit` produces *any* requested type for free.
      - **Forced variant** (a separate scratch file restricting `lit` to `base 0`
        so `base 2` is reachable ONLY through the binary call → unary call chain):
        the type-directed generator **runs out of fuel** rather than reliably
        drawing the nested call.

    So the gaps are NOT "can Specimen derive this" but: (1) there is no
    result-type-directed *selection* of factory entries (the lookup is inverted by
    enumeration/guessing, not filtered by `resTy = target`); (2) the trivial base
    case is not weighted down; (3) deep nested calls exhaust fuel. These map onto
    Specimen capabilities discussed in `Docs/Factory-directed-generation.md`.

    FOLLOW-UP: `FactoryProducerExp.lean` hand-supplies the gap-(1) producer and
    measures the result — factory-call rate flips from 0% to 80–91% in
    type-directed mode (gap 1 is the decisive fix; gap 2 weighting is secondary). -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

namespace FactoryDrawExp

/-- Minimal base types, indexed by a Nat (e.g. 0 = Int, 1 = String, 2 = Bool). -/
inductive Ty where
  | base : Nat → Ty
  deriving DecidableEq, Repr, Inhabited, Arbitrary

/-- A factory entry: a function's argument types and result type.
    (Models the `inputs`/`output` of an `LFunc`.) -/
structure FnSig where
  argTys : List Ty
  resTy  : Ty
  deriving DecidableEq, Repr, Inhabited

/-- A factory is an indexed table of signatures (models `Factory.toArray`;
    the function "name" is its index `i`). -/
abbrev Factory := List FnSig

/-- Expressions: literals of a base type, and fully-applied factory calls. -/
inductive Expr where
  | lit  : Nat → Ty → Expr
  | call : Nat → List Expr → Expr
  deriving Repr, Inhabited

/- Typing relative to a fixed factory `F`. `HasTyList` is the pointwise
   (Forall2) relation matching an argument list against a signature's arg types
   — this is the Indir rule's heart. -/
mutual
inductive HasTy (F : Factory) : Expr → Ty → Prop where
  | lit : ∀ n t, HasTy F (.lit n t) t
  | call : ∀ (i : Nat) (sig : FnSig) (args : List Expr),
      F[i]? = some sig →
      HasTyList F args sig.argTys →
      HasTy F (.call i args) sig.resTy
inductive HasTyList (F : Factory) : List Expr → List Ty → Prop where
  | nil  : HasTyList F [] []
  | cons : ∀ e es t ts,
      HasTy F e t →
      HasTyList F es ts →
      HasTyList F (e :: es) (t :: ts)
end

/-! ### Attempt 1 — SYNTHESIS mode: given a factory, produce a term and its type.
    `(+F, −e, −t)`. This is "give me an arbitrary well-typed term that may call
    factory functions." -/
#guard_msgs(drop info) in
derive_mutual (fun (F : Factory) => ∃ (e : Expr) (t : Ty), HasTy F e t)

/-! ### Attempt 2 — TYPE-DIRECTED mode: given a factory and a target type,
    produce a term at that type. `(+F, +t, −e)`. This is the mode the Indir rule
    most helps: pick a factory function whose RESULT type is `t`, then fill args.
    (Whether the derived schedule actually filters by result type, or guesses a
    function and checks, is the key quality question — see the doc.) -/
#guard_msgs(drop info) in
derive_mutual (fun (F : Factory) (t : Ty) => ∃ (e : Expr), HasTy F e t)

/-! ### The pointwise list relation on its own — does the n-ary arg list derive?
    `(+F, +ts, −es)`: given the signature's argument types, produce the argument
    expressions. -/
#guard_msgs(drop info) in
derive_generator (fun (F : Factory) (ts : List Ty) => ∃ (es : List Expr), HasTyList F es ts)

end FactoryDrawExp
