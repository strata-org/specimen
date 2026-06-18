import Specimen.DeriveArbitrary
import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: the structure-parameter blocker (bucket 0) in the *`Cmd` shape*,
    as opposed to the *`LExpr` shape* already covered by `StructParamExp.lean` /
    `StructParamPathsExp.lean`.

    ## Why a separate experiment

    `HasType` stresses the structure parameter `T` in ONE place: the generated
    term's *output type* is a projection `LExpr T.mono`. `StructParamExp.lean`
    isolates exactly that (`Boxed T : T.Elem → Prop`, generate `x : T.Elem`), and
    `StructParamPathsExp.lean` shows the constrained path fails there with
    `unknown free variable T_1`.

    Strata's `Cmd P` is different in two ways that this file isolates:

    1. **Projections appear in CONSTRUCTOR-ARGUMENT positions, not the output
       type.** A `Cmd P` value is `init (name : P.Ident) (ty : P.Ty) … |
       set … | assert (b : P.Expr) …`. The *output* type of a `CmdWT` relation is
       `Cmd P` — the parameter *applied*, NOT a projection (the well-behaved
       `Boxed T` shape). The projections `P.Ident` / `P.Ty` / `P.Expr` are instead
       the types of values GENERATED INSIDE the constructor body.

    2. **The structure has MIXED Type / non-Type fields.** `PureExpr` bundles
       `Ident Expr Ty : Type` with `EqIdent : DecidableEq Ident` and
       `TyEnv TyContext EvalEnv : Type`. The `deriving Arbitrary` port
       (`expandStructBinders` in `DeriveArbitrary.lean`) is ALL-OR-NOTHING: it
       throws on the first field that is not a Type-or-structure-of-Types.

    ## Observed behaviour (Lean v4.30.0-rc1), recorded below

    - **Gap 2 confirmed**: `deriving Arbitrary` on the MIXED structure is REJECTED
      because of the `EqIdent` field — see the `#guard_msgs(error)` block.
    - **Projection-in-argument-position is fine for the unconstrained path**: the
      ALL-Type variant (`MiniCmd'`) derives and `#synth`s cleanly (baseline A′).
    - **The constrained path fails DIFFERENTLY from the `LExpr` shape**: NOT
      `unknown free variable P_1`. Instead it emits an instance that (a) drops the
      `[Arbitrary P.Ident]`/`[Arbitrary P.Expr]` binders entirely (the param `P`
      is not `isSort`, so `MakeConstrainedProducerInstance` never collects it into
      `typeParams` and emits no instance binders), and (b) mis-binds the structure
      parameter — passing `P_1` as an *explicit* constructor argument
      (`MiniCmd'.set P_1 name e`), causing arity/type-mismatch errors. See the
      detailed comment on the `derive_generator` call.

    The upshot for the bucket-0 fix: the `LExpr` output-type freshening fix would
    NOT address the `Cmd` shape, because the `Cmd`-shape failures are about
    (i) instance-binder emission for a non-`isSort` structure parameter and
    (ii) parameter-arity handling in argument positions — neither of which is the
    output-type delaboration bug. A fix that serves both must be broader. -/

open Plausible
set_option guard_msgs.diff true

namespace StructParamCmdShapeExp

/-! ### A `PureExpr`-shaped parameter: mixed Type and non-Type fields.
    `Ident`/`Ty`/`Expr` are the generated value spaces; `EqIdent` is a
    `DecidableEq` instance field (a non-Type field), modelling `PureExpr.EqIdent`. -/
structure PE where
  Ident   : Type
  Ty      : Type
  Expr    : Type
  EqIdent : DecidableEq Ident      -- non-Type field: breaks all-or-nothing expansion

/-! ### Gap 2 — UNCONSTRAINED `deriving Arbitrary` REJECTS the mixed structure.
    The `Cmd`-shaped datatype carries projected fields in ARGUMENT positions; the
    output type `MiniCmd P` is the parameter *applied* (not a projection). The
    rejection is NOT about the argument positions — it is `expandStructBinders`'s
    all-or-nothing check tripping on the `EqIdent` field. A fix serving `Cmd` must
    expand only the Type-valued fields actually generated and tolerate (or harvest
    as a `DecidableEq` instance) the non-Type fields. -/
inductive MiniCmd (P : PE) where
  | set    (name : P.Ident) (e : P.Expr)
  | assert (b : P.Expr)

/--
error: Cannot derive Plausible.Arbitrary for 'StructParamCmdShapeExp.MiniCmd': structure parameter 'P✝' has a field of type 'DecidableEq
  P.Ident', which is not a Type or structure of Types. This makes the type effectively indexed.
-/
#guard_msgs(error) in
deriving instance Arbitrary for MiniCmd


/-! ### Baseline A′ — same shape with an ALL-Type structure (no `EqIdent`).
    Isolates gap (1) (projection-in-argument-position) away from gap (2)
    (mixed fields). This is the `Cmd`-shape analog of the passing `Params` test
    in `DeriveArbitrary/StructureParameterTest.lean`, and it SUCCEEDS: the
    unconstrained path handles projections in argument positions. -/
structure PEpure where
  Ident : Type
  Expr  : Type

inductive MiniCmd' (P : PEpure) where
  | set    (name : P.Ident) (e : P.Expr)
  | assert (b : P.Expr)

deriving instance Arbitrary for MiniCmd'

#guard_msgs(drop info) in
#synth Arbitrary (MiniCmd' ⟨Nat, Bool⟩)


/-! ### Path 2 — CONSTRAINED `derive_generator`. The relation's OUTPUT type is
    `MiniCmd' P` (parameter applied, not projected); the constructor HYPOTHESIS
    OUTPUTS have projected types `P.Ident` / `P.Expr`. This is the genuine
    `Cmd`-shape stress on the constrained path.

    Contrast `StructParamPathsExp.lean`, where the *output type itself* is the
    projection `T.Elem` and the failure is `unknown free variable T_1`. HERE the
    failure is different — the generated `aux_arb` is well-formed structurally but:

      • NO `[Arbitrary P.Ident]` / `[Arbitrary P.Expr]` instance binders are
        emitted on the inner function (the supplied binders in the lambda below
        are not threaded through), so the inner `Arbitrary.arbitrary` calls for
        `name : P_1.Ident` and `e : P_1.Expr` fail to synthesize:
          `failed to synthesize instance  Arbitrary P_1.Expr`
          `failed to synthesize instance  Arbitrary P_1.Ident`
        Root cause: `MakeConstrainedProducerInstance` collects `typeParams` (and
        emits their `[Arbitrary _]`/`[DecidableEq _]` binders) only when
        `paramType.isSort`. A structure parameter `P : PEpure` is NOT a sort, so
        it is treated as an ordinary value param and gets no instance binders.

      • The structure parameter is mis-bound as an EXPLICIT constructor argument:
          `MiniCmd'.set P_1 name e`     →  `Function expected at MiniCmd'.set …`
          `MiniCmd'.assert P_1 b`       →  `Application type mismatch: P_1 …`
        i.e. the deriver passes the parameter `P_1` positionally to the
        constructor, which expects `P` implicit. A parameter-arity/threading bug
        distinct from the binder-emission gap above.

    Neither failure is the `LExpr` output-type freshening bug. So the bucket-0
    fix, to serve `Cmd`, must (a) emit `[Arbitrary P.field]` / `[DecidableEq …]`
    binders for STRUCTURE parameters (not just `isSort` params), as the
    unconstrained `expandStructBinders` already does, and (b) thread the structure
    parameter through the constructor application as an implicit, not an explicit
    argument. -/
inductive MiniCmdWT (P : PEpure) : MiniCmd' P → Prop where
  | set    : ∀ (name : P.Ident) (e : P.Expr), MiniCmdWT P (.set name e)
  | assert : ∀ (b : P.Expr), MiniCmdWT P (.assert b)

-- Expected (today): FAILS as detailed above (binder emission + param arity),
-- NOT with `unknown free variable P_1`.
derive_generator (fun (P : PEpure) [Arbitrary P.Ident] [Arbitrary P.Expr] =>
  ∃ (c : MiniCmd' P), MiniCmdWT P c)

end StructParamCmdShapeExp
