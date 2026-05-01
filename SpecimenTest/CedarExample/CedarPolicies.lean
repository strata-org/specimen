import SpecimenTest.CedarExample.Cedar
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer

open Plausible

/-!
This file extends the Cedar definitions with policy-related types and relations,
converted from the Rocq definitions.
-/

/-- Policy effects -/
inductive Effect where
| permit
| forbid
deriving Repr, BEq, DecidableEq

/-- Cedar.Scope definitions for policies -/
inductive Cedar.Scope where
| any
| eqScope (entity: Cedar.EntityUID)
| memScope (entity: Cedar.EntityUID)
| isScope (entity: Cedar.EntityName)
| isMem (ety: Cedar.EntityName) (entity: Cedar.EntityUID)
deriving Repr, BEq, DecidableEq

/-- Converts scope to Cedar expression -/
inductive Cedar.ScopeToExpr : Cedar.Scope → Cedar.Var → Cedar.CedarExpr → Prop where
| STE_any: ∀ v, Cedar.ScopeToExpr Cedar.Scope.any v (Cedar.CedarExpr.lit (Cedar.Prim.boolean true))
| STE_equals: ∀ v uid,
    Cedar.ScopeToExpr (Cedar.Scope.eqScope uid) v (Cedar.CedarExpr.binaryApp Cedar.BinaryOp.equals (Cedar.CedarExpr.var v) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid)))
| STE_mem: ∀ v uid,
    Cedar.ScopeToExpr (Cedar.Scope.memScope uid) v (Cedar.CedarExpr.binaryApp Cedar.BinaryOp.mem (Cedar.CedarExpr.var v) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid)))
| STE_is: ∀ v n,
    Cedar.ScopeToExpr (Cedar.Scope.isScope n) v (Cedar.CedarExpr.unaryApp (Cedar.UnaryOp.is n) (Cedar.CedarExpr.var v))
| STE_ismem: ∀ v n uid,
    Cedar.ScopeToExpr (Cedar.Scope.isMem n uid) v (Cedar.CedarExpr.andExpr (Cedar.CedarExpr.unaryApp (Cedar.UnaryOp.is n) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid))) (Cedar.CedarExpr.binaryApp Cedar.BinaryOp.mem (Cedar.CedarExpr.var v) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid))))

/-- Principal scope -/
inductive PrincipalScope where
| principalScope (scope: Cedar.Scope)
deriving Repr, BEq, DecidableEq

/-- Principal scope to expression -/
inductive PSToExpr : PrincipalScope → Cedar.CedarExpr → Prop where
| MkPSExpr: ∀ s e,
    Cedar.ScopeToExpr s Cedar.Var.principal e →
    PSToExpr (PrincipalScope.principalScope s) e

/-- Resource scope -/
inductive ResourceScope where
| resourceScope (scope: Cedar.Scope)
deriving Repr, BEq, DecidableEq

/-- Resource scope to expression -/
inductive RSToExpr : ResourceScope → Cedar.CedarExpr → Prop where
| MkRSExpr: ∀ s e,
    Cedar.ScopeToExpr s Cedar.Var.resource e →
    RSToExpr (ResourceScope.resourceScope s) e

/-- Action scope -/
inductive ActionScope where
| actionScope (scope: Cedar.Scope)
| actionInAny (es: List Cedar.EntityUID)
deriving Repr, BEq, DecidableEq

/-- Action list to expression -/
inductive ALToExpr : List Cedar.EntityUID → Cedar.CedarExpr → Prop where
| ALtoE_nil: ALToExpr [] Cedar.CedarExpr.setExprNil
| ALtoE_cons: ∀ a e rest uid,
    ALToExpr rest e →
    ALToExpr (a::rest) (Cedar.CedarExpr.setExprCons (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid)) e)

/-- Action scope to expression -/
inductive ASToExpr : ActionScope → Cedar.CedarExpr → Prop where
| ASE_scope: ∀ s e,
    Cedar.ScopeToExpr s Cedar.Var.action e →
    ASToExpr (ActionScope.actionScope s) e
| ASE_any: ∀ es e,
    ALToExpr es e →
    ASToExpr (ActionScope.actionInAny es) (Cedar.CedarExpr.binaryApp Cedar.BinaryOp.mem (Cedar.CedarExpr.var Cedar.Var.action) e)

/-- Condition kind -/
inductive ConditionKind where
| when
| unless
deriving Repr, BEq, DecidableEq

/-- Policy condition -/
inductive Condition where
| MkCondition : ConditionKind → Cedar.CedarExpr → Condition
deriving Repr, BEq, DecidableEq

/-- Condition to expression -/
inductive ConditionToExpr : Condition → Cedar.CedarExpr → Prop where
| CToE_when: ∀ e, ConditionToExpr (Condition.MkCondition ConditionKind.when e) e
| CToE_unless: ∀ e,
    ConditionToExpr (Condition.MkCondition ConditionKind.unless e) (Cedar.CedarExpr.unaryApp Cedar.UnaryOp.not e)

/-- Conditions list to expression -/
inductive ConditionsToExpr : List Condition → Cedar.CedarExpr → Prop where
| CsToE_nil: ConditionsToExpr [] (Cedar.CedarExpr.lit (Cedar.Prim.boolean true))
| CsToE_cons: ∀ c cs e es,
    ConditionsToExpr cs es →
    ConditionToExpr c e →
    ConditionsToExpr (c::cs) (Cedar.CedarExpr.andExpr e es)

/-- Cedar policy -/
inductive Policy where
| MkPolicy : String → Effect → PrincipalScope → ActionScope → ResourceScope → List Condition → Policy
deriving Repr, BEq, DecidableEq

/-- Policy to expression -/
inductive PolicyToExpr : Policy → Cedar.CedarExpr → Prop where
| MkPolicyExpr: ∀ p ep a ea r er cs ecs s eff,
    PSToExpr p ep →
    ASToExpr a ea →
    RSToExpr r er →
    ConditionsToExpr cs ecs →
    PolicyToExpr
        (Policy.MkPolicy s eff p a r cs)
        (Cedar.CedarExpr.andExpr ep (Cedar.CedarExpr.andExpr ea (Cedar.CedarExpr.andExpr er ecs)))
/-- Substitute action Cedar.Variable with entity UID -/
inductive SubstituteAction : Cedar.EntityUID → Cedar.CedarExpr → Cedar.CedarExpr → Prop where
| SA_lit: ∀ uid p, SubstituteAction uid (Cedar.CedarExpr.lit p) (Cedar.CedarExpr.lit p)
| SA_var_action: ∀ uid,
    SubstituteAction uid (Cedar.CedarExpr.var Cedar.Var.action) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid))
| SA_var_other: ∀ uid v, v ≠ Cedar.Var.action → SubstituteAction uid (Cedar.CedarExpr.var v) (Cedar.CedarExpr.var v)
| SA_ite: ∀ e1 e1' e2 e2' e3 e3' uid,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid e2 e2' →
    SubstituteAction uid e3 e3' →
    SubstituteAction uid (Cedar.CedarExpr.ite e1 e2 e3) (Cedar.CedarExpr.ite e1' e2' e3')
| SA_andExpr: ∀ e1 e1' e2 e2' uid,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid e2 e2' →
    SubstituteAction uid (Cedar.CedarExpr.andExpr e1 e2) (Cedar.CedarExpr.andExpr e1' e2')
| SA_orExpr: ∀ e1 e1' e2 e2' uid,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid e2 e2' →
    SubstituteAction uid (Cedar.CedarExpr.orExpr e1 e2) (Cedar.CedarExpr.orExpr e1' e2')
| SA_unaryApp: ∀ e1 e1' uid op,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid (Cedar.CedarExpr.unaryApp op e1) (Cedar.CedarExpr.unaryApp op e1')
| SA_binaryApp: ∀ e1 e1' e2 e2' uid op,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid e2 e2' →
    SubstituteAction uid (Cedar.CedarExpr.binaryApp op e1 e2) (Cedar.CedarExpr.binaryApp op e1' e2')
| SA_getAttr: ∀ e1 e1' uid fn,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid (Cedar.CedarExpr.getAttr e1 fn) (Cedar.CedarExpr.getAttr e1' fn)
| SA_hasAttr: ∀ e1 e1' uid fn,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid (Cedar.CedarExpr.hasAttr e1 fn) (Cedar.CedarExpr.hasAttr e1' fn)
| SA_setExprNil: ∀ uid, SubstituteAction uid Cedar.CedarExpr.setExprNil Cedar.CedarExpr.setExprNil
| SA_setExprCons: ∀ e1 e1' e2 e2' uid,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid e2 e2' →
    SubstituteAction uid (Cedar.CedarExpr.setExprCons e1 e2) (Cedar.CedarExpr.setExprCons e1' e2')
| SA_recExprNil: ∀ uid, SubstituteAction uid Cedar.CedarExpr.recExprNil Cedar.CedarExpr.recExprNil
| SA_recExprCons: ∀ e1 e1' e2 e2' uid fn,
    SubstituteAction uid e1 e1' →
    SubstituteAction uid e2 e2' →
    SubstituteAction uid (Cedar.CedarExpr.recExprCons fn e1 e2) (Cedar.CedarExpr.recExprCons fn e1' e2')

/-- Well-typed scope (assumes Cedar.Var is not context) -/
inductive WellTypedScope : Cedar.Environment → Cedar.Var → Cedar.Scope → Prop where
| WTS_any: ∀ v x, WellTypedScope v x Cedar.Scope.any
| WTS_eqScope: ∀ v x uid,
    Cedar.HasType Cedar.PathSet.allpaths v
        ((Cedar.CedarExpr.binaryApp Cedar.BinaryOp.equals (Cedar.CedarExpr.var x) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid))), Cedar.PathSet.allpaths)
        (Cedar.CedarType.boolType Cedar.BoolType.anyBool) →
    WellTypedScope v x (Cedar.Scope.eqScope uid)
| WTS_memScope: ∀ v x uid,
    Cedar.HasType Cedar.PathSet.allpaths v
        ((Cedar.CedarExpr.binaryApp Cedar.BinaryOp.mem (Cedar.CedarExpr.var x) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid))), Cedar.PathSet.allpaths)
        (Cedar.CedarType.boolType Cedar.BoolType.anyBool) →
    WellTypedScope v x (Cedar.Scope.memScope uid)
| WTS_isScope: ∀ v x n,
    Cedar.HasType Cedar.PathSet.allpaths v ((Cedar.CedarExpr.unaryApp (Cedar.UnaryOp.is n) (Cedar.CedarExpr.var x)), Cedar.PathSet.allpaths) (Cedar.CedarType.boolType Cedar.BoolType.anyBool) →
    WellTypedScope v x (Cedar.Scope.isScope n)
| WTS_isMem: ∀ v x n uid,
    Cedar.HasType Cedar.PathSet.allpaths v ((Cedar.CedarExpr.andExpr (Cedar.CedarExpr.unaryApp (Cedar.UnaryOp.is n) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid))) (Cedar.CedarExpr.binaryApp Cedar.BinaryOp.mem (Cedar.CedarExpr.var x) (Cedar.CedarExpr.lit (Cedar.Prim.entityUID uid)))), Cedar.PathSet.allpaths) (Cedar.CedarType.boolType Cedar.BoolType.anyBool) →
    WellTypedScope v x (Cedar.Scope.isMem n uid)

/-- Well-typed action in set -/
inductive WellTypedActionInSet : Cedar.Environment → List Cedar.EntityUID → Prop where
| WTA_single: ∀ v t n x,
    Cedar.HasTypeVar v Cedar.Var.action t →
    Cedar.HasTypePrim v (Cedar.Prim.entityUID (Cedar.EntityUID.MkEntityUID n x)) t →
    WellTypedActionInSet v [Cedar.EntityUID.MkEntityUID n x]
| WTA_cons: ∀ v n x es t,
    Cedar.HasTypeVar v Cedar.Var.action t →
    Cedar.HasTypePrim v (Cedar.Prim.entityUID (Cedar.EntityUID.MkEntityUID n x)) t →
    WellTypedActionInSet v es →
    WellTypedActionInSet v (Cedar.EntityUID.MkEntityUID n x :: es)

/-- Well-typed action scope -/
inductive WellTypedActionScope : Cedar.Environment → ActionScope → Prop where
| WTAS_scope: ∀ v sc,
    WellTypedScope v Cedar.Var.action sc →
    WellTypedActionScope v (ActionScope.actionScope sc)
| WTAS_in: ∀ v es,
    WellTypedActionInSet v es →
    WellTypedActionScope v (ActionScope.actionInAny es)

/-- Well-typed condition -/
inductive WellTypedCondition : Cedar.Environment → Condition → Prop where
| WTC_all: ∀ v e c,
    Cedar.HasType Cedar.PathSet.allpaths v (e, Cedar.PathSet.allpaths) (Cedar.CedarType.boolType Cedar.BoolType.anyBool) →
    WellTypedCondition v (Condition.MkCondition c e)

/-- Well-typed policy -/
inductive WellTypedPolicy : Cedar.Environment → Policy → Prop where
| T_Policy: ∀ v p a r c s eff,
    WellTypedScope v Cedar.Var.principal p →
    WellTypedScope v Cedar.Var.resource r →
    WellTypedActionScope v a →
    WellTypedCondition v c →
    WellTypedPolicy v (Policy.MkPolicy s eff (PrincipalScope.principalScope p) a (ResourceScope.resourceScope r) [c])

/-- Policy has type in all Cedar.Environments -/
inductive Cedar.HasTypePolicyAll : List Cedar.Environment → Policy → Prop where
| T_PolicySingle: ∀ p, Cedar.HasTypePolicyAll [] p
| T_PolicyCons: ∀ p e es,
    WellTypedPolicy e p →
    Cedar.HasTypePolicyAll es p →
    Cedar.HasTypePolicyAll (e::es) p

/-- Request has type -/
inductive Cedar.HasTypeRequest : Cedar.Environment → Request → Prop where
| T_Request: ∀ V s reqpt reqact reqrt reqc pt rt act ct c puid ruid,
    V = Cedar.Environment.MkEnvironment s (RequestType.MkRequest reqpt reqact reqrt reqc) →
    reqpt = pt →
    reqrt = rt →
    reqact = act →
    ReqContextToCedarType reqc ct →
    RecordExpr c →
    Value c →
    Cedar.HasType Cedar.PathSet.allpaths V (c, Cedar.PathSet.allpaths) ct →
    Cedar.HasTypeRequest V (Request.MkReq (Cedar.EntityUID.MkEntityUID pt puid) act (Cedar.EntityUID.MkEntityUID rt ruid) c)

/-- Request has type in any Cedar.Environment -/
inductive Cedar.HasTypeRequestAny : List Cedar.Environment → Request → Prop where
| T_RequestSingle: ∀ v vs req,
    Cedar.HasTypeRequest v req →
    Cedar.HasTypeRequestAny (v::vs) req
| T_RequestAny: ∀ v vs req,
    Cedar.HasTypeRequestAny vs req →
    Cedar.HasTypeRequestAny (v::vs) req

/-- Validate policy -/
inductive ValidatePolicy : Cedar.Schema → Policy → Prop where
| V_policy: ∀ ets acts reqs es p,
    Cedar.ActionSchemaToRequestTypes acts [] reqs →
    Cedar.SchemaToEnvironments (Cedar.Schema.MkSchema ets acts) reqs es →
    Cedar.HasTypePolicyAll es p →
    ValidatePolicy (Cedar.Schema.MkSchema ets acts) p

/-- Validate entity -/
inductive ValidateEntity : Cedar.Schema → (Cedar.EntityUID × Cedar.EntityData) → Prop where
| V_EntityData: ∀ attrs ets acts n ts t s ancestors S,
    bogusname = Cedar.EntityName.MkName "bogus" [] →
    bogusid = Cedar.EntityUID.MkEntityUID bogusname "bogusid" →
    S = Cedar.Schema.MkSchema ets acts →
    Cedar.Value attrs →
    Cedar.GetEntityAttr ets (n, "attrs", true) t →
    Cedar.ReqContextToCedarType ts t →
    Cedar.HasType Cedar.PathSet.allpaths (Cedar.Environment.MkEnvironment S (Cedar.RequestType.MkRequest bogusname bogusid bogusname [])) (attrs, Cedar.PathSet.allpaths) t →
    ValidateEntity S (Cedar.EntityUID.MkEntityUID n s, Cedar.EntityData.MkEntityData attrs ancestors)

/-- Validate request -/
inductive ValidateRequest : Cedar.Schema → Cedar.Request → Prop where
| V_request: ∀ ets acts reqs es req,
    Cedar.ActionSchemaToRequestTypes acts [] reqs →
    Cedar.SchemaToEnvironments (Cedar.Schema.MkSchema ets acts) reqs es →
    Cedar.HasTypeRequestAny es req →
    ValidateRequest (Cedar.Schema.MkSchema ets acts) req
