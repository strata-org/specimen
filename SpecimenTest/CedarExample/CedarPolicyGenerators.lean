import SpecimenTest.CedarExample.CedarPolicies
import SpecimenTest.CedarExample.CedarCheckerGenerators

open Plausible

/-!
This file contains derived checkers and generators for the policy-related
inductive relations defined in CedarPolicies.lean.
-/

-- Suppress warnings for unused variables in derived generators/checkers
set_option linter.unusedVariables false

-- Suppress warnings for redundant pattern-match cases in derived generators/checkers
set_option match.ignoreUnusedAlts true

-- Derive checkers and generators for scope relations
#derive_checker (Cedar.ScopeToExpr s v e)
#derive_generator (fun (s : Cedar.Scope) => Cedar.ScopeToExpr s v e)
#derive_generator (fun (e : Cedar.CedarExpr) => Cedar.ScopeToExpr s v e)

-- Principal scope
#derive_checker (PSToExpr s e)
#derive_generator (fun (s : PrincipalScope) => PSToExpr s e)

-- Resource scope
#derive_checker (RSToExpr s e)
#derive_generator (fun (s : ResourceScope) => RSToExpr s e)

-- Action list and scope
#derive_checker (ALToExpr s e)
#derive_generator (fun (s : List Cedar.EntityUID) => ALToExpr s e)

#derive_checker (ASToExpr s e)
#derive_generator (fun (s : ActionScope) => ASToExpr s e)

-- Conditions
#derive_checker (ConditionToExpr c e)
#derive_generator (fun (c : Condition) => ConditionToExpr c e)

#derive_checker (ConditionsToExpr c e)
#derive_generator (fun (c : List Condition) => ConditionsToExpr c e)

-- Policy
#derive_checker (PolicyToExpr p e)

deriving instance Arbitrary for Effect

#derive_generator (fun (p : Policy) => PolicyToExpr p e)
-- Substitute action
#derive_checker (SubstituteAction uid e e')
#derive_generator (fun (e : Cedar.CedarExpr) => SubstituteAction uid e e')

-- Well-typed scope
-- #derive_checker (WellTypedScope v x s)
#derive_generator (fun (s : Cedar.Scope) => WellTypedScope v x s)

-- Well-typed action in set
#derive_checker (WellTypedActionInSet v es)
#derive_generator (fun (es : List Cedar.EntityUID) => WellTypedActionInSet v es)

-- Well-typed action scope
#derive_checker (WellTypedActionScope v a)
#derive_generator (fun (a : ActionScope) => WellTypedActionScope v a)

-- Well-typed condition
#derive_checker (WellTypedCondition v c)
#derive_generator (fun (c : Condition) => WellTypedCondition v c)

-- Well-typed policy
#derive_checker (WellTypedPolicy v p)
#derive_generator (fun (p : Policy) => WellTypedPolicy v p)

-- Policy has type in all environments
#derive_checker (HasTypePolicyAll es p)
#derive_generator (fun (p : Policy) => Cedar.HasTypePolicyAll es p)

-- Request has type
#derive_checker (Cedar.HasTypeRequest v req)
#derive_generator (fun (req : Cedar.Request) => Cedar.HasTypeRequest v req)

-- Request has type in any environment
#derive_checker (Cedar.HasTypeRequestAny vs req)
#derive_generator (fun (req : Cedar.Request) => Cedar.HasTypeRequestAny vs req)

-- Validate policy
#derive_checker (ValidatePolicy s p)
#derive_generator (fun (p : Policy) => ValidatePolicy s p)

-- Validate entity
#derive_checker (ValidateEntity s ed)
#derive_generator (fun (ed : Cedar.EntityUID × Cedar.EntityData) => ValidateEntity s ed)

-- Validate request
#derive_checker (ValidateRequest s req)



#derive_generator (fun (req : Cedar.Request) => ValidateRequest s req)

#derive_generator (fun (rs : _) => Cedar.ActionSchemaToRequestTypes acts [] rs)

-- Generate a valid policy for a given schema
def genValidPolicy (s : Cedar.Environment) (fuel : Nat) : Gen Policy := do
  ArbitrarySizedSuchThat.arbitrarySizedST (fun p => WellTypedPolicy s p) fuel

-- Generate environment from well-typed schema then well-typed policy
def genSchemaEnvPolicy (fuel : Nat) : Gen Policy := do
  let ns := [Cedar.EntityName.MkName "User" [], Cedar.EntityName.MkName "Action" []]
  -- Generate well-formed schema
  let schema ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s => Cedar.WfSchema ns s) fuel
  match schema with
  | Cedar.Schema.MkSchema ets acts => do
    -- Generate request types from schema
    let reqs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun rs => Cedar.ActionSchemaToRequestTypes acts [] rs) fuel
    -- Generate environments from schema and request types
    let envs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun es => Cedar.SchemaToEnvironments schema reqs es) fuel
    match envs with
    | env :: _ => do
      -- Generate well-typed policy for first environment
      ArbitrarySizedSuchThat.arbitrarySizedST (fun p => WellTypedPolicy env p) fuel
    | [] => throw Gen.genericFailure

#print genSchemaEnvPolicy

#eval! Gen.printSamples (genSchemaEnvPolicy 3)
