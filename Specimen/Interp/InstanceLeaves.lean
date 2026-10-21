import Specimen.Interp

/-!
# Leaves from the instances in scope

An interpreter closure bottoms out at leaves: an unconstrained generator for every type a schedule
generates blind. Registering those by hand, in a module of their own, resolves them in *that* module's
environment rather than where the generator is derived, and the interpreter then measures a different
generator from the compiled one. On Cedar the compiled code's `Arbitrary Expr` is `TypeOfLeanTest`'s
placeholder `return .lit (.bool true)`; against a hand-written leaf that generates real expressions the
interpreter reaches three times as many distinct 3-paths as the code it is meant to predict (481 against
159), and an order learned from that does nothing once pinned.

So resolve them where the derivation runs. For every type the closure generates unconstrained, the Lean
type is rebuilt from the schedule's reified form, `Arbitrary`/`Enum` and `ToVal` are synthesised in the
*current* environment, and the resulting generator is installed under the exact rendering the lookup uses
(`InterpEnv.arbitraryAt` / `enumsAt`), replacing whatever was registered. Call this in the file that holds
the `derive_mutual`, or with the same instances in scope.

Kept out of `Specimen.Interp` because it needs `MetaM`.
-/

open Lean Meta Schedules

namespace Specimen.Interp

/-- Rebuilds a Lean type from its reified form. Only type formers and their arguments are expected; a
    type variable or hole means the step belongs to an uninstantiated polymorphic mode, which cannot be
    given a leaf. -/
partial def typeOfReified : ConstructorExpr → MetaM Expr
  | .TyCtor n args | .FuncApp n args | .Ctor n args => do
    let tyArgs ← args.mapM typeOfReified
    -- `mkAppM` rather than `mkAppM'` on a fresh-level constant: it solves the universe levels from the
    -- arguments (`List.{?u}` applied to a `Type`), which the latter left unassigned and then rejected.
    instantiateMVars (← mkAppM n tyArgs.toArray)
  | e => throwError "cannot rebuild a type from `{ppConstructorExpr e}`"

private unsafe def evalValGenImpl (e : Expr) : MetaM ValGen :=
  evalExpr ValGen (mkConst ``Specimen.Interp.ValGen) e

@[implemented_by evalValGenImpl]
private opaque evalValGen (e : Expr) : MetaM ValGen

private unsafe def evalValEnumImpl (e : Expr) : MetaM ValEnum :=
  evalExpr ValEnum (mkConst ``Specimen.Interp.ValEnum) e

@[implemented_by evalValEnumImpl]
private opaque evalValEnum (e : Expr) : MetaM ValEnum

/-- What `withInstanceLeaves` did, per rendered type. -/
structure InstanceLeafReport where
  installed : List String := []
  /-- `(rendering, why)`: left as registered before (or missing). -/
  failed : List (String × String) := []
  deriving Inhabited

def InstanceLeafReport.render (r : InstanceLeafReport) : String :=
  s!"[instance-leaves] {r.installed.length} leaf/leaves from instances in scope · {r.failed.length} not \
    resolvable" ++ String.join (r.failed.map (fun (t, w) => s!"\n  kept as registered: {t}: {w.take 200}"))

/-- Every type the closure's schedules generate unconstrained, with the sort that asks for it. -/
def InterpEnv.unconstrainedTypes (env : InterpEnv) : List (HypothesisExpr × ProducerSort) :=
  let all := env.relations.toList.flatMap (fun (_, rel) =>
    rel.allSchedules.flatMap (fun (_, (steps, _)) =>
      steps.filterMap (fun st => match st with
        | .Unconstrained _ (.NonRec hyp) ps => some (hyp, ps)
        | _ => none)))
  all.foldl (fun acc (h, ps) =>
    if acc.any (fun (h', ps') => ppHypothesisExpr h' == ppHypothesisExpr h && ps' == ps) then acc
    else acc ++ [(h, ps)]) []

/-- Replaces the closure's unconstrained leaves with the `Arbitrary` (generator schedules) and `Enum`
    (enumerator schedules) instances in scope where this runs. -/
def InterpEnv.withInstanceLeaves (env : InterpEnv) : MetaM (InterpEnv × InstanceLeafReport) := do
  let mut env := env
  let mut rep : InstanceLeafReport := {}
  for (hyp, ps) in env.unconstrainedTypes do
    let key := ppHypothesisExpr hyp
    try
      let ty ← typeOfReified (.TyCtor hyp.1 hyp.2)
      match ps with
      | .Generator =>
        let e ← mkAppOptM ``Specimen.Interp.arbitraryGen #[some ty, none, none]
        env := env.addArbitraryAt key (← evalValGen e)
      | .Enumerator =>
        let e ← mkAppOptM ``Specimen.Interp.enumGen #[some ty, none, none]
        env := env.addEnumAt key (← evalValEnum e)
      rep := { rep with installed := rep.installed ++ [key] }
    catch err =>
      rep := { rep with failed := rep.failed ++ [(key, ← err.toMessageData.toString)] }
  return (env, rep)

end Specimen.Interp
