import Specimen.Schedules
import Specimen.Debug

/-!
# Rejection points of a derived producer

A rule of a derived generator or enumerator *rejects* where it can fail after drawing: a check, a
pattern match, or a required shape of a sub-producer's output, that involves a value the rule drew.
A rule with none fails, if at all, by its inputs alone (a guard, a truncation), never by chance, so
each of its runs succeeds surely or never (given its sub-producers do the same). `rejectionPoints`
lists a rule's rejection points; `specimen.reportRejections` has `derive_mutual` report them.
-/

namespace Specimen.Rejections

open Lean Meta Schedules

/-- The unknowns a constructor expression mentions. -/
partial def ceVars : ConstructorExpr → List Name
  | .Unknown n => [n]
  | .Ctor _ as | .FuncApp _ as | .TyCtor _ as => as.flatMap ceVars
  | _ => []

partial def patVars : Pattern → List Name
  | .UnknownPattern n => [n]
  | .CtorPattern _ ps => ps.flatMap patVars
  | .LitPattern _ => []

def sourceVars : Source → List Name
  | .NonRec (_, as) => as.flatMap ceVars
  | .Rec _ as | .MutRec _ as => as.flatMap ceVars

def ppSource : Source → String
  | .NonRec (h, as) => s!"{h.getString!} {as.map ppConstructorExpr}"
  | .Rec f as | .MutRec f as => s!"{f.getString!} {as.map ppConstructorExpr}"

/-- Whether matching `p` can fail: a literal, or a constructor of a type with more than one. -/
partial def refutable (p : Pattern) : MetaM Bool := do
  match p with
  | .UnknownPattern _ => return false
  | .LitPattern _ => return true
  | .CtorPattern c ps =>
    let env ← getEnv
    let several : Bool := match env.find? c with
      | some (.ctorInfo ci) =>
        match env.find? ci.induct with
        | some (.inductInfo ii) => decide (ii.ctors.length > 1)
        | _ => true
      | _ => true
    if several then return true
    for q in ps do
      if ← refutable q then return true
    return false

/-- Whether `n` names a type (its type ends in a sort): an annotation, not a value's shape. -/
def isTypeConst (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  forallTelescopeReducing ci.type fun _ b => return b.isSort

partial def ceRefutable (e : ConstructorExpr) : MetaM Bool := do
  if let .Ctor n _ := e then if ← isTypeConst n then return false
  if let .FuncApp n _ := e then if ← isTypeConst n then return false
  match e with
  | .Unknown _ | .Hole => return false
  | .Lit _ => return true
  | .Ctor c as =>
    let env ← getEnv
    let several : Bool := match env.find? c with
      | some (.ctorInfo ci) =>
        match env.find? ci.induct with
        | some (.inductInfo ii) => decide (ii.ctors.length > 1)
        | _ => true
      | _ => true
    if several then return true
    for a in as do
      if ← ceRefutable a then return true
    return false
  -- a type (an output's annotation), a sort: no constraint on the value
  | .TyCtor .. | .CSort _ => return false
  | _ => return true

/-- A rule's rejection points: each step that can fail on a value the rule drew, described. -/
def rejectionPoints (steps : List ScheduleStep) : MetaM (List String) := do
  let mut drawn : Std.HashSet Name := {}
  let mut out : List String := []
  for step in steps do
    match step with
    | .Unconstrained x _ _ => drawn := drawn.insert x
    | .SuchThat outs src _ =>
      let srcDrawn := (sourceVars src).filter (drawn.contains ·)
      for (x, pat?) in outs do
        if let some pat := pat? then
          if ← ceRefutable pat then
            out := out ++ [s!"output {x} of {ppSource src} must match {ppConstructorExpr pat}"]
        drawn := drawn.insert x
        for v in (pat?.map ceVars).getD [] do drawn := drawn.insert v
      let _ := srcDrawn
    | .Check src polarity =>
      let ds := (sourceVars src).filter (drawn.contains ·)
      unless ds.isEmpty do
        out := out ++ [s!"check {if polarity then "" else "¬ "}{ppSource src} on drawn {ds}"]
    | .Match _ v pat =>
      if drawn.contains v then
        if ← refutable pat then
          out := out ++ [s!"match drawn {v} against a refutable pattern"]
        for x in patVars pat do drawn := drawn.insert x
  return out

end Specimen.Rejections
