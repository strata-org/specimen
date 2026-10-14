import Specimen

/-!
# A type abbreviation used as a type argument reifies as a type, not a function call

`abbrev Label := String` is a constant whose value is a *type*. In `@Tagged.mk Label s n` it is a type
argument, which carries no runtime value. It used to reify as `FuncApp Label []`, so the deriver saw a
function application in the premise: it lifted the type into a fresh *value* variable with an equality
premise (unrunnable — nothing generates a value for a type) and treated the enclosing argument as
containing a call. Cedar's `abbrev Attr := String` hit this on every premise over a map keyed by `Attr`.
-/

open Lean Meta Elab Term Schedules

structure Tagged (α : Type) where
  tag : α
  n : Nat

abbrev Label := String

inductive Carries : Nat → Tagged Label → Prop where
  | mk : ∀ n s, Carries n ⟨s, n⟩

/-- Reify `Carries`'s constructor conclusion and show how its `Tagged` argument's type argument came out. -/
def reifiedTypeArg : TermElabM String := do
  let info ← getConstInfoCtor ``Carries.mk
  forallTelescopeReducing info.type fun _ concl => do
    let (_, args) ← exprToHypothesisExpr ``Carries.mk concl
    match args with
    | [_, .Ctor _ (ty :: _)] =>
      return match ty with
        | .TyCtor c _ => s!"TyCtor {c}"
        | .FuncApp f _ => s!"FuncApp {f}"
        | _ => "other"
    | _ => return s!"unexpected shape: {args.length} args"

/-- info: "TyCtor Label" -/
#guard_msgs in
#eval reifiedTypeArg
