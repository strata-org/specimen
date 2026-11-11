import Specimen.Correctness.ReachClose
import Specimen.Correctness.SearchFinds

/-!
# The unconstrained generators of the base types are complete

`ArbitrarySizedComplete` for `Bool`, `Unit`, `Int`, `Char`, `String`, and `Option`, `×` and `⊕` of
complete types (`Nat` and `List` are in `ReachClose`). The generators derived for a user's types draw
from these.
-/

namespace Specimen.Correctness

open Basalt

instance : ArbitrarySizedComplete Bool where
  complete b := ⟨0, fun s _ => produces_of_reach (by
    show reachObs.spec (do pure ((← chooseNat 0 1) == 0) : SGen Bool) _
    walk
    cases b
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩)⟩

instance : ArbitrarySizedComplete Unit where
  complete _ := ⟨0, fun _ _ => produces_pure_iff.mpr rfl⟩

instance : ArbitrarySizedComplete Int where
  complete i := ⟨i.natAbs, fun s hs => by
    show Produces (do pure ((← chooseNat 0 (2 * s) : Nat) - (s : Int)) : SGen Int) i
    refine produces_bind_of (produces_chooseNat (k := (i + s).toNat) _ (Nat.zero_le _) (by omega))
      (produces_pure_iff.mpr ?_)
    omega⟩

instance : ArbitrarySizedComplete Char where
  complete c := ⟨0, fun s _ => by
    show Produces (frequency [(19, fun _ => do pure (Char.ofNat (← chooseNat 32 126))),
      (1, fun _ => do pure (Char.ofNat (← chooseNat 0 0x10FFFF)))] : SGen Char) c
    refine produces_of_reach ((reach_frequency (by decide)).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      by decide, reach_of_produces ?_⟩)
    have hc : c.toNat ≤ 0x10FFFF := by
      have h := c.valid
      simp only [Char.toNat, UInt32.isValidChar, Nat.isValidChar] at *
      omega
    exact produces_bind_of (produces_chooseNat (k := c.toNat) _ (Nat.zero_le _) hc)
      (produces_pure_iff.mpr (Char.ofNat_toNat c).symm)⟩

instance {α : Type} [ArbitrarySized α] [ArbitrarySizedComplete α] : ArbitrarySizedComplete (Option α) where
  complete o := ⟨match o with | none => 0 | some a => ArbitrarySizedComplete.bound a, fun s hs => by
    refine produces_of_reach ?_
    show reachObs.spec (oneOf [fun () => pure none, fun () => some <$> ArbitrarySized.arbitrarySized s] :
      SGen (Option α)) _
    walk
    cases o with
    | none => exact Or.inl rfl
    | some a => exact Or.inr ⟨a, ArbitrarySizedComplete.produces hs, rfl⟩⟩

instance {α β : Type} [ArbitrarySized α] [ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] : ArbitrarySizedComplete (α × β) where
  complete p := ⟨ArbitrarySizedComplete.bound p.1 + ArbitrarySizedComplete.bound p.2, fun s hs => by
    show Produces (do
      let a ← ArbitrarySized.arbitrarySized s
      let b ← ArbitrarySized.arbitrarySized s
      pure (a, b) : SGen (α × β)) p
    exact produces_bind_of (ArbitrarySizedComplete.produces (x := p.1) (by omega))
      (produces_bind_of (ArbitrarySizedComplete.produces (x := p.2) (by omega))
        (produces_pure_iff.mpr rfl))⟩

instance {α β : Type} [ArbitrarySized α] [ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] : ArbitrarySizedComplete (α ⊕ β) where
  complete p := ⟨Sum.elim ArbitrarySizedComplete.bound ArbitrarySizedComplete.bound p, fun s hs => by
    refine produces_of_reach ?_
    show reachObs.spec (oneOf [fun () => Sum.inl <$> ArbitrarySized.arbitrarySized s,
      fun () => Sum.inr <$> ArbitrarySized.arbitrarySized s] : SGen (α ⊕ β)) _
    walk
    cases p with
    | inl a => exact Or.inl ⟨a, ArbitrarySizedComplete.produces hs, rfl⟩
    | inr b => exact Or.inr ⟨b, ArbitrarySizedComplete.produces hs, rfl⟩⟩

instance : ArbitrarySizedComplete String where
  complete str := ⟨ArbitrarySizedComplete.bound str.toList, fun s hs => by
    show Produces (do pure (String.ofList (← ArbitrarySized.arbitrarySized (α := List Char) s)) :
      SGen String) str
    exact produces_bind_of (ArbitrarySizedComplete.produces (x := str.toList) hs)
      (produces_pure_iff.mpr String.ofList_toList.symm)⟩

open Lean Meta Elab Tactic in
/-- Case on every hypothesis that is an `∃`, keeping its witness and its body, and read each
unconstrained draw in a hypothesis at its instance's body, as `unfold_arbitrary` does the goal's:
an induction hypothesis of `arbitrary_complete`, for a field of the type itself, is then a fact
`reach_close` uses for the draw of that field. -/
partial def arbitraryCompleteHyps (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← whnfR (← instantiateMVars d.type)).isAppOf ``Exists then
      let gs ← g.cases d.fvarId
      return ← gs.toList.flatMapM fun s => arbitraryCompleteHyps s.mvarId
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' ← Meta.transform ty (pre := fun e => do
      if e.isAppOf ``Basalt.ArbitrarySized.arbitrarySized then
        match ← unfoldProjInst? e with
        | some e' => return .visit e'.headBeta
        | none => return .continue
      return .continue)
    if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  return [g]

open Lean Meta Elab Tactic in
/-- `arbitrary_complete`'s hypotheses (`arbitraryCompleteHyps`). -/
elab "arbitrary_complete_hyps" : tactic => do
  replaceMainGoal (← arbitraryCompleteHyps (← getMainGoal))

open Lean Meta Elab Tactic in
/-- Unfold, once, the generator a derived `ArbitrarySized` instance's body calls
(`T.basaltArbitrarySized`), so that `walk` sees its branches. -/
elab "unfold_derived_arbitrary" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let found ← IO.mkRef (none : Option Name)
  Meta.forEachExpr ty fun e => do
    if (← found.get).isNone then
      if let some c := e.getAppFn.constName? then
        if let .str _ l := c then
          if l == "basaltArbitrarySized" then found.set (some c)
  let some c ← found.get | throwError "unfold_derived_arbitrary: no derived generator in the goal"
  evalTactic (← `(tactic| unfold $(mkIdent c):ident))

/-- `ArbitrarySizedSearch` for a type whose generator was derived (`deriving instance
Basalt.ArbitrarySized`), a recursive one included: by induction on the size, the generator unfolded
once at both readings, its recursive draws related by the induction hypothesis. Use as
`⟨by arbitrary_search_derived⟩`. -/
macro "arbitrary_search_derived" : tactic => `(tactic| (
  intro n
  induction n <;>
  (arbitrary_complete_hyps
   unfold_arbitrary_all; (try unfold_derived_arbitrary); walk)))

/-- `ArbitrarySizedHits` for a type whose generator was derived, as `arbitrary_search_derived` is.
Use as `⟨by arbitrary_hits_derived⟩`. -/
macro "arbitrary_hits_derived" : tactic => `(tactic| (
  intro n
  induction n <;>
  (arbitrary_complete_hyps
   unfold_arbitrary_all; (try unfold_derived_arbitrary); walk)))

/-- `ArbitrarySizedComplete` for a type whose generator was derived (`deriving instance
Basalt.ArbitrarySized`): by induction on the value, for each constructor the walk of the generator at
a positive size, its choices made by `reach_close` from the fields' own `ArbitrarySizedComplete`
instances (and, for a field of the type itself, the induction hypothesis), the size bound their sum.
Use as `⟨by arbitrary_complete⟩`. Not for a nested inductive (one whose fields hold it in another
type, a `List T` say), which `induction` does not take. -/
macro "arbitrary_complete" : tactic => `(tactic| (
  intro x
  induction x <;>
  (arbitrary_complete_hyps
   refine ⟨?_ + 1, fun s hs => produces_of_reach ?_⟩
   on_goal 2 => (
     cases s with
     | zero => exact absurd hs (Nat.not_succ_le_zero _)
     | succ s =>
       have hs := Nat.le_of_succ_le_succ hs
       unfold_arbitrary_all; (try unfold_derived_arbitrary); walk; all_goals reach_close; reach_close_bounds)
   all_goals exact 0)))

end Specimen.Correctness
