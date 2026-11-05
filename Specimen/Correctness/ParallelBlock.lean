import Lean
import Specimen.Debug

/-!
# A block's induction, its workers' cases proved in parallel

The soundness proofs of a derived block are one induction on the fuel, over the conjunction of its
workers' statements. `proveBlockParallel` states each worker's base case and step (`∀ f, (S₁ f ∧ … ∧
Sₖ f) → Sᵢ (f + 1)`) as a theorem of its own, which Lean elaborates in parallel, and assembles the
block's theorem from them by `Nat.rec`, at once: the theorems' statements are known before their
proofs are.
-/

namespace Specimen.Correctness

open Lean Meta Elab Term Command

/-- `log_time "name" tac`: `tac`, its time and thread logged to `SPECIMEN_TIMER_LOG`. -/
syntax "log_time " str ppSpace tactic : tactic

elab_rules : tactic
  | `(tactic| log_time $n:str $t:tactic) => do
    let t0 ← IO.monoNanosNow
    try Lean.Elab.Tactic.evalTactic t
    finally
      timerLog s!"  ptime {n.getString} {((← IO.monoNanosNow) - t0) / 1000000} ms tid {← IO.getTID} at {t0 / 1000000}"

/-- The block `∀ fuel, S₁ fuel ∧ … ∧ Sₖ fuel` of the workers' statements `ws` (`∀ fuel, …` each),
as `block`; each worker's case `wᵢ.<tag>_zero` and `wᵢ.<tag>_step`, by `zeroTac i` and `stepTac i`
(which see the step's hypothesis as `ih`). Statements without universe parameters only. -/
def proveBlockParallel (ws : Array (Name × Expr)) (tag : String) (block : Name)
    (zeroTac stepTac : Nat → CommandElabM (TSyntax `tactic)) : CommandElabM Unit := do
  let k := ws.size
  let conjAt (x : Expr) : Expr :=
    let parts := ws.map fun (_, s) => s.bindingBody!.instantiate1 x
    parts.pop.foldr (fun p acc => mkAnd p acc) parts.back!
  let succ (f : Expr) : Expr := mkNatAdd f (mkNatLit 1)
  -- the cases' statements, as definitions the theorems are stated with
  let mut names : Array (Name × Name) := #[]
  for i in [:k] do
    let (w, s) := ws[i]!
    let zeroS := Name.str w s!"{tag}_zero_stmt"
    let stepS := Name.str w s!"{tag}_step_stmt"
    liftTermElabM do
      let zero := s.bindingBody!.instantiate1 (mkNatLit 0)
      let step ← withLocalDeclD `f (mkConst ``Nat) fun f => withLocalDeclD `ih (conjAt f) fun ih =>
        mkForallFVars #[f, ih] (s.bindingBody!.instantiate1 (succ f))
      for (n, v) in [(zeroS, zero), (stepS, step)] do
        let d : DefinitionVal := { name := n, levelParams := [], type := mkSort levelZero, value := v, hints := .abbrev, safety := .safe }
        addDecl (.defnDecl d)
        setReducibleAttribute n
    names := names.push (Name.str w s!"{tag}_zero", Name.str w s!"{tag}_step")
    let z ← zeroTac i
    let st ← stepTac i
    let zId : Ident := mkIdent (`_root_ ++ names[i]!.1)
    let sId : Ident := mkIdent (`_root_ ++ names[i]!.2)
    let zS : Ident := mkIdent zeroS
    let sS : Ident := mkIdent stepS
    let fId : Ident := mkIdent `f
    let ihId : Ident := mkIdent `ih
    elabCommand (← `(command| theorem $zId:ident : $zS:ident := by
      delta $zS:ident
      $z:tactic))
    let lbl := Syntax.mkStrLit s!"{names[i]!.2}"
    elabCommand (← `(command| theorem $sId:ident : $sS:ident := by
      log_time $lbl (
        delta $sS:ident
        intro $fId:ident $ihId:ident
        $st:tactic)))
  -- the block, by induction, from the cases
  liftTermElabM do
    let conj ← withLocalDeclD `fuel (mkConst ``Nat) fun fuel => mkForallFVars #[fuel] (conjAt fuel)
    let pair (es : Array Expr) : MetaM Expr :=
      es.pop.foldrM (fun e acc => mkAppM ``And.intro #[e, acc]) es.back!
    let motive ← withLocalDeclD `n (mkConst ``Nat) fun n => mkLambdaFVars #[n] (conjAt n)
    let zeroPair ← pair (names.map fun (z, _) => mkConst z)
    let stepFn ← withLocalDeclD `f (mkConst ``Nat) fun f => withLocalDeclD `ih (conjAt f) fun ih => do
      mkLambdaFVars #[f, ih] (← pair (names.map fun (_, s) => mkApp2 (mkConst s) f ih))
    let pf ← withLocalDeclD `fuel (mkConst ``Nat) fun fuel =>
      mkLambdaFVars #[fuel] (mkAppN (mkConst ``Nat.rec [levelZero]) #[motive, zeroPair, stepFn, fuel])
    addDecl <| .thmDecl { name := block, levelParams := [], type := conj, value := pf }

end Specimen.Correctness
