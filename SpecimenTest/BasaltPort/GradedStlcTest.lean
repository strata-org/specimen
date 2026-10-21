import Basalt.Graded
import Basalt.GradedSound
import SpecimenTest.CommonDefinitions.STLCDefinitions

/-!
# `typing` as a graded enumeration, and where counting stops

`GradedAlgebraTest.lean` pins the algebra on datatypes (`Nat`, `Bool`, `List`, a binary tree). This file
does it for a real dependent relation — STLC's `typing Γ e τ` — because that is what the deriver has to
emit, and because it is where the `Graded`/`GradedBind` split stops being a design note and starts
deciding what is computable.

## The result, stated up front

**Four of the five typing rules stay applicative; `TApp` does not, and no reformulation fixes it.**

`TConst`, `TAdd`, `TVar` and `TAbs` are all expressible with `union`/`single`/`pay`/`pair`/`gmap` alone.
So the `TApp`-free fragment has a `Cnt` interpretation: its well-typed terms can be **counted without
being enumerated**, and `countsIx_stlcAF` proves that count correct.

`TApp` is different:

    TApp : typing Γ e₂ τ₁ → typing Γ e₁ (.Fun τ₁ τ₂) → typing Γ (.App e₁ e₂) τ₂

`τ₁` is existentially quantified and occurs in **both** premises. So the two sub-enumerations are
*correlated* — the `τ₁` chosen for `e₂` must be the same one that indexes `e₁`'s enumeration. `pair` is an
independent product and cannot express that; `bindC` can, and that is the entire content of the split.

Which of the two binds is a separate question, and getting it wrong is a *completeness* bug rather than a
typing error — see `stlcStep`'s docstring. `τ₁` carries its own size, so its level must be convolved
(`bindC`), not pinned to the premises' level (`bind`).

The consequence is not a limitation of this file, it is a fact about the relation: **there is no
compositional count-only interpretation of STLC typing.** To learn how many well-typed terms of size `n`
exist you must enumerate them and take the length. `Cnt` buys you nothing here, and `Counts` correctly
has nothing to say — there is no `GradedBind Cnt` instance to state it against.

Worth being precise about *why* no reformulation rescues it. Re-moding the premise so the enumerator
returns `(e₂, τ₁)` pairs does not help: the second premise's *index* still depends on the `τ₁` value.
Enumerating the two premises independently and filtering the mismatches needs `guard`, which is also
outside `Graded` and for the same reason. Correlation between premises is precisely the capability
`Graded` lacks.

## What grading measures here

The derivation, not the term — see `Basalt/Graded.lean`. `pay` marks a rule application with a recursive
premise, so a level counts nested rule applications. `TVar`'s cost is the de Bruijn index, since
`lookupEnum` pays per `Later` step, and `TConst`'s is the numeral's magnitude via `natStep`.
-/

open Basalt

/-- The index of the `typing` enumeration. Context and goal type are **inputs**, the term is the output —
the polarity `derive_mutual` would assign, with `e` the ∃-quantified position. -/
abbrev TyIx := List type × type

/-- `type` graded by size. It is a binary tree (`Nat` | `Fun`), so its level counts are Catalan — the same
sequence `GradedAlgebraTest.lean` gets for `GradedTestTree`, which is a useful coincidence to notice: the
type enumeration `TApp` needs is itself perfectly well-behaved. The problem is never `typeE`, it is the
correlation `TApp` requires of it. -/
def typeStep [Graded f] (rec : f type) : f type :=
  Choice.union (Graded.single type.Nat)
    (Graded.pay (Graded.gmap (fun p => type.Fun p.1 p.2) (Graded.pair rec rec)))

/-- `lookup Γ x τ` with `Γ` and `τ` as inputs and `x` the output: the de Bruijn indices at which `Γ` holds
`τ`, graded by that index.

Structurally recursive on `Γ`, so it needs no `gradedIter` — unlike `typing`, this relation shrinks an
input. That is also why it stays applicative: the `Now` rule's side condition `σ = τ` is decided on inputs,
which is an `if`, not a `guard`. -/
def lookupEnum [Graded f] : List type → type → f Nat
  | [], _ => Choice.nothing
  | σ :: Γ, τ =>
      Choice.union (if σ = τ then Graded.single 0 else Choice.nothing)
        (Graded.pay (Graded.gmap (· + 1) (lookupEnum Γ τ)))

/-- The `TApp`-free fragment: `TVar`, `TConst`, `TAdd`, `TAbs`.

Written against **`Graded` alone**. That is the claim being made — it therefore specialises to `Cnt`, and
`countsIx_stlcAF` below proves the counts match the enumeration. Matching on `τ` at the top is how the
rules that constrain their conclusion's type contribute nothing at other indices. -/
def stlcAFStep [Graded f] (natE : f Nat) (rec : TyIx → f term) : TyIx → f term
  | (Γ, .Nat) =>
      Choice.union (Graded.gmap term.Var (lookupEnum Γ .Nat))
        (Choice.union (Graded.gmap term.Const natE)
          (Graded.pay (Graded.gmap (fun p => term.Add p.1 p.2)
            (Graded.pair (rec (Γ, .Nat)) (rec (Γ, .Nat))))))
  | (Γ, .Fun τ1 τ2) =>
      Choice.union (Graded.gmap term.Var (lookupEnum Γ (.Fun τ1 τ2)))
        (Graded.pay (Graded.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))))

/-- The full system. `GradedBind` rather than `Graded`, and `TApp` is the only reason: binding `typeE` is
what correlates the `τ₁` in `e₂`'s enumeration with the `τ₁` indexing `e₁`'s.

This body **cannot** be instantiated at `Cnt`, and that is not an oversight — try it and the instance is
missing, which is the check that the split has not eroded.

**`bindC`, not `bind`.** `τ₁` is an auxiliary output that carries its own size, so its level must be
*convolved* with the premises' levels, not pinned equal to them. Using level-preserving `bind` here makes
the enumeration incomplete, and not merely budget-limited: with `bind`, `(λx:Nat. 0) 0` is produced at no
level at all, because `τ₁ = Nat` sits at level 0 while `Abs Nat (Const 0)` costs a `pay`, so no `n`
satisfies both. `stlc_enumerates_small_app` below is the regression test for exactly that term. -/
def stlcStep [GradedBind f] (natE : f Nat) (typeE : f type) (rec : TyIx → f term) : TyIx → f term
  | (Γ, τ) =>
      Choice.union (stlcAFStep natE rec (Γ, τ))
        (Graded.pay (GradedBind.bindC typeE (fun τ1 =>
          Graded.gmap (fun p => term.App p.1 p.2)
            (Graded.pair (rec (Γ, .Fun τ1 τ)) (rec (Γ, τ1))))))

/-! ## Counting the applicative fragment

Assembled from the closure lemmas, so each proof is the shape of its rule and nothing more. -/

theorem counts_typeStep (x : Lv type) (c : Cnt type) (h : Counts x c) :
    Counts (typeStep x) (typeStep c) :=
  (counts_single type.Nat).union (((h.pair h).gmap _).pay)

theorem counts_type (levels : Nat) :
    Counts (gradedIter typeStep levels) (gradedIter typeStep levels) :=
  counts_gradedIter counts_typeStep levels

theorem counts_lookupEnum (τ : type) : ∀ Γ : List type,
    Counts (lookupEnum Γ τ) (lookupEnum Γ τ)
  | [] => counts_nothing
  | _ :: Γ => ((counts_single 0).ite counts_nothing).union
      (((counts_lookupEnum τ Γ).gmap _).pay)

theorem counts_stlcAFStep {natE : Lv Nat} {cnatE : Cnt Nat} (hn : Counts natE cnatE)
    (x : TyIx → Lv term) (c : TyIx → Cnt term) (hx : CountsIx x c) :
    CountsIx (stlcAFStep natE x) (stlcAFStep cnatE c) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
    exact ((counts_lookupEnum _ Γ).gmap _).union
      ((hn.gmap _).union ((((hx (Γ, .Nat)).pair (hx (Γ, .Nat))).gmap _).pay))
  | Fun τ1 τ2 =>
    exact ((counts_lookupEnum _ Γ).gmap _).union (((hx (τ1 :: Γ, τ2)).gmap _).pay)

/-- **The counting result for the `TApp`-free fragment.** Level `n` of the enumeration has exactly as many
terms as the cardinality interpretation says, at every index and every number of levels. -/
theorem countsIx_stlcAF {natE : Lv Nat} {cnatE : Cnt Nat} (hn : Counts natE cnatE) (levels : Nat) :
    CountsIx (gradedIterIx (stlcAFStep natE) levels) (gradedIterIx (stlcAFStep cnatE) levels) :=
  counts_gradedIterIx (counts_stlcAFStep hn) levels

/-- Specialised to the magnitude-graded `Nat` leaf, which is the form the `#eval`s below use. -/
theorem stlcAF_length_eq_count (levels : Nat) (i : TyIx) (n : Nat) :
    (gradedIterIx (f := Lv) (stlcAFStep (gradedIter natStep levels)) levels i n).length
      = gradedIterIx (f := Cnt) (stlcAFStep (gradedIter natStep levels)) levels i n :=
  countsIx_stlcAF (counts_nat levels) levels i n

/-! ## Agreement, including `TApp`

`Agrees` relates `Lv` to `SetE`, and both implement `GradedBind`, so the full system is in scope here even
though counting is not. This is the asymmetry the split predicts, showing up as which theorems exist. -/

theorem agrees_typeStep (x : Lv type) (s : SetE type) (h : Agrees x s) :
    Agrees (typeStep x) (typeStep s) :=
  (agrees_single type.Nat).union (((h.pair h).gmap _).pay)

theorem agrees_lookupEnum (τ : type) : ∀ Γ : List type,
    Agrees (lookupEnum Γ τ) (lookupEnum Γ τ)
  | [] => agrees_nothing
  | _ :: Γ => ((agrees_single 0).ite agrees_nothing).union
      (((agrees_lookupEnum τ Γ).gmap _).pay)

theorem agrees_stlcAFStep {natE : Lv Nat} {snatE : SetE Nat} (hn : Agrees natE snatE)
    (x : TyIx → Lv term) (s : TyIx → SetE term) (hx : AgreesIx x s) :
    AgreesIx (stlcAFStep natE x) (stlcAFStep snatE s) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
    exact ((agrees_lookupEnum _ Γ).gmap _).union
      ((hn.gmap _).union ((((hx (Γ, .Nat)).pair (hx (Γ, .Nat))).gmap _).pay))
  | Fun τ1 τ2 =>
    exact ((agrees_lookupEnum _ Γ).gmap _).union (((hx (τ1 :: Γ, τ2)).gmap _).pay)

/-- The full system, `TApp` included. `Agrees.bindC` is what carries the correlated premise. -/
theorem agrees_stlcStep {natE : Lv Nat} {snatE : SetE Nat} (hn : Agrees natE snatE)
    {typeE : Lv type} {stypeE : SetE type} (ht : Agrees typeE stypeE)
    (x : TyIx → Lv term) (s : TyIx → SetE term) (hx : AgreesIx x s) :
    AgreesIx (stlcStep natE typeE x) (stlcStep snatE stypeE s) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  exact (agrees_stlcAFStep hn x s hx (Γ, τ)).union
    ((ht.bindC fun τ1 => (((hx (Γ, .Fun τ1 τ)).pair (hx (Γ, τ1))).gmap _)).pay)

/-- **Soundness and completeness for the whole of `typing`'s enumeration**, level by level: `→` nothing
enumerated that the specification excludes, `←` nothing the specification admits missed at its own level.
Counting has no counterpart to this — that is the point of the file. -/
theorem agreesIx_stlc {natE : Lv Nat} {snatE : SetE Nat} (hn : Agrees natE snatE)
    {typeE : Lv type} {stypeE : SetE type} (ht : Agrees typeE stypeE) (levels : Nat) :
    AgreesIx (gradedIterIx (stlcStep natE typeE) levels)
      (gradedIterIx (stlcStep snatE stypeE) levels) :=
  agrees_gradedIterIx (agrees_stlcStep hn ht) levels

/-! ## Actual numbers

`levels` is both the recursion depth and the leaf budget below, so these are enumerations of derivations
nested at most `levels` deep. Small values only: `Lv` is a function carrier with no memoisation, so `pair`
recomputes its operands' levels and cost climbs steeply. -/

private def natE : Lv Nat := gradedIter natStep 6
private def cnatE : Cnt Nat := gradedIter natStep 6
private def typeE : Lv type := gradedIter typeStep 6
private def stypeE : SetE type := gradedIter typeStep 6

private def afLv : TyIx → Lv term := gradedIterIx (stlcAFStep natE) 6
private def afCnt : TyIx → Cnt term := gradedIterIx (stlcAFStep cnatE) 6
private def fullLv : TyIx → Lv term := gradedIterIx (stlcStep natE typeE) 4

-- Types are Catalan, as the binary-tree shape predicts.
/-- info: [1, 1, 2, 5, 14, 42] -/
#guard_msgs in
#eval ((List.range 6).map fun n => (gradedIter (f := Cnt) typeStep 8 n : Nat))

-- `TApp`-free well-typed terms at `⊢ _ : Nat`, counted *without enumerating* — this is the `Cnt` path,
-- and it is the one STLC as a whole does not have.
/-- info: [1, 2, 5, 15, 51, 188] -/
#guard_msgs in
#eval ((List.range 6).map fun n => (afCnt ([], .Nat) n : Nat))

-- The same numbers via the value carrier. `stlcAF_length_eq_count` says this agreement is not luck.
/-- info: [1, 2, 5, 15, 51, 188] -/
#guard_msgs in
#eval ((List.range 6).map fun n => (afLv ([], .Nat) n).length)

-- Level 1 at `x : Nat ⊢ _ : Nat`, to see the terms rather than a count. `Const 1` is here rather than at
-- level 0 because `natStep` grades a numeral by its magnitude.
/--
info: [term.Const 1,
 term.Add (term.Var 0) (term.Var 0),
 term.Add (term.Var 0) (term.Const 0),
 term.Add (term.Const 0) (term.Var 0),
 term.Add (term.Const 0) (term.Const 0)]
-/
#guard_msgs in
#eval (afLv ([type.Nat], .Nat) 1)

-- `TApp`-free at a function type: only `TVar` and `TAbs` apply, and with an empty context `TVar` cannot,
-- so level 0 is *empty* — `TAbs` has to pay. A rule set that yielded something here would be wrong.
/-- info: [0, 2, 5, 21, 110] -/
#guard_msgs in
#eval ((List.range 5).map fun n => (afCnt ([], .Fun .Nat .Nat) n : Nat))

-- The full system, values only. There is deliberately no `Cnt` line to compare against.
--
-- Against `[1, 2, 5, 15, ...]` for the `TApp`-free fragment: levels 0 and 1 are unchanged, and level 2
-- gains exactly the two smallest well-typed applications, `(λx:Nat. x) 0` and `(λx:Nat. 0) 0`. Under the
-- old level-preserving `bind` this column read `[1, 2, 5, 16]` — no application until level 3, and the
-- two above never appearing at all.
/-- info: [1, 2, 7, 28] -/
#guard_msgs in
#eval ((List.range 4).map fun n => (fullLv ([], .Nat) n).length)

-- The two applications level 2 adds, named.
/--
info: [term.App (term.Abs (type.Nat) (term.Var 0)) (term.Const 0),
 term.App (term.Abs (type.Nat) (term.Const 0)) (term.Const 0)]
-/
#guard_msgs in
#eval ((fullLv ([], .Nat) 2).filter fun t => !((afLv ([], .Nat) 2).contains t))

/-! ### Regression: the `bind`-vs-`bindC` incompleteness

`(λx:Nat. 0) 0` is about the smallest well-typed application there is. Under level-preserving `bind` it was
enumerated at **no level whatsoever** — `τ₁ = Nat` sits at type level 0, so `bind` demanded the premise
pair also be at level 0, but `Abs Nat (Const 0)` costs a `pay`. Unreachable, not merely over budget.

This is the failure a level-by-level `Agrees` theorem structurally cannot catch: `Lv` and `SetE` ran the
same body, so both were wrong in the same way and agreed perfectly. Catching it needs the enumeration
compared against the *inductive* `typing`, which is the next thing to prove and the reason this test is
here in the meantime. -/

-- Now produced, and at level 2 exactly.
/-- info: [false, false, true, false] -/
#guard_msgs in
#eval ((List.range 4).map fun n => (fullLv ([], .Nat) n).contains
  (term.App (term.Abs .Nat (term.Const 0)) (term.Const 0)))
