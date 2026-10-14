import SpecimenTest.BasaltPort.GradedStlcAdequacy

/-!
# Adequacy of a graded enumeration, proved once over rules-as-data

`SpecimenTest/BasaltPort/GradedStlcAdequacy.lean` proves `typing Γ e τ ↔ ∃ L levels n, enumAt L levels …`
for STLC, by hand, for a hand-written `stlcStep` whose premises were hand-assigned to graded
operations. This file replaces the hand-assignment with a datatype and the hand proof with two generic
theorems — and then proves the generic result *is* the hand-written one, not an analogue of it
(§"The bridge").

## The rule shape

`Body ι α` is a straight-line premise list in continuation-passing form — the smallest thing that
still distinguishes the choices a deriver has to make per premise:

* `call i k` — a premise that is a *recursive* (or same-SCC sibling) call of the relation being
  derived, at index `i`. Always `bindC`: its output is a derivation of the same relation and so
  always carries its own size.
* `aux g p P k` — a premise discharged by *another* producer `p`, which is a **budget-indexed family**
  `Nat → Lv β` (a leaf generator for a type, a cross-SCC checker/enumerator, an existentially
  quantified auxiliary output). `p` is the **executable** enumeration, not a specification, so a rule
  set cannot claim coverage its leaf code lacks. `g` is the deriver's choice: `.sized` ⇒ `bindC`,
  `.flat` ⇒ `bind`. **This is the choice that was got wrong once.**
* `check v P k` — a decidable premise, discharged by a Kleene verdict. `guard`.
* `cond t c k` — a side condition decided on the *inputs*. `if`.
* `pay k` — one rule application's worth of level. Per-rule rather than uniform, because the rules a
  deriver emits do not all pay: `stlcStep` charges `TAdd`/`TAbs`/`TApp` and not `TVar`/`TConst`.
* `ret a` / `fail` — the conclusion, and "this rule does not apply at this index".

Nothing else is in the datatype. In particular there are no variables, no environment and no
substitution: a premise's continuation receives its output as a Lean function argument, so the
binding structure is Lean's. That is what keeps the two adequacy proofs to one case per premise kind.

## What is proved, and why it catches the bug

Each `Body` has two readings that are *independent*:

* `denote` — the graded enumeration, which reads the `Grade` and ignores the `Prop`s;
* `HoldsR` / `Derives` — the inductive relation the rules define, which reads the `Prop`s and
  **ignores the `Grade`**.

`soundR` and `complete` relate them, and `adequate` packages the pair; `adequateL` restates it for the
value carrier `denoteL`/`enumL`, which is executable code. Because the relation cannot see the grading,
a wrong grade cannot be absorbed by "both sides made the same mistake" — which is exactly how the
original `bind`-for-`bindC` bug survived every level-wise `Agrees` theorem. Concretely the per-premise
obligation completeness imposes is

* `.sized` ⇒ `Covers p P` — the producer reaches each admissible value at *some* budget and *some*
  level;
* `.flat`  ⇒ `Unsized p P` — it reaches it, from some budget on, at *every* level.

`Unsized` is what "level-preserving" literally means, and for a leaf that carries its own size it is
false. §"The wrong choice" below refutes it for STLC's type leaf and then exhibits a well-typed term
the `.flat` rule set enumerates at no level at all.

Both obligations quantify the **leaf budget**, which is what makes the generic theorem's statement
`∃ L l n, …` rather than `∃ l n, …`: a leaf is a family `p : Nat → Lv β`, completeness picks the
budget, and `MonoL` (also in `BodyComplete`) is what lets two premises found at different budgets be
raised to a common one.

## The bridge

`stepOf (rules .sized) L rec = stlcStep (natAt L) (tyAt L) rec` — one unfolding of the rule *data*
is the hand-written step function, equal and not merely equivalent. Hence
`Stlc.stlc_iff_budget_generic` and `Stlc.stlc_mem_iff_budget_generic` have, character for character,
the statements of `GradedStlcAdequacy.stlc_iff_budget` and `stlc_mem_iff_budget`; the four `example`s
at the end of §"The bridge" machine-check that by putting each where the other is expected.

Three reconciliation lemmas are the whole content: `bindC_ret` (a `bindC` into a `ret` is a `gmap` —
the split is forced), `bindC_bindC_ret` (two nested ones are a `pair`), and `denote_rVar` (the
generate-and-check mode for `TVar` — `aux` over all naturals followed by `check lookup` — is exactly
the direct producer `gmap term.Var (lookupEnum Γ τ)`, because `lookupEnum` grades a variable by its
own de Bruijn index). That is why `Body` needs no `pair` and no `gmap` constructor.

## Relation to `Schedules.ScheduleStep`

`ScheduleStep` is the emission-side IR; this is its adequacy-relevant erasure. The mapping is total:

| `ScheduleStep`                                  | `Body`                                  |
| ----------------------------------------------- | --------------------------------------- |
| `.SuchThat outs (.Rec fn args)`                 | `call i k`                              |
| `.SuchThat outs (.MutRec fn args)`              | `call i k` (same constructor: the two interpreters already treat `.Rec`/`.MutRec` identically) |
| `.SuchThat outs (.NonRec hyp)`                  | `aux .sized p P k`                      |
| `.Unconstrained v (.NonRec ty)`                 | `aux .sized p P k` (leaf generator)     |
| `.Check src polarity`                           | `check v P k` (polarity is folded into `v`: `.no`/`.yes` swap, `.inconclusive` fixed) |
| `.Match explicit scrutinee pattern`             | `cond t c k`, or a Lean `match` in the rule function with `fail` in the non-matching branch |
| `ScheduleSort.ProducerSchedule _ conclusion`    | `pay` then `ret a`                      |

and the fields it drops are the ones both interpreters already drop: `Explicit`, the
`Option ConstructorExpr` type annotations, `ProducerSort`, and the `.Rec`/`.MutRec` distinction. See
the file's closing section for why a faithful `ScheduleStep` semantics was not the target.
-/

open Basalt

namespace RuleShape

/-- The deriver's per-premise grading choice for an auxiliary producer: does the premise's output
carry its own size (`bindC`), or is it delegated on the undivided budget (`bind`)? -/
inductive Grade where
  /-- The output carries its own size: convolve. `bindC`. -/
  | sized
  /-- The output carries no size: level-preserving. `bind`. -/
  | flat
  deriving DecidableEq, Repr

variable {ι α β : Type}

/-- One constructor's premise list, in continuation-passing form.

`Type 1` because `aux` quantifies over the premise's output type and because the `Prop` fields carry
the premise's *meaning* alongside its *implementation*. Those two are what make the bug visible:
`denote` reads the implementation, `HoldsR` reads the meaning, and neither can see the other. -/
inductive Body (ι α : Type) : Type 1 where
  /-- The conclusion: emit this output. -/
  | ret (a : α) : Body ι α
  /-- This rule does not apply here. The erasure of a failed `.Match`. -/
  | fail : Body ι α
  /-- One rule application's worth of level. Per-rule, not uniform: `stlcStep` charges
  `TAdd`/`TAbs`/`TApp` and not `TVar`/`TConst`, and the bridge below has to reproduce that exactly. -/
  | pay (k : Body ι α) : Body ι α
  /-- A side condition decided on the inputs: `t` is the test that runs, `c` what it decides. -/
  | cond (t : Bool) (c : Prop) (k : Body ι α) : Body ι α
  /-- A checked premise: `v` is the Kleene verdict that runs, `P` the proposition it checks. -/
  | check (v : V) (P : Prop) (k : Body ι α) : Body ι α
  /-- A recursive / same-SCC premise at index `i`, binding its output. -/
  | call (i : ι) (k : α → Body ι α) : Body ι α
  /-- A premise discharged by another producer `p`, which is claimed to produce exactly the values
  satisfying `P`. `g` is the grading choice.

  `p` is the **executable** enumeration, indexed by a *leaf budget*: `p L` is the enumeration the
  leaf offers when run at budget `L`. Its specification is read off it by `specOf`, so a rule set
  cannot claim a leaf coverage property its code does not have, and the budget is what the generic
  completeness theorem quantifies. -/
  | aux (g : Grade) {β : Type} (p : Nat → Lv β) (P : β → Prop) (k : β → Body ι α) : Body ι α

/-- What an executable producer specifies: the values it lists, level by level. `Agrees` by
construction, so no per-leaf agreement obligation is ever needed. -/
def specOf (p : Lv β) : SetE β := fun n b => b ∈ p n

theorem agrees_specOf (p : Lv β) : Agrees p (specOf p) := fun _ _ => Iff.rfl

theorem specOf_eq_of_agrees {p : Lv β} {s : SetE β} (h : Agrees p s) : specOf p = s := by
  funext n b; exact propext (h n b)

/-- One body per constructor, per index. The index-dependence is what lets a rule that constrains its
conclusion contribute nothing elsewhere; `fail` covers the same job inside a body. -/
abbrev RuleSet (ι α : Type) := ι → List (Body ι α)

/-! ## The relation the rules define

Two presentations, both needed and for different directions.

`HoldsR R b a` plugs an *arbitrary* `R` in for the recursive premises. It is a plain recursive `Prop`,
so at an instance it unfolds by `simp` into precisely the constructor's premises — which is what makes
"these rules are valid for `typing`" a five-line obligation rather than an inversion exercise.

`Derives`/`Holds` is the relation *generated* by the rules: the least such `R`. It is an inductive, so
it supports the induction completeness needs. -/

/-- The premises of `b`, read with `R` for the recursive calls. Grading-blind by construction, and
`pay`-blind too: a level is not a premise. -/
def HoldsR (R : ι → α → Prop) : Body ι α → α → Prop
  | .ret a', a => a = a'
  | .fail, _ => False
  | .pay k, a => HoldsR R k a
  | .cond _ c k, a => c ∧ HoldsR R k a
  | .check _ P k, a => P ∧ HoldsR R k a
  | .call i k, a => ∃ x, R i x ∧ HoldsR R (k x) a
  | .aux _ _ P k, a => ∃ b, P b ∧ HoldsR R (k b) a

mutual
/-- `b`'s premises hold, with `Derives` for the recursive ones. -/
inductive Holds (rules : RuleSet ι α) : Body ι α → α → Prop where
  | ret (a : α) : Holds rules (.ret a) a
  | pay {k out} (h : Holds rules k out) : Holds rules (.pay k) out
  | cond {t c k out} (hc : c) (h : Holds rules k out) : Holds rules (.cond t c k) out
  | check {v P k out} (hP : P) (h : Holds rules k out) : Holds rules (.check v P k) out
  | call {i k a out} (ha : Derives rules i a) (h : Holds rules (k a) out) :
      Holds rules (.call i k) out
  | aux {g : Grade} {β : Type} {p : Nat → Lv β} {P : β → Prop} {k : β → Body ι α} {b out}
      (hb : P b) (h : Holds rules (k b) out) : Holds rules (.aux g p P k) out
/-- The relation generated by the rule set: some rule at `i` has all its premises. -/
inductive Derives (rules : RuleSet ι α) : ι → α → Prop where
  | intro {i b a} (hb : b ∈ rules i) (h : Holds rules b a) : Derives rules i a
end

/-- `HoldsR (Derives rules)` is `Holds rules`, in the direction soundness needs. -/
theorem holds_of_holdsR {rules : RuleSet ι α} :
    ∀ (b : Body ι α) (a : α), HoldsR (Derives rules) b a → Holds rules b a := by
  intro b
  induction b with
  | ret a' => intro a h; cases h; exact .ret _
  | fail => intro a h; exact h.elim
  | pay k ih => intro a h; exact .pay (ih a h)
  | cond t c k ih => intro a h; exact .cond h.1 (ih a h.2)
  | check v P k ih => intro a h; exact .check h.1 (ih a h.2)
  | call i k ih =>
      intro a h
      obtain ⟨x, hx, hk⟩ := h
      exact .call hx (ih x a hk)
  | aux g p P k ih =>
      intro a h
      obtain ⟨x, hx, hk⟩ := h
      exact .aux hx (ih x a hk)

/-! ## The graded denotation -/

/-- The graded enumeration a body denotes at leaf budget `L`, at the specification carrier. The *only*
place the `Grade` is read.

`denoteL` below is the same text at the value carrier; `agrees_denote` proves them level-wise equal,
so everything proved here transports to the enumeration that runs. -/
def denote (L : Nat) (rec : ι → SetE α) : Body ι α → SetE α
  | .ret a => Graded.single a
  | .fail => Choice.nothing
  | .pay k => Graded.pay (denote L rec k)
  | .cond t _ k => if t then denote L rec k else Choice.nothing
  | .check v _ k => Graded.gmap Prod.fst (GradedBind.guard (fun _ => v) (denote L rec k))
  | .call i k => GradedBind.bindC (rec i) (fun a => denote L rec (k a))
  | .aux .sized p _ k => GradedBind.bindC (specOf (p L)) (fun b => denote L rec (k b))
  | .aux .flat p _ k => GradedBind.bind (specOf (p L)) (fun b => denote L rec (k b))

/-- The same body at the **value** carrier: this is the enumeration that executes. -/
def denoteL (L : Nat) (rec : ι → Lv α) : Body ι α → Lv α
  | .ret a => Graded.single a
  | .fail => Choice.nothing
  | .pay k => Graded.pay (denoteL L rec k)
  | .cond t _ k => if t then denoteL L rec k else Choice.nothing
  | .check v _ k => Graded.gmap Prod.fst (GradedBind.guard (fun _ => v) (denoteL L rec k))
  | .call i k => GradedBind.bindC (rec i) (fun a => denoteL L rec (k a))
  | .aux .sized p _ k => GradedBind.bindC (p L) (fun b => denoteL L rec (k b))
  | .aux .flat p _ k => GradedBind.bind (p L) (fun b => denoteL L rec (k b))

@[simp] theorem denote_ret (L : Nat) (rec : ι → SetE α) (a : α) :
    denote L rec (.ret a) = Graded.single a := rfl
@[simp] theorem denote_fail (L : Nat) (rec : ι → SetE α) :
    denote L rec (.fail : Body ι α) = Choice.nothing := rfl
@[simp] theorem denote_pay (L : Nat) (rec : ι → SetE α) (k : Body ι α) :
    denote L rec (.pay k) = Graded.pay (denote L rec k) := rfl
@[simp] theorem denote_cond_true (L : Nat) (rec : ι → SetE α) (c : Prop) (k : Body ι α) :
    denote L rec (.cond true c k) = denote L rec k := by simp [denote]
@[simp] theorem denote_cond_false (L : Nat) (rec : ι → SetE α) (c : Prop) (k : Body ι α) :
    denote L rec (.cond false c k) = Choice.nothing := by simp [denote]
@[simp] theorem denote_call (L : Nat) (rec : ι → SetE α) (i : ι) (k : α → Body ι α) :
    denote L rec (.call i k) = GradedBind.bindC (rec i) (fun a => denote L rec (k a)) := rfl
@[simp] theorem denote_aux_sized (L : Nat) (rec : ι → SetE α) (p : Nat → Lv β) (P : β → Prop)
    (k : β → Body ι α) :
    denote L rec (.aux .sized p P k)
      = GradedBind.bindC (specOf (p L)) (fun b => denote L rec (k b)) := rfl
@[simp] theorem denote_aux_flat (L : Nat) (rec : ι → SetE α) (p : Nat → Lv β) (P : β → Prop)
    (k : β → Body ι α) :
    denote L rec (.aux .flat p P k)
      = GradedBind.bind (specOf (p L)) (fun b => denote L rec (k b)) := rfl

@[simp] theorem denoteL_ret (L : Nat) (rec : ι → Lv α) (a : α) :
    denoteL L rec (.ret a) = Graded.single a := rfl
@[simp] theorem denoteL_fail (L : Nat) (rec : ι → Lv α) :
    denoteL L rec (.fail : Body ι α) = Choice.nothing := rfl
@[simp] theorem denoteL_pay (L : Nat) (rec : ι → Lv α) (k : Body ι α) :
    denoteL L rec (.pay k) = Graded.pay (denoteL L rec k) := rfl
@[simp] theorem denoteL_cond_true (L : Nat) (rec : ι → Lv α) (c : Prop) (k : Body ι α) :
    denoteL L rec (.cond true c k) = denoteL L rec k := by simp [denoteL]
@[simp] theorem denoteL_cond_false (L : Nat) (rec : ι → Lv α) (c : Prop) (k : Body ι α) :
    denoteL L rec (.cond false c k) = Choice.nothing := by simp [denoteL]
@[simp] theorem denoteL_check (L : Nat) (rec : ι → Lv α) (v : V) (P : Prop) (k : Body ι α) :
    denoteL L rec (.check v P k)
      = Graded.gmap Prod.fst (GradedBind.guard (fun _ => v) (denoteL L rec k)) := rfl
@[simp] theorem denoteL_call (L : Nat) (rec : ι → Lv α) (i : ι) (k : α → Body ι α) :
    denoteL L rec (.call i k) = GradedBind.bindC (rec i) (fun a => denoteL L rec (k a)) := rfl
@[simp] theorem denoteL_aux_sized (L : Nat) (rec : ι → Lv α) (p : Nat → Lv β) (P : β → Prop)
    (k : β → Body ι α) :
    denoteL L rec (.aux .sized p P k) = GradedBind.bindC (p L) (fun b => denoteL L rec (k b)) := rfl
@[simp] theorem denoteL_aux_flat (L : Nat) (rec : ι → Lv α) (p : Nat → Lv β) (P : β → Prop)
    (k : β → Body ι α) :
    denoteL L rec (.aux .flat p P k) = GradedBind.bind (p L) (fun b => denoteL L rec (k b)) := rfl

/-- A `check` premise filters. The `inconclusive` verdict *survives* — that is `guard`'s contract —
so an inconclusive verdict is only sound where the proposition actually holds, which is exactly the
obligation `BodySound` imposes below. -/
@[simp] theorem denote_check_apply (L : Nat) (rec : ι → SetE α) (v : V) (P : Prop) (k : Body ι α)
    (n : Nat) (a : α) :
    denote L rec (.check v P k) n a ↔ (v ≠ .no ∧ denote L rec k n a) := by
  show (Graded.gmap Prod.fst (GradedBind.guard (fun _ => v) (denote L rec k)) : SetE α) n a ↔ _
  simp only [SetE.gmap_apply, SetE.guard_apply]
  cases v with
  | yes =>
      constructor
      · rintro ⟨q, ⟨h1, -⟩, rfl⟩; exact ⟨by simp, h1⟩
      · rintro ⟨-, h⟩; exact ⟨(a, true), ⟨h, rfl⟩, rfl⟩
  | inconclusive =>
      constructor
      · rintro ⟨q, ⟨h1, -⟩, rfl⟩; exact ⟨by simp, h1⟩
      · rintro ⟨-, h⟩; exact ⟨(a, false), ⟨h, rfl⟩, rfl⟩
  | no =>
      constructor
      · rintro ⟨q, ⟨-, hf⟩, -⟩; exact hf.elim
      · rintro ⟨hv, -⟩; exact absurd rfl hv

/-! ## Well-formedness of a rule set

Predicates on bodies, each carrying only what its theorem needs. The asymmetry is the point:
**`BodySound` does not mention the `Grade` at all** — a mis-graded rule set is still sound, so no
soundness theorem can catch the bug. `BodyComplete` is where the choice is discharged. -/

/-- The producer only offers values the premise admits, at every budget. -/
def Sound (p : Nat → Lv β) (P : β → Prop) : Prop := ∀ L n b, b ∈ p L n → P b
/-- The producer offers each admissible value at *some* budget and *some* level. What `bindC`
needs. -/
def Covers (p : Nat → Lv β) (P : β → Prop) : Prop := ∀ b, P b → ∃ L n, b ∈ p L n
/-- The producer offers each admissible value, from some budget on, at *every* level. What `bind`
needs — and what fails for any producer whose output carries its own size.

Quantifying the budget existentially (rather than demanding availability at budget 0, where a
`gradedIter` leaf is empty) is what keeps the refutation below honest: `not_unsized_typeProd` does not
win by pointing at an unfunded leaf, it wins because `Nat` is at type-level 0 and nowhere else. -/
def Unsized (p : Nat → Lv β) (P : β → Prop) : Prop :=
  ∀ b, P b → ∃ L, ∀ L', L ≤ L' → ∀ n, b ∈ p L' n
/-- A bigger leaf budget never loses a value. What lets premises found at different budgets be raised
to a common one — the leaf-side counterpart of `enum_le`. -/
def MonoL (p : Nat → Lv β) : Prop := ∀ L L', L ≤ L' → ∀ n b, b ∈ p L n → b ∈ p L' n

/-! ### Budget-independent producers

Most real leaves do not vary with the budget — Cedar's `schemaEnum`/`recordEnum` walk a finite `Map`, and
nothing about them grows. `constP` lifts such a producer into the indexed form, and the four obligations
then reduce to their single-producer statements, with `MonoL` free. This is what keeps a rule set whose
leaves are all budget-independent from having to mention budgets at all. -/

/-- A producer that ignores the budget. -/
def constP (p : Lv β) : Nat → Lv β := fun _ => p

@[simp] theorem constP_apply (p : Lv β) (L : Nat) : constP p L = p := rfl

/-- `constP_apply` at full application. Since Lean v4.34 `simp` does not rewrite the partial application
`constP p L` inside `constP p L n`, so the saturated form needs its own lemma. -/
@[simp] theorem constP_apply₂ (p : Lv β) (L n : Nat) : constP p L n = p n := rfl

theorem monoL_constP (p : Lv β) : MonoL (constP p) := fun _ _ _ _ _ h => h

theorem sound_constP {p : Lv β} {P : β → Prop} (h : ∀ n b, b ∈ p n → P b) :
    Sound (constP p) P := fun _ n b hb => h n b hb

theorem covers_constP {p : Lv β} {P : β → Prop} (h : ∀ b, P b → ∃ n, b ∈ p n) :
    Covers (constP p) P := fun b hb => let ⟨n, hn⟩ := h b hb; ⟨0, n, hn⟩

/-- For a budget-independent producer, `Unsized` is exactly "reached at every level" — the budget
quantifier collapses because there is nothing for it to range over. -/
theorem unsized_constP {p : Lv β} {P : β → Prop} (h : ∀ b, P b → ∀ n, b ∈ p n) :
    Unsized (constP p) P := fun b hb => ⟨0, fun _ _ n => h b hb n⟩

/-- `bind` is the strictly stronger demand. It is satisfiable — a producer replicated at every level
is exactly what a premise "delegated on the undivided budget" looks like — but not by a sized leaf. -/
theorem covers_of_unsized {p : Nat → Lv β} {P : β → Prop} (h : Unsized p P) : Covers p P :=
  fun b hb => let ⟨L, hL⟩ := h b hb; ⟨L, 0, hL L (Nat.le_refl L) 0⟩

/-- The level- and budget-agnostic producer: the canonical `.flat` premise, and a witness that
`Unsized` is not vacuous. -/
theorem unsized_const (P : β → Prop) (l : List β) (hl : ∀ b, P b → b ∈ l) :
    Unsized (fun _ _ => l) P := fun b hb => ⟨0, fun _ _ _ => hl b hb⟩

/-- …and it is monotone in the budget for free. -/
theorem monoL_const (l : Nat → List β) : MonoL (fun _ => l) := fun _ _ _ _ _ h => h

/-- What soundness needs of a body: every test is a *sound* decision of the premise it claims to
decide, and every auxiliary producer only offers admissible values. Grading-blind. -/
def BodySound : Body ι α → Prop
  | .ret _ => True
  | .fail => True
  | .pay k => BodySound k
  | .cond t c k => (t = true → c) ∧ BodySound k
  | .check v P k => (v ≠ .no → P) ∧ BodySound k
  | .call _ k => ∀ a, BodySound (k a)
  | .aux _ p P k => Sound p P ∧ ∀ b, BodySound (k b)

/-- What completeness needs of a body: every test is a *complete* decision, every auxiliary producer
is monotone in the leaf budget, and — the point of the exercise — each producer satisfies the coverage
law appropriate to **its declared grade**. -/
def BodyComplete : Body ι α → Prop
  | .ret _ => True
  | .fail => True
  | .pay k => BodyComplete k
  | .cond t c k => (c → t = true) ∧ BodyComplete k
  | .check v P k => (P → v ≠ .no) ∧ BodyComplete k
  | .call _ k => ∀ a, BodyComplete (k a)
  | .aux .sized p P k => MonoL p ∧ Covers p P ∧ ∀ b, BodyComplete (k b)
  | .aux .flat p P k => MonoL p ∧ Unsized p P ∧ ∀ b, BodyComplete (k b)

/-- Budget-monotonicity alone, which is what the level arithmetic needs before either coverage law is
in play. It is not a separate obligation on a rule set: `bodyMono_of_complete` extracts it from
`BodyComplete`, so `adequate` still asks for exactly four things. -/
def BodyMono : Body ι α → Prop
  | .ret _ => True
  | .fail => True
  | .pay k => BodyMono k
  | .cond _ _ k => BodyMono k
  | .check _ _ k => BodyMono k
  | .call _ k => ∀ a, BodyMono (k a)
  | .aux _ p _ k => MonoL p ∧ ∀ b, BodyMono (k b)

/-- So `MonoL` is never an extra hypothesis anywhere. -/
theorem bodyMono_of_complete : ∀ b : Body ι α, BodyComplete b → BodyMono b := by
  intro b
  induction b with
  | ret a => intro _; exact trivial
  | fail => intro _; exact trivial
  | pay k ih => intro h; exact ih h
  | cond t c k ih => intro h; exact ih h.2
  | check v P k ih => intro h; exact ih h.2
  | call i k ih => intro h; exact fun a => ih a (h a)
  | aux g p P k ih =>
      intro h
      cases g
      · exact ⟨h.1, fun b => ih b (h.2.2 b)⟩
      · exact ⟨h.1, fun b => ih b (h.2.2 b)⟩

/-! ## The step and its iteration

A level is a count of rule applications, but `pay` is now *inside* a body rather than wrapped around
every rule by `stepOf`, so a rule with no recursive premise costs nothing — which is what the
hand-written `stlcAFStep` does and what the bridge needs. -/

/-- Finite union of the alternatives at an index. Generic over the carrier, so the value and
specification steps are the same function. -/
def unionAll {f : Type → Type} [Choice f] : List (f α) → f α :=
  List.foldr Choice.union Choice.nothing

theorem unionAll_apply (xs : List (SetE α)) (n : Nat) (a : α) :
    unionAll xs n a ↔ ∃ x ∈ xs, x n a := by
  induction xs with
  | nil => simp [unionAll]
  | cons x xs ih => simp only [unionAll, List.foldr_cons] at *; simp [SetE.union_apply, ih]

/-- One unfolding of the whole relation at leaf budget `L`: every rule at the index. -/
def stepOf (rules : RuleSet ι α) (L : Nat) (rec : ι → SetE α) (i : ι) : SetE α :=
  unionAll ((rules i).map (denote L rec))

/-- The enumeration family the rule set denotes at leaf budget `L`, closed at `l` iterations. -/
abbrev enum (rules : RuleSet ι α) (L l : Nat) : ι → SetE α := gradedIterIx (stepOf rules L) l

/-- The same at the value carrier: the family that executes. -/
def stepOfL (rules : RuleSet ι α) (L : Nat) (rec : ι → Lv α) (i : ι) : Lv α :=
  unionAll ((rules i).map (denoteL L rec))

/-- The enumeration that runs, closed at `l` iterations. -/
abbrev enumL (rules : RuleSet ι α) (L l : Nat) : ι → Lv α := gradedIterIx (stepOfL rules L) l

theorem stepOf_apply (rules : RuleSet ι α) (L : Nat) (rec : ι → SetE α) (i : ι) (n : Nat) (a : α) :
    stepOf rules L rec i n a ↔ ∃ b ∈ rules i, denote L rec b n a := by
  simp only [stepOf, unionAll_apply, List.mem_map]
  constructor
  · rintro ⟨x, ⟨b, hb, rfl⟩, hx⟩; exact ⟨b, hb, hx⟩
  · rintro ⟨b, hb, hx⟩; exact ⟨_, ⟨b, hb, rfl⟩, hx⟩

/-! ## Monotonicity, in the iteration count *and* the leaf budget

Assembled from `GradedSound`'s `SubE` closure lemmas; `bind` and `guard` are the two cases that
development did not need and so does not have. The budget leg (`denote_monoL`, `enum_leL`) is what the
existentially quantified leaf budget costs, and it is one extra structural induction. -/

theorem SubE.bindF {x s : SetE β} {k h : β → SetE α} (hx : SubE x s) (hk : ∀ b, SubE (k b) (h b)) :
    SubE (GradedBind.bind x k) (GradedBind.bind s h) := by
  intro n a ha
  simp only [SetE.bind_apply] at ha ⊢
  obtain ⟨b, hb, hkb⟩ := ha
  exact ⟨b, hx n b hb, hk b n a hkb⟩

theorem SubE.guardF {x s : SetE β} (p : β → V) (hx : SubE x s) :
    SubE (GradedBind.guard p x) (GradedBind.guard p s) := by
  intro n q hq
  simp only [SetE.guard_apply] at hq ⊢
  exact ⟨hx n q.1 hq.1, hq.2⟩

theorem denote_mono (L : Nat) {x y : ι → SetE α} (h : SubIxE x y) :
    ∀ b : Body ι α, SubE (denote L x b) (denote L y b) := by
  intro b
  induction b with
  | ret a => exact SubE.refl _
  | fail => exact SubE.refl _
  | pay k ih => exact ih.pay
  | cond t c k ih => cases t <;> simp only [denote_cond_true, denote_cond_false]
                     · exact SubE.refl _
                     · exact ih
  | check v P k ih => exact SubE.gmap _ (SubE.guardF _ ih)
  | call i k ih => exact SubE.bindC (h i) (fun a => ih a)
  | aux g p P k ih =>
      cases g
      · exact SubE.bindC (SubE.refl _) (fun b => ih b)
      · exact SubE.bindF (SubE.refl _) (fun b => ih b)

theorem subE_specOf_of_monoL {p : Nat → Lv β} (hm : MonoL p) {L L' : Nat} (hL : L ≤ L') :
    SubE (specOf (p L)) (specOf (p L')) := fun n b h => hm L L' hL n b h

theorem denote_monoL {L L' : Nat} (hL : L ≤ L') {rec : ι → SetE α} :
    ∀ b : Body ι α, BodyMono b → SubE (denote L rec b) (denote L' rec b) := by
  intro b
  induction b with
  | ret a => intro _; exact SubE.refl _
  | fail => intro _; exact SubE.refl _
  | pay k ih => intro hm; exact (ih hm).pay
  | cond t c k ih =>
      intro hm
      cases t
      · simp only [denote_cond_false]; exact SubE.refl _
      · simp only [denote_cond_true]; exact ih hm
  | check v P k ih => intro hm; exact SubE.gmap _ (SubE.guardF _ (ih hm))
  | call i k ih => intro hm; exact SubE.bindC (SubE.refl _) (fun a => ih a (hm a))
  | aux g p P k ih =>
      intro hm
      cases g
      · exact SubE.bindC (subE_specOf_of_monoL hm.1 hL) (fun b => ih b (hm.2 b))
      · exact SubE.bindF (subE_specOf_of_monoL hm.1 hL) (fun b => ih b (hm.2 b))

theorem stepOf_mono (rules : RuleSet ι α) (L : Nat) {x y : ι → SetE α} (h : SubIxE x y) :
    SubIxE (stepOf rules L x) (stepOf rules L y) := by
  intro i n a ha
  rw [stepOf_apply] at ha ⊢
  obtain ⟨b, hb, hd⟩ := ha
  exact ⟨b, hb, denote_mono L h b n a hd⟩

theorem stepOf_monoL {rules : RuleSet ι α} (hmono : ∀ i, ∀ b ∈ rules i, BodyMono b)
    {L L' : Nat} (hL : L ≤ L') (rec : ι → SetE α) :
    SubIxE (stepOf rules L rec) (stepOf rules L' rec) := by
  intro i n a ha
  rw [stepOf_apply] at ha ⊢
  obtain ⟨b, hb, hd⟩ := ha
  exact ⟨b, hb, denote_monoL hL b (hmono i b hb) n a hd⟩

theorem enum_le {rules : RuleSet ι α} (L : Nat) {l l' : Nat} (hl : l ≤ l') :
    SubIxE (enum rules L l) (enum rules L l') :=
  subIxE_gradedIterIx_le (fun _ _ h => stepOf_mono rules L h) hl

theorem enum_leL {rules : RuleSet ι α} (hmono : ∀ i, ∀ b ∈ rules i, BodyMono b)
    {L L' : Nat} (hL : L ≤ L') : ∀ l, SubIxE (enum rules L l) (enum rules L' l)
  | 0 => fun _ => subE_nothing _
  | l + 1 => fun i n a ha =>
      stepOf_monoL hmono hL (enum rules L' l) i n a
        (stepOf_mono rules L (enum_leL hmono hL l) i n a ha)

/-- Raise the leaf budget and the iteration count at once: the bump the completeness induction needs
to put sub-results found at different budgets onto a common one. -/
theorem enum_bump {rules : RuleSet ι α} (hmono : ∀ i, ∀ b ∈ rules i, BodyMono b)
    {L L' l l' : Nat} (hL : L ≤ L') (hl : l ≤ l') :
    SubIxE (enum rules L l) (enum rules L' l') := fun i =>
  SubE.trans (enum_leL hmono hL l i) (enum_le L' hl i)

/-! ## Soundness, generically

Everything the enumeration produces satisfies any relation the rules are valid for. No hypothesis
about the `Grade`s: they are invisible here, which is the file's thesis stated as an absence. -/

theorem denote_soundR {R : ι → α → Prop} {L : Nat} {rec : ι → SetE α}
    (hrec : ∀ i n a, rec i n a → R i a) :
    ∀ (b : Body ι α), BodySound b → ∀ n a, denote L rec b n a → HoldsR R b a := by
  intro b
  induction b with
  | ret a' =>
      intro _ n a h
      simp only [denote_ret, SetE.single_apply] at h
      exact h.2
  | fail => intro _ n a h; exact absurd h (by simp)
  | pay k ih =>
      intro hwf n a h
      cases n with
      | zero => exact absurd h (by simp)
      | succ m =>
          simp only [denote_pay, SetE.pay_succ] at h
          exact ih hwf m a h
  | cond t c k ih =>
      intro hwf n a h
      cases t
      · simp only [denote_cond_false] at h; exact absurd h (by simp)
      · simp only [denote_cond_true] at h
        exact ⟨hwf.1 rfl, ih hwf.2 n a h⟩
  | check v P k ih =>
      intro hwf n a h
      rw [denote_check_apply] at h
      exact ⟨hwf.1 h.1, ih hwf.2 n a h.2⟩
  | call i k ih =>
      intro hwf n a h
      simp only [denote_call, SetE.bindC_apply] at h
      obtain ⟨j, -, x, hx, hk⟩ := h
      exact ⟨x, hrec i j x hx, ih x (hwf x) (n - j) a hk⟩
  | aux g p P k ih =>
      intro hwf n a h
      cases g
      · simp only [denote_aux_sized, SetE.bindC_apply] at h
        obtain ⟨j, -, x, hx, hk⟩ := h
        exact ⟨x, hwf.1 L j x hx, ih x (hwf.2 x) (n - j) a hk⟩
      · simp only [denote_aux_flat, SetE.bind_apply] at h
        obtain ⟨x, hx, hk⟩ := h
        exact ⟨x, hwf.1 L n x hx, ih x (hwf.2 x) n a hk⟩

/-- **Generic soundness.** If every rule is sound (its tests really decide their premises, its
auxiliary producers really produce what they claim) and `R` is closed under the rules, then nothing
the enumeration produces is outside `R` — at any leaf budget, iteration count, index or level. -/
theorem soundR {rules : RuleSet ι α} {R : ι → α → Prop}
    (hs : ∀ i, ∀ b ∈ rules i, BodySound b)
    (hvalid : ∀ i, ∀ b ∈ rules i, ∀ a, HoldsR R b a → R i a) :
    ∀ (L l : Nat) (i : ι) (n : Nat) (a : α), enum rules L l i n a → R i a := by
  intro L l
  induction l with
  | zero => intro i n a h; exact absurd h (by simp [gradedIterIx])
  | succ l ih =>
      intro i n a h
      replace h : stepOf rules L (enum rules L l) i n a := h
      rw [stepOf_apply] at h
      obtain ⟨b, hb, hd⟩ := h
      exact hvalid i b hb a
        (denote_soundR (fun i n a h => ih i n a h) b (hs i b hb) n a hd)

/-- Soundness against the relation the rules *generate*, which is the least such `R`. -/
theorem sound {rules : RuleSet ι α} (hs : ∀ i, ∀ b ∈ rules i, BodySound b) :
    ∀ (L l : Nat) (i : ι) (n : Nat) (a : α), enum rules L l i n a → Derives rules i a :=
  soundR hs (fun _ b hb a h => .intro hb (holds_of_holdsR b a h))

/-! ## Completeness, generically

The direction that reads the `Grade`s. Induction on the derivation; the leaf budget and the iteration
count are raised to a common pair with `enum_bump` and `denote_monoL`. -/

/-- **Generic completeness.** Every derivation of the rule set is enumerated — at some leaf budget,
some iteration count and some level.

The per-premise obligations sit in `BodyComplete`, and for an `aux` premise they are exactly the
distinction the deriver has to get right: `Covers` for `.sized`, `Unsized` for `.flat`. -/
theorem complete {rules : RuleSet ι α} (hc : ∀ i, ∀ b ∈ rules i, BodyComplete b) :
    ∀ {i : ι} {a : α}, Derives rules i a → ∃ L l n, enum rules L l i n a := by
  have hmono : ∀ i, ∀ b ∈ rules i, BodyMono b :=
    fun i b hb => bodyMono_of_complete b (hc i b hb)
  intro i a h
  refine @Derives.rec ι α rules
    (fun b out _ => BodyComplete b → ∃ L l n, denote L (enum rules L l) b n out)
    (fun i out _ => ∃ L l n, enum rules L l i n out)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ i a h
  -- `ret`
  · intro a' _
    exact ⟨0, 0, 0, by simp⟩
  -- `pay`
  · intro k out _ ih hwf
    obtain ⟨L, l, n, hn⟩ := ih hwf
    exact ⟨L, l, n + 1, by simpa using hn⟩
  -- `cond`
  · intro t c k out hcc _ ih hwf
    obtain ⟨L, l, n, hn⟩ := ih hwf.2
    rw [hwf.1 hcc]
    exact ⟨L, l, n, by simpa using hn⟩
  -- `check`
  · intro v P k out hP _ ih hwf
    obtain ⟨L, l, n, hn⟩ := ih hwf.2
    exact ⟨L, l, n, by rw [denote_check_apply]; exact ⟨hwf.1 hP, hn⟩⟩
  -- `call`
  · intro i' k a' out _ _ ihD ihH hwf
    obtain ⟨L₁, l₁, n₁, h₁⟩ := ihD
    obtain ⟨L₂, l₂, n₂, h₂⟩ := ihH (hwf a')
    refine ⟨max L₁ L₂, max l₁ l₂, n₁ + n₂, ?_⟩
    simp only [denote_call, SetE.bindC_apply]
    refine ⟨n₁, by omega, a',
      enum_bump hmono (Nat.le_max_left _ _) (Nat.le_max_left _ _) i' n₁ a' h₁, ?_⟩
    have harith : n₁ + n₂ - n₁ = n₂ := by omega
    rw [harith]
    exact SubE.trans
      (denote_monoL (Nat.le_max_right L₁ L₂) (k a') (bodyMono_of_complete _ (hwf a')))
      (denote_mono _ (enum_bump hmono (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (k a'))
      n₂ out h₂
  -- `aux`
  · intro g β p P k b out hb _ ih hwf
    cases g
    · obtain ⟨L₁, n₁, h₁⟩ := hwf.2.1 b hb
      obtain ⟨L₂, l, n₂, h₂⟩ := ih (hwf.2.2 b)
      refine ⟨max L₁ L₂, l, n₁ + n₂, ?_⟩
      simp only [denote_aux_sized, SetE.bindC_apply]
      refine ⟨n₁, by omega, b, hwf.1 L₁ _ (Nat.le_max_left _ _) n₁ b h₁, ?_⟩
      have harith : n₁ + n₂ - n₁ = n₂ := by omega
      rw [harith]
      exact SubE.trans
        (denote_monoL (Nat.le_max_right L₁ L₂) (k b) (bodyMono_of_complete _ (hwf.2.2 b)))
        (denote_mono _ (enum_leL hmono (Nat.le_max_right L₁ L₂) l) (k b))
        n₂ out h₂
    · obtain ⟨L₁, hL₁⟩ := hwf.2.1 b hb
      obtain ⟨L₂, l, n₂, h₂⟩ := ih (hwf.2.2 b)
      refine ⟨max L₁ L₂, l, n₂, ?_⟩
      simp only [denote_aux_flat, SetE.bind_apply]
      refine ⟨b, hL₁ _ (Nat.le_max_left _ _) n₂, ?_⟩
      exact SubE.trans
        (denote_monoL (Nat.le_max_right L₁ L₂) (k b) (bodyMono_of_complete _ (hwf.2.2 b)))
        (denote_mono _ (enum_leL hmono (Nat.le_max_right L₁ L₂) l) (k b))
        n₂ out h₂
  -- the rule application itself
  · intro i' b a' hb _ ih
    obtain ⟨L, l, n, hn⟩ := ih (hc i' b hb)
    refine ⟨L, l + 1, n, ?_⟩
    show stepOf rules L (enum rules L l) i' n a'
    rw [stepOf_apply]
    exact ⟨b, hb, hn⟩

/-! ## Transport to the carrier that runs

Nothing here is restated from `GradedSound.lean`: the value and specification denotations are the same
text, so their agreement is assembled from `Agrees.union`/`.pay`/`.gmap`/`.bind`/`.bindC`/`.guard` and
lifted by `agrees_gradedIterIx`. -/

theorem agrees_unionAll_map {bs : List (Body ι α)} {fL : Body ι α → Lv α} {fS : Body ι α → SetE α}
    (h : ∀ b, Agrees (fL b) (fS b)) : Agrees (unionAll (bs.map fL)) (unionAll (bs.map fS)) := by
  induction bs with
  | nil => exact agrees_nothing
  | cons b bs ih => exact (h b).union ih

theorem agrees_denote (L : Nat) {recL : ι → Lv α} {recS : ι → SetE α} (h : AgreesIx recL recS) :
    ∀ b : Body ι α, Agrees (denoteL L recL b) (denote L recS b) := by
  intro b
  induction b with
  | ret a => exact agrees_single a
  | fail => exact agrees_nothing
  | pay k ih => exact ih.pay
  | cond t c k ih =>
      cases t
      · simp only [denote_cond_false, denoteL_cond_false]; exact agrees_nothing
      · simp only [denote_cond_true, denoteL_cond_true]; exact ih
  | check v P k ih => exact (ih.guard (fun _ => v)).gmap Prod.fst
  | call i k ih => exact (h i).bindC (fun a => ih a)
  | aux g p P k ih =>
      cases g
      · exact (agrees_specOf (p L)).bindC (fun b => ih b)
      · exact (agrees_specOf (p L)).bind (fun b => ih b)

theorem agrees_stepOf {rules : RuleSet ι α} (L : Nat) {recL : ι → Lv α} {recS : ι → SetE α}
    (h : AgreesIx recL recS) : AgreesIx (stepOfL rules L recL) (stepOf rules L recS) :=
  fun _ => agrees_unionAll_map (fun b => agrees_denote L h b)

/-- The enumeration that runs and the one the theorems are about have the same levels, at every leaf
budget, index and iteration count. -/
theorem agrees_enum (rules : RuleSet ι α) (L l : Nat) :
    AgreesIx (enumL rules L l) (enum rules L l) :=
  agrees_gradedIterIx (fun _ _ h => agrees_stepOf L h) l

/-! ## The generic adequacy theorem -/

/-- **Adequacy, once and for all.** For a rule set that is sound and complete premise-by-premise, and
a relation `R` that the rules are valid for and that the rules generate, `R` *is* the graded
enumeration folded over leaf budgets, iteration counts and levels.

`hvalid` is the easy half of "the rules present `R`": one constructor application per rule. `hgen` is
the other half, proved at an instance by induction on `R`'s own derivation. Neither mentions grading;
`hs`/`hc` mention nothing else. -/
theorem adequate {rules : RuleSet ι α} {R : ι → α → Prop}
    (hs : ∀ i, ∀ b ∈ rules i, BodySound b)
    (hc : ∀ i, ∀ b ∈ rules i, BodyComplete b)
    (hvalid : ∀ i, ∀ b ∈ rules i, ∀ a, HoldsR R b a → R i a)
    (hgen : ∀ i a, R i a → Derives rules i a)
    (i : ι) (a : α) : R i a ↔ ∃ L l n, enum rules L l i n a :=
  ⟨fun h => complete hc (hgen i a h), fun ⟨L, l, n, h⟩ => soundR hs hvalid L l i n a h⟩

/-- **Adequacy for the enumeration that actually runs.** Same hypotheses; the statement is membership
in a level of the value enumeration. -/
theorem adequateL {rules : RuleSet ι α} {R : ι → α → Prop}
    (hs : ∀ i, ∀ b ∈ rules i, BodySound b)
    (hc : ∀ i, ∀ b ∈ rules i, BodyComplete b)
    (hvalid : ∀ i, ∀ b ∈ rules i, ∀ a, HoldsR R b a → R i a)
    (hgen : ∀ i a, R i a → Derives rules i a)
    (i : ι) (a : α) : R i a ↔ ∃ L l n, a ∈ enumL rules L l i n := by
  rw [adequate hs hc hvalid hgen i a]
  exact ⟨fun ⟨L, l, n, h⟩ => ⟨L, l, n, (agrees_enum rules L l i n a).mpr h⟩,
         fun ⟨L, l, n, h⟩ => ⟨L, l, n, (agrees_enum rules L l i n a).mp h⟩⟩

/-! ## Reconciling a premise list with a hand-written step function

Three equalities, and they are the whole reason `Body` needs no product and no map constructor: a
`bindC` whose continuation returns immediately *is* a `gmap`, and two nested ones *are* a `pair`. The
splits `bindC` offers are forced by the `ret`'s demand that no level be left over. -/

theorem setE_ext {x y : SetE α} (h : ∀ n a, x n a ↔ y n a) : x = y := by
  funext n a; exact propext (h n a)

/-- A `bindC` whose continuation returns immediately is a `gmap`: `i ≤ n` together with `n - i = 0`
forces `i = n`, so no budget is actually split. -/
theorem bindC_ret {γ : Type} (x : SetE β) (f : β → γ) :
    (GradedBind.bindC x (fun v => Graded.single (f v)) : SetE γ) = Graded.gmap f x := by
  refine setE_ext fun n c => ?_
  simp only [SetE.bindC_apply, SetE.single_apply, SetE.gmap_apply]
  constructor
  · rintro ⟨i, hi, v, hv, hz, he⟩
    have hin : i = n := by omega
    subst hin
    exact ⟨v, hv, he.symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨n, Nat.le_refl n, v, hv, by omega, rfl⟩

/-- Two nested `bindC`s ending in a `ret` are exactly `pair` followed by `gmap`: the two splits are
forced to `i + j = n`. This is why a premise list needs no product operation. -/
theorem bindC_bindC_ret {γ δ : Type} (x : SetE β) (y : SetE γ) (g : β → γ → δ) :
    (GradedBind.bindC x (fun v => GradedBind.bindC y (fun w => Graded.single (g v w))) : SetE δ)
      = Graded.gmap (fun p : β × γ => g p.1 p.2) (Graded.pair x y) := by
  refine setE_ext fun n d => ?_
  simp only [SetE.bindC_apply, SetE.single_apply, SetE.gmap_apply, SetE.pair_apply]
  constructor
  · rintro ⟨i, hi, v, hv, j, hj, w, hw, hz, he⟩
    refine ⟨(v, w), ⟨i, hi, hv, ?_⟩, he.symm⟩
    have hji : j = n - i := by omega
    subst hji
    exact hw
  · rintro ⟨p, ⟨i, hi, h1, h2⟩, rfl⟩
    exact ⟨i, hi, p.1, h1, n - i, Nat.le_refl _, p.2, h2, by omega, rfl⟩

end RuleShape

/-! # The instance: STLC's full five-rule `typing`

Every constructor of the datatype is exercised: `cond` by `TConst`/`TAdd` (the conclusion pins
`τ = Nat`), `fail` by `TAbs` at a non-function type (the erasure of a failed `.Match`), `check` by
`TVar` (generate-and-check, the mode a deriver falls back to when a premise cannot be run as a
producer), `pay` by `TAdd`/`TAbs`/`TApp` and — deliberately — *not* by `TVar`/`TConst`, `call` by
`TAdd`/`TAbs`/`TApp`, `aux .sized` by the numeral leaf, the variable leaf and `TApp`'s existentially
quantified `τ₁`.

The rule set is parameterised by the `Grade` of `TApp`'s type premise, so that the *relational* facts
(`hvalid`, `derives_of_typing`) are proved once for both the right and the wrong choice — they cannot
see the grade, which is the whole point.

Every leaf here is one of `GradedStlcTest`'s own: `natProd`/`typeProd` are literally
`gradedIter natStep`/`gradedIter typeStep`, so the rule data denotes the hand-written enumerator and
not a look-alike. -/

namespace RuleShape.Stlc

open RuleShape

/-- The enumeration index: context and goal type are inputs, the term is the output. -/
abbrev Ix := TyIx

/-! ### The three leaves, as executable budget-indexed enumerations

Each is a family `Nat → Lv _`, and the only obligations any of them has to meet are `Sound`, `Covers`
and `MonoL` — all three inherited from lemmas `GradedStlcAdequacy.lean` already proved. -/

/-- The de Bruijn-index leaf for `TVar`'s generate-and-check mode: level `n` is the singleton `[n]`,
independent of the leaf budget. -/
def idProd : Nat → Lv Nat := fun _ n => [n]

/-- The numeral leaf at budget `L`: literally `GradedStlcTest`'s `natStep` fixed point. -/
def natProd : Nat → Lv Nat := fun L => gradedIter natStep L

/-- The type leaf at budget `L`: literally `GradedStlcTest`'s `typeStep` fixed point. -/
def typeProd : Nat → Lv type := fun L => gradedIter typeStep L

/-- The specification the numeral leaf's *code* has is the one the hand-written development named.
This, and its type counterpart, are what make the bridge an equality rather than a simulation. -/
theorem specOf_natProd (L : Nat) : specOf (natProd L) = natAt L :=
  specOf_eq_of_agrees (agrees_nat L)

theorem specOf_typeProd (L : Nat) : specOf (typeProd L) = tyAt L :=
  specOf_eq_of_agrees (agrees_type L)

theorem sound_idProd : Sound idProd (fun _ : Nat => True) := fun _ _ _ _ => trivial
theorem covers_idProd : Covers idProd (fun _ : Nat => True) :=
  fun x _ => ⟨0, x, by simp [idProd]⟩
theorem monoL_idProd : MonoL idProd := fun _ _ _ _ _ h => h

theorem sound_natProd : Sound natProd (fun _ : Nat => True) := fun _ _ _ _ => trivial
theorem covers_natProd : Covers natProd (fun _ : Nat => True) := by
  intro k _
  obtain ⟨L, n, h⟩ := natAt_reaches k
  exact ⟨L, n, (agrees_nat L n k).mpr h⟩
theorem monoL_natProd : MonoL natProd := by
  intro L L' hL n k h
  exact (agrees_nat L' n k).mpr (natAt_le hL n k ((agrees_nat L n k).mp h))

theorem sound_typeProd : Sound typeProd (fun _ : type => True) := fun _ _ _ _ => trivial
theorem covers_typeProd : Covers typeProd (fun _ : type => True) := by
  intro τ _
  obtain ⟨L, n, h⟩ := tyAt_reaches τ
  exact ⟨L, n, (agrees_type L n τ).mpr h⟩
theorem monoL_typeProd : MonoL typeProd := by
  intro L L' hL n τ h
  exact (agrees_type L' n τ).mpr (tyAt_le hL n τ ((agrees_type L n τ).mp h))

/-! ### `lookupEnum`, characterised

`lookupEnum` grades a variable by *its own de Bruijn index*. That is the fact that makes generate-and-
check equal to the direct producer, and hence the fact that lets the `check` constructor appear in the
rule data without the bridge losing equality. -/

/-- The de Bruijn-index producer is *graded by the index*: level `n` holds `x` exactly when `x = n`
and `Γ` really holds `τ` at `x`. This is what makes generate-and-check equal to it. -/
theorem mem_lookupEnum_iff : ∀ (Γ : List type) (τ : type) (n x : Nat),
    (lookupEnum Γ τ : SetE Nat) n x ↔ (x = n ∧ lookup Γ x τ) := by
  intro Γ
  induction Γ with
  | nil =>
      intro τ n x
      constructor
      · intro h; exact absurd h (by simp [lookupEnum])
      · rintro ⟨-, h⟩; cases h
  | cons σ Γ ih =>
      intro τ n x
      simp only [lookupEnum, SetE.union_apply]
      constructor
      · rintro (h | h)
        · by_cases hst : σ = τ
          · rw [ite_eq_left hst] at h
            simp only [SetE.single_apply] at h
            obtain ⟨hn, hx⟩ := h
            subst hn; subst hx; subst hst
            exact ⟨rfl, lookup.Now _ _⟩
          · rw [ite_eq_right hst] at h; exact absurd h (by simp)
        · cases n with
          | zero => exact absurd h (by simp)
          | succ m =>
              simp only [SetE.pay_succ, SetE.gmap_apply] at h
              obtain ⟨y, hy, hxy⟩ := h
              obtain ⟨rfl, hl⟩ := (ih τ m y).mp hy
              subst hxy
              exact ⟨rfl, lookup.Later τ σ y Γ hl⟩
      · rintro ⟨rfl, hl⟩
        cases hl with
        | Now =>
            refine Or.inl ?_
            rw [ite_eq_left rfl]
            simp
        | Later _ _ y _ hl' =>
            refine Or.inr ?_
            simp only [SetE.pay_succ, SetE.gmap_apply]
            exact ⟨y, (ih _ y y).mpr ⟨rfl, hl'⟩, rfl⟩

/-- A decidable `lookup`, to serve as the `check` premise's Kleene verdict. -/
def lookupB : List type → Nat → type → Bool
  | [], _, _ => false
  | σ :: _, 0, τ => decide (σ = τ)
  | _ :: Γ, x + 1, τ => lookupB Γ x τ

theorem lookupB_iff : ∀ (Γ : List type) (x : Nat) (τ : type),
    lookupB Γ x τ = true ↔ lookup Γ x τ := by
  intro Γ
  induction Γ with
  | nil => intro x τ; simp only [lookupB, Bool.false_eq_true, false_iff]; intro h; cases h
  | cons σ Γ ih =>
      intro x τ
      cases x with
      | zero =>
          simp only [lookupB, decide_eq_true_eq]
          constructor
          · intro h; subst h; exact lookup.Now _ _
          · intro h; cases h with | Now => rfl
      | succ x =>
          simp only [lookupB, ih]
          constructor
          · intro h; exact lookup.Later _ _ _ _ h
          · intro h; cases h with | Later _ _ _ _ h => exact h

/-- The `TVar` check's verdict is a *decisive* Kleene decision of `lookup`: it is never
`inconclusive`, so the `guard` neither keeps a wrong element nor drops a right one. -/
theorem varVerdict_ne_no_iff (Γ : List type) (x : Nat) (τ : type) :
    (if lookupB Γ x τ then V.yes else V.no) ≠ V.no ↔ lookup Γ x τ := by
  rw [← lookupB_iff]
  cases lookupB Γ x τ <;> simp

/-! ### The five rules -/

/-- `TVar`: generate the de Bruijn index from the unconstrained `Nat` leaf, then *check* `lookup`. -/
def rVar (i : Ix) : Body Ix term :=
  .aux .sized idProd (fun _ => True) fun x =>
    .check (if lookupB i.1 x i.2 then V.yes else V.no) (lookup i.1 x i.2) (.ret (.Var x))

/-- `TConst`: the conclusion pins the goal type, the numeral is an unconstrained leaf. -/
def rConst (i : Ix) : Body Ix term :=
  .cond (decide (i.2 = type.Nat)) (i.2 = type.Nat)
    (.aux .sized natProd (fun _ => True) fun k => .ret (.Const k))

/-- `TAdd`: two recursive premises at the same index. -/
def rAdd (i : Ix) : Body Ix term :=
  .cond (decide (i.2 = type.Nat)) (i.2 = type.Nat)
    (.pay (.call (i.1, type.Nat) fun e1 => .call (i.1, type.Nat) fun e2 => .ret (.Add e1 e2)))

/-- `TAbs`: a `.Match` on the goal type, done in Lean, with `fail` in the non-matching branch. -/
def rAbs : Ix → Body Ix term
  | (Γ, .Fun τ1 τ2) => .pay (.call (τ1 :: Γ, τ2) fun b => .ret (.Abs τ1 b))
  | (_, .Nat) => .fail

/-- `TApp`, the rule the whole exercise is about. -/
def rApp (g : Grade) (i : Ix) : Body Ix term :=
  .pay (.aux g typeProd (fun _ => True) fun τ1 =>
    .call (i.1, type.Fun τ1 i.2) fun e1 => .call (i.1, τ1) fun e2 => .ret (.App e1 e2))

/-- The five rules, listed in `stlcAFStep`/`stlcStep`'s own order — which is what makes the union fold
reconcile with the hand-written nest of `Choice.union`s. -/
def rules (g : Grade) : RuleSet Ix term := fun i => [rVar i, rConst i, rAdd i, rAbs i, rApp g i]

/-- `typing`, re-indexed the way the enumeration is. -/
def R : Ix → term → Prop := fun i e => typing i.1 e i.2

/-! ## The relational obligations — grading-blind, hence proved once for both grades -/

theorem hvalid (g : Grade) : ∀ i, ∀ b ∈ rules g i, ∀ e, HoldsR R b e → R i e := by
  intro ⟨Γ, τ⟩ b hb e h
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · simp only [rVar, HoldsR] at h
    obtain ⟨x, -, hlk, rfl⟩ := h
    exact typing.TVar Γ x τ hlk
  · simp only [rConst, HoldsR] at h
    obtain ⟨hτ, k, -, rfl⟩ := h
    subst hτ
    exact typing.TConst Γ k
  · simp only [rAdd, HoldsR] at h
    obtain ⟨hτ, e1, h1, e2, h2, rfl⟩ := h
    subst hτ
    exact typing.TAdd Γ e1 e2 h1 h2
  · cases τ with
    | Nat => simp only [rAbs, HoldsR] at h
    | Fun τ1 τ2 =>
        simp only [rAbs, HoldsR] at h
        obtain ⟨b', hb', rfl⟩ := h
        exact typing.TAbs Γ b' τ1 τ2 hb'
  · simp only [rApp, HoldsR] at h
    obtain ⟨τ1, -, e1, h1, e2, h2, rfl⟩ := h
    exact typing.TApp Γ e1 e2 τ1 τ h2 h1

theorem derives_of_typing (g : Grade) : ∀ {Γ e τ}, typing Γ e τ → Derives (rules g) (Γ, τ) e := by
  intro Γ e τ h
  induction h with
  | TConst Γ n =>
      refine Derives.intro (b := rConst (Γ, type.Nat)) ?_ ?_
      · simp [rules]
      · exact .cond rfl (.aux trivial (.ret _))
  | TAdd Γ e1 e2 _ _ ih1 ih2 =>
      refine Derives.intro (b := rAdd (Γ, type.Nat)) ?_ ?_
      · simp [rules]
      · exact .cond rfl (.pay (.call ih1 (.call ih2 (.ret _))))
  | TAbs Γ b τ1 τ2 _ ih =>
      refine Derives.intro (b := rAbs (Γ, type.Fun τ1 τ2)) ?_ ?_
      · simp [rules]
      · exact .pay (.call ih (.ret _))
  | TVar Γ x τ hlk =>
      refine Derives.intro (b := rVar (Γ, τ)) ?_ ?_
      · simp [rules]
      · exact .aux trivial (.check hlk (.ret _))
  | TApp Γ e1 e2 τ1 τ2 _ _ ih2 ih1 =>
      refine Derives.intro (b := rApp g (Γ, τ2)) ?_ ?_
      · simp [rules]
      · exact .pay (.aux trivial (.call ih1 (.call ih2 (.ret _))))

theorem hgen (g : Grade) : ∀ (i : Ix) (e : term), R i e → Derives (rules g) i e := by
  intro ⟨Γ, τ⟩ e h
  exact derives_of_typing g h

/-! ## The grading obligations

Three lines per premise at most, and the only graded content in the whole instance: `Sound`/`Covers`/
`MonoL` for three leaves and one decisiveness fact about the `TVar` verdict. -/

theorem hsound (g : Grade) : ∀ i, ∀ b ∈ rules g i, BodySound b := by
  intro ⟨Γ, τ⟩ b hb
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact ⟨sound_idProd, fun x => ⟨fun hv => (varVerdict_ne_no_iff Γ x τ).mp hv, trivial⟩⟩
  · exact ⟨fun h => of_decide_eq_true h, sound_natProd, fun _ => trivial⟩
  · exact ⟨fun h => of_decide_eq_true h, fun _ _ => trivial⟩
  · cases τ with
    | Nat => exact trivial
    | Fun τ1 τ2 => exact fun _ => trivial
  · exact ⟨sound_typeProd, fun _ => fun _ => fun _ => trivial⟩

theorem hcompleteSized : ∀ i, ∀ b ∈ rules .sized i, BodyComplete b := by
  intro ⟨Γ, τ⟩ b hb
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact ⟨monoL_idProd, covers_idProd,
      fun x => ⟨fun hl => (varVerdict_ne_no_iff Γ x τ).mpr hl, trivial⟩⟩
  · exact ⟨fun h => decide_eq_true h, monoL_natProd, covers_natProd, fun _ => trivial⟩
  · exact ⟨fun h => decide_eq_true h, fun _ _ => trivial⟩
  · cases τ with
    | Nat => exact trivial
    | Fun τ1 τ2 => exact fun _ => trivial
  · exact ⟨monoL_typeProd, covers_typeProd, fun _ => fun _ => fun _ => trivial⟩

/-! ## The payoff: STLC adequacy as an instance of the generic theorem -/

/-- **STLC's full five-rule `typing` relation is exactly its graded enumeration.**

No induction on `typing` and no induction on levels appears in this proof: both directions come from
`RuleShape.adequate`. What is supplied per-instance is only the *rule data* plus four obligations, none
of which involves the graded algebra beyond `Sound`/`Covers`/`MonoL` of three leaves. -/
theorem stlc_adequate (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ L l n, enum (rules .sized) L l (Γ, τ) n e :=
  adequate (hsound .sized) hcompleteSized (hvalid .sized) (hgen .sized) (Γ, τ) e

/-- **The same for the enumeration that runs.** `enumL` is executable `Nat → List term` code built
from the rule *data*; this says its levels are exactly the well-typed terms. -/
theorem stlc_mem_adequate (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ L l n, e ∈ enumL (rules .sized) L l (Γ, τ) n :=
  adequateL (hsound .sized) hcompleteSized (hvalid .sized) (hgen .sized) (Γ, τ) e

end RuleShape.Stlc

/-! # The bridge: the derived enumerator *is* the hand-written one

The instantiation above proves adequacy for the enumerator the *rule data* denotes. This section shows
that enumerator is not merely equivalent to `GradedStlcTest.stlcStep` — it is **equal** to it, level
for level, at every leaf budget. So `GradedStlcAdequacy.stlc_iff_budget` and `stlc_mem_iff_budget`
themselves come out of `RuleShape.adequate`, and the four `example`s at the end check that by putting
each statement where the other is expected.

One denotation lemma per rule. `bindC_ret` and `bindC_bindC_ret` carry `TConst`/`TAdd`/`TAbs`/`TApp`;
`TVar` needs `mem_lookupEnum_iff`, because the rule data runs it in generate-and-check mode
(`aux` over every natural, then `check lookup`) while `stlcAFStep` runs it as a direct producer, and
those coincide exactly because `lookupEnum` grades a variable by its index. -/

namespace RuleShape.Stlc

open RuleShape

/-- **Generate-and-check is the direct producer.** The `aux`-then-`check` body denotes precisely
`gmap term.Var (lookupEnum Γ τ)`: the `bindC` forces the index premise's level to be the whole level,
the `check` keeps exactly the indices `Γ` really holds `τ` at, and `lookupEnum`'s grading is that same
index. Neither containment is slack. -/
theorem denote_rVar (L : Nat) (rec : Ix → SetE term) (Γ : List type) (τ : type) :
    denote L rec (rVar (Γ, τ)) = Graded.gmap term.Var (lookupEnum Γ τ : SetE Nat) := by
  refine setE_ext fun n a => ?_
  simp only [rVar, denote_aux_sized, SetE.bindC_apply, denote_check_apply, denote_ret,
    SetE.single_apply, SetE.gmap_apply, mem_lookupEnum_iff, specOf, idProd, List.mem_singleton]
  constructor
  · rintro ⟨j, hj, x, rfl, hv, hz, rfl⟩
    have hjn : x = n := by omega
    subst hjn
    exact ⟨x, ⟨rfl, (varVerdict_ne_no_iff Γ x τ).mp hv⟩, rfl⟩
  · rintro ⟨x, ⟨rfl, hl⟩, rfl⟩
    exact ⟨x, Nat.le_refl _, x, rfl, (varVerdict_ne_no_iff Γ x τ).mpr hl, by omega, rfl⟩

theorem denote_rConst_nat (L : Nat) (rec : Ix → SetE term) (Γ : List type) :
    denote L rec (rConst (Γ, type.Nat)) = Graded.gmap term.Const (natAt L) := by
  show denote L rec (Body.cond (decide (type.Nat = type.Nat)) _
      (.aux .sized natProd (fun _ => True) fun k => .ret (.Const k))) = _
  simp only [decide_true, denote_cond_true, denote_aux_sized, denote_ret, specOf_natProd]
  exact bindC_ret _ _

theorem denote_rConst_fun (L : Nat) (rec : Ix → SetE term) (Γ : List type) (a b : type) :
    denote L rec (rConst (Γ, type.Fun a b)) = Choice.nothing := by
  show denote L rec (Body.cond (decide (type.Fun a b = type.Nat)) _ _) = _
  simp only [reduceCtorEq, decide_false, denote_cond_false]

theorem denote_rAdd_nat (L : Nat) (rec : Ix → SetE term) (Γ : List type) :
    denote L rec (rAdd (Γ, type.Nat))
      = Graded.pay (Graded.gmap (fun p => term.Add p.1 p.2)
          (Graded.pair (rec (Γ, type.Nat)) (rec (Γ, type.Nat)))) := by
  show denote L rec (Body.cond (decide (type.Nat = type.Nat)) _
      (.pay (.call (Γ, type.Nat) fun e1 => .call (Γ, type.Nat) fun e2 => .ret (.Add e1 e2))) ) = _
  simp only [decide_true, denote_cond_true, denote_pay, denote_call, denote_ret]
  exact congrArg Graded.pay (bindC_bindC_ret _ _ _)

theorem denote_rAdd_fun (L : Nat) (rec : Ix → SetE term) (Γ : List type) (a b : type) :
    denote L rec (rAdd (Γ, type.Fun a b)) = Choice.nothing := by
  show denote L rec (Body.cond (decide (type.Fun a b = type.Nat)) _ _) = _
  simp only [reduceCtorEq, decide_false, denote_cond_false]

theorem denote_rAbs_nat (L : Nat) (rec : Ix → SetE term) (Γ : List type) :
    denote L rec (rAbs (Γ, type.Nat)) = Choice.nothing := rfl

theorem denote_rAbs_fun (L : Nat) (rec : Ix → SetE term) (Γ : List type) (τ1 τ2 : type) :
    denote L rec (rAbs (Γ, type.Fun τ1 τ2))
      = Graded.pay (Graded.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))) := by
  show denote L rec (Body.pay (.call (τ1 :: Γ, τ2) fun b => .ret (.Abs τ1 b))) = _
  simp only [denote_pay, denote_call, denote_ret]
  exact congrArg Graded.pay (bindC_ret _ _)

theorem denote_rApp (L : Nat) (rec : Ix → SetE term) (Γ : List type) (τ : type) :
    denote L rec (rApp .sized (Γ, τ))
      = Graded.pay (GradedBind.bindC (tyAt L) fun τ1 =>
          Graded.gmap (fun p => term.App p.1 p.2)
            (Graded.pair (rec (Γ, type.Fun τ1 τ)) (rec (Γ, τ1)))) := by
  simp only [rApp, denote_pay, denote_aux_sized, denote_call, denote_ret, specOf_typeProd]
  refine congrArg Graded.pay (congrArg (GradedBind.bindC (tyAt L)) ?_)
  funext τ1
  exact bindC_bindC_ret _ _ _

/-- **The derived enumerator is the hand-written one.** One unfolding of the rule set at leaf budget
`L` is `stlcStep (natAt L) (tyAt L)` — equal, not merely equivalent. -/
theorem stepOf_eq_stlcStep (L : Nat) (rec : Ix → SetE term) :
    stepOf (rules .sized) L rec = stlcStep (natAt L) (tyAt L) rec := by
  funext i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
      simp only [stepOf, rules, List.map_cons, List.map_nil, unionAll, List.foldr_cons,
        List.foldr_nil, denote_rVar, denote_rConst_nat, denote_rAdd_nat, denote_rAbs_nat,
        denote_rApp]
      refine setE_ext fun n e => ?_
      simp only [stlcStep, stlcAFStep, SetE.union_apply, SetE.nothing_apply, or_false, false_or,
        or_assoc]
  | Fun a b =>
      simp only [stepOf, rules, List.map_cons, List.map_nil, unionAll, List.foldr_cons,
        List.foldr_nil, denote_rVar, denote_rConst_fun, denote_rAdd_fun, denote_rAbs_fun,
        denote_rApp]
      refine setE_ext fun n e => ?_
      simp only [stlcStep, stlcAFStep, SetE.union_apply, SetE.nothing_apply, or_false, false_or,
        or_assoc]

theorem enum_eq_enumAt (L : Nat) : ∀ l, enum (rules .sized) L l = enumAt L l
  | 0 => by funext i; rfl
  | l + 1 => by
      show stepOf (rules .sized) L (enum (rules .sized) L l)
        = stlcStep (natAt L) (tyAt L) (enumAt L l)
      rw [enum_eq_enumAt L l, stepOf_eq_stlcStep]

/-- **`stlc_iff_budget`, out of the generic theorem.** Identical statement to
`GradedStlcAdequacy.stlc_iff_budget` — see the `example`s below — but the proof is: five rules as data,
four obligations, and `RuleShape.adequate`. No induction on `typing`, no level arithmetic. -/
theorem stlc_iff_budget_generic (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ L levels n, enumAt L levels (Γ, τ) n e := by
  rw [stlc_adequate Γ e τ]
  constructor
  · rintro ⟨L, l, n, h⟩
    exact ⟨L, l, n, by rwa [enum_eq_enumAt] at h⟩
  · rintro ⟨L, l, n, h⟩
    exact ⟨L, l, n, by rwa [enum_eq_enumAt]⟩

/-- And for the enumeration that actually **runs**, through `agreesIx_stlc`. -/
theorem stlc_mem_iff_budget_generic (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ L levels n,
      e ∈ gradedIterIx (stlcStep (gradedIter natStep L : Lv Nat)
        (gradedIter typeStep L : Lv type)) levels (Γ, τ) n := by
  rw [stlc_iff_budget_generic Γ e τ]
  exact ⟨fun ⟨L, l, n, h⟩ =>
           ⟨L, l, n, (agreesIx_stlc (agrees_nat L) (agrees_type L) l (Γ, τ) n e).mpr h⟩,
         fun ⟨L, l, n, h⟩ =>
           ⟨L, l, n, (agreesIx_stlc (agrees_nat L) (agrees_type L) l (Γ, τ) n e).mp h⟩⟩

end RuleShape.Stlc

/-- The recovered statement is *literally* `GradedStlcAdequacy.stlc_iff_budget`'s. -/
example : (∀ (Γ : List type) (e : term) (τ : type),
    typing Γ e τ ↔ ∃ L levels n, enumAt L levels (Γ, τ) n e) :=
  RuleShape.Stlc.stlc_iff_budget_generic

example : (∀ (Γ : List type) (e : term) (τ : type),
    typing Γ e τ ↔ ∃ L levels n, enumAt L levels (Γ, τ) n e) := stlc_iff_budget

example : (∀ (Γ : List type) (e : term) (τ : type),
    typing Γ e τ ↔ ∃ L levels n,
      e ∈ gradedIterIx (stlcStep (gradedIter natStep L : Lv Nat)
        (gradedIter typeStep L : Lv type)) levels (Γ, τ) n) :=
  RuleShape.Stlc.stlc_mem_iff_budget_generic

example : (∀ (Γ : List type) (e : term) (τ : type),
    typing Γ e τ ↔ ∃ L levels n,
      e ∈ gradedIterIx (stlcStep (gradedIter natStep L : Lv Nat)
        (gradedIter typeStep L : Lv type)) levels (Γ, τ) n) := stlc_mem_iff_budget

/-! # The wrong choice, and why the generic proof refuses it

Two independent demonstrations that `.flat` (level-preserving `bind`) for `TApp`'s type premise is
wrong. Note first what is *not* broken: `hsound` is proved for **both** grades and `soundR` needs
nothing else, so the mis-graded rule set is still sound. Only completeness notices — which is exactly
the asymmetry that let the original bug through a full set of level-wise `Agrees` theorems. -/

namespace RuleShape.Stlc

open RuleShape

/-- Level `n` of the type enumeration holds only types of size `n`, at any budget. -/
theorem tyAt_sound : ∀ (L n : Nat) (τ : type), tyAt L n τ → tyCount τ = n := by
  intro L
  induction L with
  | zero => intro n τ h; exact absurd h (by simp [gradedIter])
  | succ L ih =>
      intro n τ h
      replace h : (typeStep (tyAt L) : SetE type) n τ := h
      simp only [typeStep, SetE.union_apply] at h
      rcases h with h | h
      · obtain ⟨hn, hτ⟩ := h; subst hτ; subst hn; rfl
      · cases n with
        | zero => exact absurd h (by simp)
        | succ m =>
            simp only [SetE.pay_succ, SetE.gmap_apply, SetE.pair_apply] at h
            obtain ⟨q, ⟨i, hi, h1, h2⟩, hτ⟩ := h
            subst hτ
            have e1 := ih i q.1 h1
            have e2 := ih (m - i) q.2 h2
            simp only [tyCount]
            omega

/-! ## 1. The generic completeness hypothesis is not merely unproved — it is false

`BodyComplete` demands `Unsized` of a `.flat` premise: from some budget on, the producer must offer its
value at *every* level. A type leaf graded by its number of `Fun` nodes offers `Nat` at level 0 and
nowhere else, at every budget, so the obligation is refutable — and refutable for a reason about the
grading rather than about funding. -/

theorem not_unsized_typeProd : ¬ Unsized typeProd (fun _ : type => True) := by
  intro h
  obtain ⟨L, hL⟩ := h type.Nat trivial
  have h2 : tyAt (L + 1) 1 type.Nat :=
    (agrees_type (L + 1) 1 type.Nat).mp (hL (L + 1) (by omega) 1)
  have h3 := tyAt_sound (L + 1) 1 type.Nat h2
  simp only [tyCount] at h3
  omega

theorem not_bodyComplete_rApp_flat (i : Ix) : ¬ BodyComplete (rApp .flat i) := fun h =>
  not_unsized_typeProd h.2.1

/-- The hypothesis `RuleShape.complete` needs cannot be discharged for the mis-graded rule set: it is
false. So the generic route to completeness is *blocked*, not merely unfinished. -/
theorem not_hcomplete_flat : ¬ (∀ i, ∀ b ∈ rules .flat i, BodyComplete b) := fun h =>
  not_bodyComplete_rApp_flat ([], type.Nat)
    (h ([], type.Nat) (rApp .flat ([], type.Nat)) (by simp [rules]))

/-! ## 2. And the enumeration really is incomplete: a concrete missing term

`(λx:Nat. 0) 0` — the term the original regression test names. Under `.flat` the type premise must be
found at the *same* level as the two term premises; `Nat` sits at type level 0, while any term premise
costs at least one rule application, so no level satisfies both. It is missed at **every** leaf budget,
**every** iteration count and **every** level, not merely over budget. -/

/-- `(λx:Nat. 0) 0`. -/
def badTerm : term := .App (.Abs type.Nat (.Const 0)) (.Const 0)

theorem typing_badTerm : typing [] badTerm type.Nat :=
  typing.TApp [] (.Abs type.Nat (.Const 0)) (.Const 0) type.Nat type.Nat
    (typing.TConst [] 0)
    (typing.TAbs [] (.Const 0) type.Nat type.Nat (typing.TConst [type.Nat] 0))

/-- The correctly graded rule set does enumerate it — straight out of the generic adequacy theorem. -/
theorem enum_sized_badTerm : ∃ L l n, enum (rules .sized) L l ([], type.Nat) n badTerm :=
  (stlc_adequate [] badTerm type.Nat).mp typing_badTerm

/-- Soundness of the *mis-graded* rule set. It holds: grading is invisible to `soundR`. -/
theorem flat_sound : ∀ L l i n e, enum (rules .flat) L l i n e → R i e :=
  soundR (hsound .flat) (hvalid .flat)

theorem abs_typing_inv {τ1 τ2 : type} {e : term}
    (h : typing [] (.Abs type.Nat e) (.Fun τ1 τ2)) : τ1 = type.Nat := by
  cases h; rfl

/-- At a function type in the *empty* context, level 0 is empty: `TVar` has nothing to look up,
`TConst`/`TAdd` do not apply, and `TAbs`/`TApp` both pay. This is the local replacement for the
uniform-`pay` file's `enum_zero`, which is false once `pay` is per-rule. -/
theorem enum_zero_fun (g : Grade) (L : Nat) : ∀ (l : Nat) (a b : type) (e : term),
    ¬ enum (rules g) L l ([], type.Fun a b) 0 e := by
  intro l
  induction l with
  | zero => intro a b e h; exact absurd h (by simp [gradedIterIx])
  | succ l _ =>
      intro a b e h
      replace h : stepOf (rules g) L (enum (rules g) L l) ([], type.Fun a b) 0 e := h
      rw [stepOf_apply] at h
      obtain ⟨r, hr, hd⟩ := h
      simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [denote_rVar] at hd; simp [lookupEnum] at hd
      · rw [denote_rConst_fun] at hd; exact absurd hd (by simp)
      · rw [denote_rAdd_fun] at hd; exact absurd hd (by simp)
      · simp only [rAbs, denote_pay, SetE.pay_zero] at hd
      · simp only [rApp, denote_pay, SetE.pay_zero] at hd

/-- **The counterexample.** A well-typed term the mis-graded enumeration produces at no leaf budget,
no iteration count and no level whatsoever. Contrast `enum_sized_badTerm`. -/
theorem not_enum_flat_badTerm : ∀ L l n, ¬ enum (rules .flat) L l ([], type.Nat) n badTerm := by
  intro L l
  induction l with
  | zero => intro n h; exact absurd h (by simp [gradedIterIx])
  | succ l _ =>
      intro n h
      replace h : stepOf (rules .flat) L (enum (rules .flat) L l) ([], type.Nat) n badTerm := h
      rw [stepOf_apply] at h
      obtain ⟨b, hb, hd⟩ := h
      have hR : HoldsR R b badTerm :=
        denote_soundR (fun i n a h => flat_sound L l i n a h) b
          (hsound .flat ([], type.Nat) b hb) n badTerm hd
      simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · simp only [rVar, HoldsR] at hR
        obtain ⟨x, -, -, hk⟩ := hR
        exact absurd hk (by simp [badTerm])
      · simp only [rConst, HoldsR] at hR
        obtain ⟨-, k, -, hk⟩ := hR
        exact absurd hk (by simp [badTerm])
      · simp only [rAdd, HoldsR] at hR
        obtain ⟨-, e1, -, e2, -, hk⟩ := hR
        exact absurd hk (by simp [badTerm])
      · simp only [rAbs, HoldsR] at hR
      · simp only [rApp, denote_pay, denote_aux_flat, denote_call, denote_ret] at hd
        cases n with
        | zero => exact absurd hd (by simp)
        | succ m =>
            simp only [SetE.pay_succ, SetE.bind_apply, SetE.bindC_apply, SetE.single_apply] at hd
            obtain ⟨τ1, hτ1, j, hj, e1, he1, j', hj', e2, -, -, hsplit⟩ := hd
            rw [badTerm] at hsplit
            cases hsplit
            have hτ : τ1 = type.Nat :=
              abs_typing_inv (flat_sound L l ([], type.Fun τ1 type.Nat) j _ he1)
            subst hτ
            have hm : m = 0 := by
              have h0 := tyAt_sound L m type.Nat ((agrees_type L m type.Nat).mp hτ1)
              simp only [tyCount] at h0
              omega
            subst hm
            have hj0 : j = 0 := Nat.le_zero.mp hj
            subst hj0
            exact enum_zero_fun .flat L l type.Nat type.Nat _ he1

/-! ### The contrast at the carrier that runs

Transported through `agrees_enum`, so both statements are about the executable `Nat → List term`. -/

/-- `(λx:Nat. 0) 0` appears in some level of the correctly graded value enumeration. -/
theorem mem_enumL_sized_badTerm : ∃ L l n, badTerm ∈ enumL (rules .sized) L l ([], type.Nat) n :=
  (stlc_mem_adequate [] badTerm type.Nat).mp typing_badTerm

/-- …and in **no** level of the mis-graded one. One field of one constructor of one rule apart. -/
theorem not_mem_enumL_flat_badTerm :
    ∀ L l n, badTerm ∉ enumL (rules .flat) L l ([], type.Nat) n := fun L l n h =>
  not_enum_flat_badTerm L l n ((agrees_enum (rules .flat) L l ([], type.Nat) n badTerm).mp h)

/-! ### The same facts, by evaluation

`enumL` is ordinary code, so the claims can also just be run — and since `stepOf_eq_stlcStep` is an
equality, the derived enumerator's levels are the hand-written enumerator's *as lists*, order
included. -/

-- Level counts at `⊢ _ : Nat`, leaf budget 6 and five iterations.
/-- info: [1, 2, 7, 28, 138, 571] -/
#guard_msgs in
#eval ((List.range 6).map fun n => (enumL (rules .sized) 6 5 ([], type.Nat) n).length)

-- The mis-graded rule set. It first differs at level 2, and it is not merely *missing* terms: it also
-- puts terms at the wrong level, because a level-preserving type premise lets an arbitrarily large
-- type annotation ride for free. These are the numbers `GradedStlcTest.lean` records for the original
-- `bind` bug: `[1, 2, 5, 16]`.
/-- info: [1, 2, 5, 16, 66, 319] -/
#guard_msgs in
#eval ((List.range 6).map fun n => (enumL (rules .flat) 6 5 ([], type.Nat) n).length)

-- The hand-written enumerator, same budget and iteration count. `stepOf_eq_stlcStep` says this
-- agreement is not luck.
/-- info: [1, 2, 7, 28, 138, 571] -/
#guard_msgs in
#eval ((List.range 6).map fun n => (gradedIterIx (f := Lv)
  (stlcStep (gradedIter natStep 6) (gradedIter typeStep 6)) 5 ([], type.Nat) n).length)

-- …not just the same counts: the same list.
/-- info: true -/
#guard_msgs in
#eval (enumL (rules .sized) 6 5 ([], type.Nat) 5) == (gradedIterIx (f := Lv)
  (stlcStep (gradedIter natStep 6) (gradedIter typeStep 6)) 5 ([], type.Nat) 5)

-- What `.flat` loses at level 2: exactly the two smallest well-typed applications.
/--
info: [term.App (term.Abs (type.Nat) (term.Var 0)) (term.Const 0),
 term.App (term.Abs (type.Nat) (term.Const 0)) (term.Const 0)]
-/
#guard_msgs in
#eval (enumL (rules .sized) 6 5 ([], type.Nat) 2).filter
  (fun t => !((enumL (rules .flat) 6 5 ([], type.Nat) 2).contains t))

-- `(λx:Nat. 0) 0`: produced at level 2 by the correctly graded rules, at no level by the others.
/-- info: [false, false, true, false, false] -/
#guard_msgs in
#eval ((List.range 5).map fun n => (enumL (rules .sized) 6 5 ([], type.Nat) n).contains badTerm)

/-- info: [false, false, false, false, false] -/
#guard_msgs in
#eval ((List.range 5).map fun n => (enumL (rules .flat) 6 5 ([], type.Nat) n).contains badTerm)

end RuleShape.Stlc

/-! # What this does not do

An honest list, because each item is a place where the generic theorem is weaker than it looks.

* **One output type per rule set.** `call` returns the relation's own `α`, so a *mutual SCC whose
  members produce different types* — `typing` producing a `term` beside `lookup` producing a `Nat` — is
  not directly a `call`. It is encodable by taking `ι` and `α` to be sums and tagging, and cross-SCC
  premises are `aux` regardless, but neither is exhibited here: `lookup` is instantiated as a `check`
  instead. Nothing in the two theorems depends on `ι` or `α`, so the sum encoding costs no new proof —
  only new plumbing.

* **`check` discards the conclusiveness flag.** `guard` returns `f (α × Bool)`; `denote` projects the
  `Bool` away. That is why `BodySound` has to demand `v ≠ .no → P`, which makes an `inconclusive`
  verdict sound only where `P` in fact holds. A faithful treatment threads the flag into the output and
  weakens soundness to "conclusive results are in the relation". The STLC instance's one `check` is
  decisive (`varVerdict_ne_no_iff`), so it is unaffected, and `V.inconclusive` is therefore exercised by
  the semantics but not by the instance.

* **One leaf budget for all leaves.** `denote` threads a single `L` to every `aux` premise, so a rule
  set cannot give its numeral leaf a different budget from its type leaf. That is the shape
  `stlcStep (natAt L) (tyAt L)` has and so is not a limitation for the bridge, but a deriver that wants
  per-leaf budgets would need `p` to be indexed by something richer than `Nat`.

* **No `Cnt` leg.** The counting carrier cannot interpret `bind`/`guard`, so nothing here counts. That
  matches `GradedStlcTest.lean`'s finding: `TApp` has no compositional count-only interpretation.

* **`ScheduleStep` is mapped, not proved to be mapped.** The table in the module docstring is a
  hand-checked correspondence, not a Lean function `ScheduleStep → Body` with a simulation lemma against
  `Gen.lean`/`CheckEnum.lean`. Writing that erasure is the next step, and it is the step that would let a
  deriver's schedule be *validated* by these theorems rather than merely resemble them. It is also the
  step whose cost this design exists to avoid paying twice: the erasure is first-order and syntactic,
  whereas adequacy is where the induction is.

* **The bridge is one relation deep.** `stepOf_eq_stlcStep` is proved by naming every rule and
  unfolding; it is not a theorem about a class of rule sets. What makes it cheap is that the three
  reconciliation lemmas (`bindC_ret`, `bindC_bindC_ret`, `denote_rVar`) are reusable and the rest is
  `simp`, but a second relation would still be a second proof of the same shape.
-/

/-! # Axiom audit -/

