import SpecimenTest.CommonDefinitions.STLCDefinitions
import SpecimenTest.CommonDefinitions.STLCBasaltGenerators
import Specimen
import Basalt.SPMF.Backtrack
import Basalt.SPMF.Arbitrary

/-!
# Budget measures for the derived STLC generators

The measures live in their own module, with no `derive_mutual` of their own, so that every file
that proves something about the derived `typing` generators — `StlcCompleteness.lean` by hand,
`TypingBridge.lean` through the generic family interpreter — can run its own derivation and still
share them. The two proofs arrive at the same budgets by different routes, which is the cross-check
that the budgets are right.

Four measures, each forced by a different behaviour of the emitted code. See
`StlcCompleteness.lean`'s header for the full argument; in brief:

* `budget`  — the search budget. **Doubles** at `Add`/`App` because the emitter halves `size` there;
  `max 2` floor because the `size = 0` pool withholds every recursive constructor.
* `tdepth`  — the fuel backstop, one level per recursive step.
* `varBound` — largest de Bruijn index + 1, bounding the `initSize` the lookup producer needs.
* `tyNeed` — the depth of the types `TApp` draws unconstrained, computed through `outTy`.
-/

open Plausible Basalt

/-- Candidate budget: the minimum `size` at which the generator should reach `e`. -/
def budget : term → Nat
  | .Const _ => 0
  | .Var _   => 0
  | .Abs _ e => max 2 (budget e + 1)
  | .Add a b => max 2 (2 * max (budget a) (budget b) + 1)
  | .App a b => max 2 (2 * max (budget a) (budget b) + 1)

/-- Depth of a type, for budgeting the *derived* `ArbitraryFueled type` generator. -/
def typeDepth : type → Nat
  | .Nat     => 0
  | .Fun a b => max (typeDepth a) (typeDepth b) + 1

/-- **Completeness of a derived UNCONSTRAINED generator.** Needed because `TApp` draws its argument
    type from `ArbitraryFueled type` instead of synthesising it, so the constrained generator's
    completeness is only as good as this one's. Conditional on fuel, exactly like the constrained
    case: the fuel-`n` generator reaches types of depth at most `n`. -/
theorem type_gen_complete : ∀ (τ : type) (n : Nat), typeDepth τ ≤ n →
    τ ∈ (@type.basaltArbitraryFueled SPMF _ n).support := by
  intro τ
  induction τ with
  | Nat =>
    intro n _
    cases n with
    | zero =>
      simp [type.basaltArbitraryFueled, SPMF.support_oneOf]
    | succ n =>
      simp [type.basaltArbitraryFueled, SPMF.support_oneOf]
  | Fun a b iha ihb =>
    intro n hn
    -- `typeDepth (Fun a b) = max … + 1 ≤ n` rules out fuel 0, which is why the zero branch offering
    -- only `Nat` is not a counterexample to completeness.
    cases n with
    | zero => exact absurd hn (by simp only [typeDepth]; omega)
    | succ n =>
      have ha : typeDepth a ≤ n := by simp only [typeDepth] at hn; omega
      have hb : typeDepth b ≤ n := by simp only [typeDepth] at hn; omega
      simp only [type.basaltArbitraryFueled, SPMF.support_oneOf, Set.mem_ofPred_eq,
        List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨_, .inr rfl, ?_⟩
      simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
      exact ⟨a, iha n ha, b, ihb n hb, rfl⟩

/-! ### The type-draw budget

The schedule the deriver now picks for `TApp` *draws* the argument type from the unconstrained
`ArbitraryFueled type` generator (there is no auxiliary pair mode), and that is the only place a type
is drawn — `TAbs` reads its annotation off the target type and pays nothing.  The drawn type is not a
subterm of the term: it is the type the derivation assigns to the argument.  `typing` is
syntax-directed and deterministic, so that type is computable from the term and its context — `outTy`
recovers it, `typing_outTy` proves the recovery correct, and `tyNeed` accumulates its depth over
every `App` node. -/

/-- The type `typing` assigns to `e` under `Γ`, recovered by recursion on the term. -/
def outTy : List type → term → Option type
  | _, .Const _ => some .Nat
  | Γ, .Var x   => Γ[x]?
  | Γ, .Abs a b => (outTy (a :: Γ) b).map (type.Fun a)
  | _, .Add _ _ => some .Nat
  | Γ, .App a _ =>
      match outTy Γ a with
      | some (.Fun _ c) => some c
      | _ => none

/-- A derivable `lookup` is what `List.getElem?` computes. -/
theorem lookup_getElem? {Γ : List type} {x : Nat} {τ : type} (h : lookup Γ x τ) :
    Γ[x]? = some τ := by
  induction h with
  | Now τ Γ => rfl
  | Later τ τ' n Γ _ ih => simpa using ih

/-- `typing` is syntax-directed: `outTy` recovers the (unique) type of a well-typed term. -/
theorem typing_outTy {Γ : List type} {e : term} {τ : type} (h : typing Γ e τ) :
    outTy Γ e = some τ := by
  induction h with
  | TConst Γ n => rfl
  | TAdd Γ e1 e2 _ _ _ _ => rfl
  | TAbs Γ e τ1 τ2 _ ih => simp [outTy, ih]
  | TVar Γ x τ hlk => simpa [outTy] using lookup_getElem? hlk
  | TApp Γ e1 e2 τ1 τ2 _ _ _ ih1 => simp [outTy, ih1]

/-- The type-draw budget: fuel the unconstrained `type` draws need, one per `App` node. -/
def tyNeed : List type → term → Nat
  | _, .Const _ => 0
  | _, .Var _   => 0
  | Γ, .Abs a b => tyNeed (a :: Γ) b
  | Γ, .Add a b => max (tyNeed Γ a) (tyNeed Γ b)
  | Γ, .App a b => max ((outTy Γ b).elim 0 typeDepth) (max (tyNeed Γ a) (tyNeed Γ b))

/-- Fuel needed: one level per recursive generator step. -/
def tdepth : term → Nat
  | .Const _ => 0
  | .Var _   => 0
  | .Abs _ e => tdepth e + 1
  | .Add a b => max (tdepth a) (tdepth b) + 1
  | .App a b => max (tdepth a) (tdepth b) + 1

/-- Largest de Bruijn index appearing, +1: bounds the `initSize` the lookup producer needs. -/
def varBound : term → Nat
  | .Const _ => 0
  | .Var x   => x + 1
  | .Abs _ e => varBound e
  | .Add a b => max (varBound a) (varBound b)
  | .App a b => max (varBound a) (varBound b)

/-- The `TConst` branch draws its literal from `Arbitrary Nat`, so completeness there is exactly that
    generator's support lemma, which lives in `Basalt.SPMF.Arbitrary`. -/
theorem nat_arbitraryGen_support (n : Nat) :
    n ∈ (Basalt.Nat.arbitraryGen (G := SPMF)).support :=
  Basalt.Nat.mem_support_arbitraryGen n

/-- The halving arithmetic, shared by the `Add` and `App` branches: the measure's doubling is
    exactly what survives the emitter's `Nat.div size' 2`, and the `max 2` floor is what forces
    `size' ≠ 0` — which is what keeps the recursive branches in the pool at all. -/
theorem budget_children {x y : term} {sz : Nat}
    (h : max 2 (2 * max (budget x) (budget y) + 1) ≤ sz + 1) :
    budget x ≤ sz / 2 ∧ budget y ≤ sz / 2 ∧ sz ≠ 0 := by
  refine ⟨?_, ?_, by omega⟩
  · refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    have := Nat.le_max_left (budget x) (budget y); omega
  · refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    have := Nat.le_max_right (budget x) (budget y); omega

/-! ### A closed-form size bound

`budget` is a linear recurrence, which is what makes the branch arithmetic `omega`-friendly, but it is
not readable as a statement about a term. This closed form is: `2 ^ hdepth e * (ldepth e + 2)`, where
`hdepth` counts only the **halving** constructors (`Add`/`App`) and `ldepth` only the linear one
(`Abs`).

The exponential is real, not an artefact — the emitted schedule halves `size` at every `Add`/`App`, so
a balanced `Add` tree of constructor depth `d` genuinely needs `size ≈ 2 ^ d`. The `+2` is forced:
`+1` breaks the `Abs` floor and `+3` breaks the halving identity `2^(h+1)*(l+2) = 2*(2^h*(l+2))`.

Ported from `StlcCompleteness.lean`, which derived it first; `budget` and its `sizeNeed` are the same
recurrence, so the proof transfers by renaming. -/

def hdepth : term → Nat
  | .Const _ => 0
  | .Var _ => 0
  | .Abs _ e => hdepth e
  | .Add a b => max (hdepth a) (hdepth b) + 1
  | .App a b => max (hdepth a) (hdepth b) + 1

def ldepth : term → Nat
  | .Const _ => 0
  | .Var _ => 0
  | .Abs _ e => ldepth e + 1
  | .Add a b => max (ldepth a) (ldepth b)
  | .App a b => max (ldepth a) (ldepth b)

/-- The closed-form size budget: `2 ^ hdepth e * (ldepth e + 2)`. -/
def sizeMeasure (e : term) : Nat := 2 ^ hdepth e * (ldepth e + 2)

theorem sizeMeasure_mono {h' h l' l : Nat} (hh : h' ≤ h) (hl : l' ≤ l) :
    2 ^ h' * (l' + 2) ≤ 2 ^ h * (l + 2) :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hh) (by omega)

theorem two_le_pow_mul (h l : Nat) : 2 ≤ 2 ^ h * (l + 2) := by
  have hp : 1 * 2 ≤ 2 ^ h * (l + 2) := Nat.mul_le_mul Nat.one_le_two_pow (by omega)
  omega

theorem two_le_sizeMeasure (e : term) : 2 ≤ sizeMeasure e := by
  simp only [sizeMeasure]; exact two_le_pow_mul _ _

theorem pow_succ_mul (m k : Nat) : 2 ^ (m + 1) * k = 2 * (2 ^ m * k) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc]

/-- The halving-constructor step, shared by `Add` and `App`: both double the children's budget and
add a level to `hdepth`, so one inequality covers both cases of `budget_lt_sizeMeasure`. -/
theorem halving_le {a b : term} (iha : budget a + 1 ≤ sizeMeasure a)
    (ihb : budget b + 1 ≤ sizeMeasure b) :
    max 2 (2 * max (budget a) (budget b) + 1) + 1
      ≤ 2 ^ (max (hdepth a) (hdepth b) + 1) * (max (ldepth a) (ldepth b) + 2) := by
  have hg : 2 ≤ 2 ^ max (hdepth a) (hdepth b) * (max (ldepth a) (ldepth b) + 2) :=
    two_le_pow_mul _ _
  have ha : budget a + 1 ≤ 2 ^ max (hdepth a) (hdepth b) * (max (ldepth a) (ldepth b) + 2) := by
    refine Nat.le_trans iha ?_
    simp only [sizeMeasure]
    exact sizeMeasure_mono (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hb : budget b + 1 ≤ 2 ^ max (hdepth a) (hdepth b) * (max (ldepth a) (ldepth b) + 2) := by
    refine Nat.le_trans ihb ?_
    simp only [sizeMeasure]
    exact sizeMeasure_mono (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rw [pow_succ_mul]
  omega

/-- **The exact measure is dominated by the closed form**, so the readable depth bound is a free
corollary rather than the induction hypothesis. -/
theorem budget_lt_sizeMeasure (e : term) : budget e + 1 ≤ sizeMeasure e := by
  induction e with
  | Const n =>
    have h := two_le_sizeMeasure (term.Const n)
    simp only [budget]; omega
  | Var x =>
    have h := two_le_sizeMeasure (term.Var x)
    simp only [budget]; omega
  | Add a b iha ihb => simpa only [budget, sizeMeasure, hdepth, ldepth] using halving_le iha ihb
  | App a b iha ihb => simpa only [budget, sizeMeasure, hdepth, ldepth] using halving_le iha ihb
  | Abs t body ih =>
    have hE : sizeMeasure (.Abs t body) = sizeMeasure body + 2 ^ hdepth body := by
      simp only [sizeMeasure, hdepth, ldepth]
      have hr : ldepth body + 1 + 2 = (ldepth body + 2) + 1 := by omega
      rw [hr, Nat.mul_succ]
    have h1 : 1 ≤ 2 ^ hdepth body := Nat.one_le_two_pow
    have h2 : 2 ≤ sizeMeasure body := two_le_sizeMeasure body
    simp only [budget]
    omega
