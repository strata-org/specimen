import Basalt.GradedLazy
import SpecimenTest.BasaltPort.GradedStlcAdequacy

/-!
# STLC on the lazy-level carrier

`GradedStlcAdequacy.lean` proves `typing` is exactly the enumeration that runs on
`Array (Thunk (List α))`. That carrier builds a level whole once touched, which costs the whole level to
read its first `k` terms — ruinous when one level is huge (measured:
1.6 GB and 2.7 s for the first 5 000 terms of a 9·10⁶-term level, against 67 MB and 3 ms lazily;
`bench/README.md` carries the full table).

This file restates the same result on `Basalt/GradedLazy.lean`'s `Array (Thunk (LList α))`, where a level is
forced only as far as it is read. It is a mechanical translation of the strict section — every step is a
closure lemma from `GradedLazy` plus the same width invariant — and adds the statement the strict carrier
could not usefully make: **the first `k` terms read lazily from any level are well typed**.
-/

open Basalt

/-! ## The system at `LvL`

Each definition mirrors its `Lv` counterpart operation for operation, with `N` threaded. -/

/-- `Nat` graded by magnitude, at width `N + 1`. -/
def natStepL (N : Nat) (rec : LvL Nat) : LvL Nat :=
  LvL.union (LvL.single N 0) (LvL.pay (LvL.gmap (· + 1) rec))

/-- `type` graded by size, at width `N + 1`. -/
def typeStepL (N : Nat) (rec : LvL type) : LvL type :=
  LvL.union (LvL.single N type.Nat)
    (LvL.pay (LvL.gmap (fun p => type.Fun p.1 p.2) (LvL.pair rec rec)))

/-- The de Bruijn indices at which `Γ` holds `τ`, at width `N + 1`. Structurally recursive on `Γ`, exactly
as `lookupEnum` is — the width is threaded unchanged. -/
def lookupEnumL (N : Nat) : List type → type → LvL Nat
  | [], _ => LvL.nothing N
  | σ :: Γ, τ =>
      LvL.union (if σ = τ then LvL.single N 0 else LvL.nothing N)
        (LvL.pay (LvL.gmap (· + 1) (lookupEnumL N Γ τ)))

/-- The `TApp`-free fragment at width `N + 1`. -/
def stlcAFStepL (N : Nat) (natE : LvL Nat) (rec : TyIx → LvL term) : TyIx → LvL term
  | (Γ, .Nat) =>
      LvL.union (LvL.gmap term.Var (lookupEnumL N Γ .Nat))
        (LvL.union (LvL.gmap term.Const natE)
          (LvL.pay (LvL.gmap (fun p => term.Add p.1 p.2)
            (LvL.pair (rec (Γ, .Nat)) (rec (Γ, .Nat))))))
  | (Γ, .Fun τ1 τ2) =>
      LvL.union (LvL.gmap term.Var (lookupEnumL N Γ (.Fun τ1 τ2)))
        (LvL.pay (LvL.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))))

/-- The full system at width `N + 1`. `LvL.bindC` is the correlated premise, same as at `Lv`. -/
def stlcStepL (N : Nat) (natE : LvL Nat) (typeE : LvL type) (rec : TyIx → LvL term) :
    TyIx → LvL term
  | (Γ, τ) =>
      LvL.union (stlcAFStepL N natE rec (Γ, τ))
        (LvL.pay (LvL.bindC typeE (fun τ1 =>
          LvL.gmap (fun p => term.App p.1 p.2)
            (LvL.pair (rec (Γ, .Fun τ1 τ)) (rec (Γ, τ1))))))

/-- `gradedIter` at `LvL`. The base case has to *name* the width — that is the one place the carrier's
explicit size cannot be inferred from an operand. -/
def gradedIterL {α : Type} (N : Nat) (step : LvL α → LvL α) : Nat → LvL α
  | 0 => LvL.nothing N
  | l + 1 => step (gradedIterL N step l)

/-- `gradedIterIx` at `LvL`. Same remark about the base case. -/
def gradedIterIxL {α ι : Type} (N : Nat) (step : (ι → LvL α) → ι → LvL α) : Nat → ι → LvL α
  | 0, _ => LvL.nothing N
  | l + 1, i => step (gradedIterIxL N step l) i

/-! ## The width invariant

Every enumeration above has width exactly `N + 1`. These are what discharge the size side conditions on
`AgreeL.union` / `.pair` / `.bindC`; without them the carrier change does not go through. -/

@[simp] theorem sizeL_natStepL (N : Nat) (rec : LvL Nat) : (natStepL N rec).size = N + 1 := by
  simp [natStepL]

@[simp] theorem sizeL_typeStepL (N : Nat) (rec : LvL type) : (typeStepL N rec).size = N + 1 := by
  simp [typeStepL]

@[simp] theorem sizeL_lookupEnumL (N : Nat) (τ : type) : ∀ Γ : List type,
    (lookupEnumL N Γ τ).size = N + 1
  | [] => by simp [lookupEnumL]
  | σ :: Γ => by
      rw [lookupEnumL, LvL.size_union]
      by_cases h : σ = τ <;> simp [h]

@[simp] theorem sizeL_stlcAFStepL (N : Nat) (natE : LvL Nat) (rec : TyIx → LvL term) (i : TyIx) :
    (stlcAFStepL N natE rec i).size = N + 1 := by
  obtain ⟨Γ, τ⟩ := i
  cases τ <;> simp [stlcAFStepL]

@[simp] theorem sizeL_stlcStepL (N : Nat) (natE : LvL Nat) (typeE : LvL type)
    (rec : TyIx → LvL term) (i : TyIx) : (stlcStepL N natE typeE rec i).size = N + 1 := by
  obtain ⟨Γ, τ⟩ := i
  simp [stlcStepL]

theorem sizeL_gradedIterL {α : Type} (N : Nat) {step : LvL α → LvL α}
    (hs : ∀ x, (step x).size = N + 1) : ∀ l, (gradedIterL N step l).size = N + 1
  | 0 => by simp [gradedIterL]
  | _ + 1 => hs _

theorem sizeL_gradedIterIxL {α ι : Type} (N : Nat) {step : (ι → LvL α) → ι → LvL α}
    (hs : ∀ x i, (step x i).size = N + 1) : ∀ l i, (gradedIterIxL N step l i).size = N + 1
  | 0, _ => by simp [gradedIterIxL]
  | _ + 1, i => hs _ i

/-! ## Agreement with the `Lv` system

Nothing about `Agrees` or `SubE` is reproved: every step below is an application of a closure lemma from
`Basalt/GradedRun.lean`, plus a size obligation discharged by the invariant above. The one piece of
plumbing `GradedRun` does not ship is the `ite` case, needed for `lookupEnum`'s `σ = τ` side condition. -/

theorem agreeL_natStepL (N : Nat) {rec : LvL Nat} {m : Lv Nat}
    (h : AgreeL rec m) (hsz : rec.size = N + 1) : AgreeL (natStepL N rec) (natStep m) :=
  (agreeL_single N 0).union ((h.gmap _).pay) (by simp [hsz])

theorem agreeL_typeStepL (N : Nat) {rec : LvL type} {m : Lv type}
    (h : AgreeL rec m) (hsz : rec.size = N + 1) : AgreeL (typeStepL N rec) (typeStep m) :=
  (agreeL_single N type.Nat).union (((h.pair h rfl).gmap _).pay) (by simp [hsz])

theorem agreeL_lookupEnumL (N : Nat) (τ : type) : ∀ Γ : List type,
    AgreeL (lookupEnumL N Γ τ) (lookupEnum Γ τ)
  | [] => agreeL_nothing N
  | σ :: Γ => by
      rw [lookupEnumL, lookupEnum]
      refine AgreeL.union (AgreeL.ite (agreeL_single N 0) (agreeL_nothing N))
        (((agreeL_lookupEnumL N τ Γ).gmap _).pay) ?_
      by_cases h : σ = τ <;> simp [h]

theorem agreeL_stlcAFStepL (N : Nat) {natE : LvL Nat} {natM : Lv Nat}
    (hn : AgreeL natE natM) (hnsz : natE.size = N + 1)
    {rec : TyIx → LvL term} {m : TyIx → Lv term}
    (h : ∀ i, AgreeL (rec i) (m i)) (hsz : ∀ i, (rec i).size = N + 1) :
    ∀ i, AgreeL (stlcAFStepL N natE rec i) (stlcAFStep natM m i) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
    exact ((agreeL_lookupEnumL N _ Γ).gmap _).union
      ((hn.gmap _).union
        ((((h (Γ, .Nat)).pair (h (Γ, .Nat)) rfl).gmap _).pay) (by simp [hsz, hnsz]))
      (by simp [hnsz])
  | Fun τ1 τ2 =>
    exact ((agreeL_lookupEnumL N _ Γ).gmap _).union
      (((h (τ1 :: Γ, τ2)).gmap _).pay) (by simp [hsz])

theorem agreeL_stlcStepL (N : Nat) {natE : LvL Nat} {natM : Lv Nat}
    (hn : AgreeL natE natM) (hnsz : natE.size = N + 1)
    {typeE : LvL type} {typeM : Lv type}
    (ht : AgreeL typeE typeM) (htsz : typeE.size = N + 1)
    {rec : TyIx → LvL term} {m : TyIx → Lv term}
    (h : ∀ i, AgreeL (rec i) (m i)) (hsz : ∀ i, (rec i).size = N + 1) :
    ∀ i, AgreeL (stlcStepL N natE typeE rec i) (stlcStep natM typeM m i) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  exact (agreeL_stlcAFStepL N hn hnsz h hsz (Γ, τ)).union
    ((ht.bindC (fun τ1 => (((h (Γ, .Fun τ1 τ)).pair (h (Γ, τ1)) (by simp [hsz])).gmap _))
        (fun _ => by simp [hsz, htsz])).pay)
    (by simp [htsz])

theorem agreeL_gradedIterL {α : Type} (N : Nat) {stepT : LvL α → LvL α} {step : Lv α → Lv α}
    (hstep : ∀ x m, AgreeL x m → x.size = N + 1 → AgreeL (stepT x) (step m))
    (hsize : ∀ x, (stepT x).size = N + 1) :
    ∀ l, AgreeL (gradedIterL N stepT l) (gradedIter step l)
  | 0 => agreeL_nothing N
  | l + 1 =>
      hstep _ _ (agreeL_gradedIterL N hstep hsize l) (sizeL_gradedIterL N hsize l)

theorem agreeL_gradedIterIxL {α ι : Type} (N : Nat) {stepT : (ι → LvL α) → ι → LvL α}
    {step : (ι → Lv α) → ι → Lv α}
    (hstep : ∀ x m, (∀ i, AgreeL (x i) (m i)) → (∀ i, (x i).size = N + 1) →
      ∀ i, AgreeL (stepT x i) (step m i))
    (hsize : ∀ x i, (stepT x i).size = N + 1) :
    ∀ l i, AgreeL (gradedIterIxL N stepT l i) (gradedIterIx step l i)
  | 0, _ => agreeL_nothing N
  | l + 1, i =>
      hstep _ _ (agreeL_gradedIterIxL N hstep hsize l) (sizeL_gradedIterIxL N hsize l) i

/-! ## The executable enumeration, and its agreement -/

/-- **The STLC enumeration that runs.** Array width `N + 1` (levels `0..N`), leaf budget `L`, `levels`
iterations. Definitionally the `Lv` enumeration of `stlc_mem_iff_budget` with `LvL` operations in place of
`Lv` ones and the width threaded. -/
def enumL (N L levels : Nat) : TyIx → LvL term :=
  gradedIterIxL N
    (stlcStepL N (gradedIterL N (natStepL N) L) (gradedIterL N (typeStepL N) L)) levels

@[simp] theorem sizeL_enumL (N L levels : Nat) (i : TyIx) : (enumL N L levels i).size = N + 1 :=
  sizeL_gradedIterIxL N (fun _ _ => sizeL_stlcStepL ..) levels i

/-- **The carrier change is sound and loses nothing within the width.** Every level the array stores reads
exactly as the `Lv` enumeration does. -/
theorem agreeL_enumL (N L levels : Nat) (i : TyIx) :
    AgreeL (enumL N L levels i) (enumLv L levels i) :=
  agreeL_gradedIterIxL N
    (fun _ _ hx hsz =>
      agreeL_stlcStepL N
        (agreeL_gradedIterL N (fun _ _ h hs => agreeL_natStepL N h hs) (fun _ => sizeL_natStepL ..) L)
        (sizeL_gradedIterL N (fun _ => sizeL_natStepL ..) L)
        (agreeL_gradedIterL N (fun _ _ h hs => agreeL_typeStepL N h hs) (fun _ => sizeL_typeStepL ..) L)
        (sizeL_gradedIterL N (fun _ => sizeL_typeStepL ..) L)
        hx hsz)
    (fun _ _ => sizeL_stlcStepL ..) levels i

/-- The level-by-level form, for a caller whose width is already fixed. -/
theorem mem_enumL_iff (N L levels : Nat) (i : TyIx) (n : Nat) (hn : n < N + 1) (e : term) :
    e ∈ ((enumL N L levels i).get n).toList ↔ e ∈ enumLv L levels i n := by
  rw [agreeL_enumL N L levels i n (by simpa using hn)]

/-- **`typing` is exactly the enumeration that runs.**

Same content as `stlc_mem_iff_budget`, on `Array (Thunk (List term))` instead of `Nat → List term` — so
the theorem is now about code with the right cost model: levels are memoised by the array and deferred by
the thunks, rather than recomputed `(k+1)^n` times by a function carrier.

The extra `N` is the array width and the extra `n < N + 1` is `Agree`'s bound. Neither weakens the
biconditional: `→` produces its own level and may take `N := n`; `←` is the `Lv` soundness result
transported over one level the array actually stores. -/
theorem stlc_mem_iff_runL (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ N L levels n, n < N + 1 ∧ e ∈ ((enumL N L levels (Γ, τ)).get n).toList := by
  rw [stlc_mem_iff_budget Γ e τ]
  constructor
  · rintro ⟨L, levels, n, h⟩
    exact ⟨n, L, levels, n, Nat.lt_succ_self n,
      (mem_enumL_iff n L levels (Γ, τ) n (Nat.lt_succ_self n) e).mpr h⟩
  · rintro ⟨N, L, levels, n, hn, h⟩
    exact ⟨L, levels, n, (mem_enumL_iff N L levels (Γ, τ) n hn e).mp h⟩


/-- **Reading lazily is sound.** Any term among the first `k` read from any level of the lazy enumeration
is well typed — without forcing the rest of the level. -/
theorem stlc_take_sound {Γ : List type} {τ : type} {N L levels n k : Nat} (hn : n < N + 1) {e : term}
    (h : e ∈ ((enumL N L levels (Γ, τ)).get n).take k) : typing Γ e τ := by
  rw [LList.take_eq] at h
  exact (stlc_mem_iff_runL Γ e τ).2 ⟨N, L, levels, n, hn, List.mem_of_mem_take h⟩

/-! ## The carrier change did not alter the enumeration, checked by evaluation -/

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval ((List.range 4).map fun n =>
  ((enumL 3 6 4 ([], .Nat)).get n).toList == (enumT 3 6 4 ([], .Nat)).get n)

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval ((List.range 4).map fun n =>
  ((enumL 3 6 4 ([], .Fun .Nat .Nat)).get n).toList == (enumT 3 6 4 ([], .Fun .Nat .Nat)).get n)

-- `take` reads the same prefix `toList` would, without building the rest.
/-- info: true -/
#guard_msgs in
#eval ((enumL 3 6 4 ([], .Nat)).get 3).take 5 == ((enumT 3 6 4 ([], .Nat)).get 3).take 5
