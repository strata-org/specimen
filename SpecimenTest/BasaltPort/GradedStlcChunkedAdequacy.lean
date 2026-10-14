import Basalt.GradedChunked
import SpecimenTest.BasaltPort.GradedStlcLazyAdequacy

/-!
# STLC on the chunked-level carrier

The same result as `GradedStlcAdequacy.lean` (strict levels) and `GradedStlcLazyAdequacy.lean` (lazy
levels), on `Basalt/GradedChunked.lean`'s `Array (Thunk (LList (List α)))`: a level is a lazy list of
strict chunks of at least `C` elements. Mechanically translated from the lazy file; the chunk size `C` is
threaded as a parameter and **holds for every `C`**, so the choice is purely a performance one. Membership
is in the flattened level; `stlc_takeC_sound` says the first `k` terms read chunk by chunk are well typed.
-/

open Basalt

/-! ## The system at `LvC`

Each definition mirrors its `Lv` counterpart operation for operation, with `N` threaded. -/

/-- `Nat` graded by magnitude, at width `N + 1`. -/
def natStepC (N C : Nat) (rec : LvC Nat) : LvC Nat :=
  LvC.union C (LvC.single N 0) (LvC.pay (LvC.gmap (· + 1) rec))

/-- `type` graded by size, at width `N + 1`. -/
def typeStepC (N C : Nat) (rec : LvC type) : LvC type :=
  LvC.union C (LvC.single N type.Nat)
    (LvC.pay (LvC.gmap (fun p => type.Fun p.1 p.2) (LvC.pair C rec rec)))

/-- The de Bruijn indices at which `Γ` holds `τ`, at width `N + 1`. Structurally recursive on `Γ`, exactly
as `lookupEnum` is — the width is threaded unchanged. -/
def lookupEnumC (N C : Nat) : List type → type → LvC Nat
  | [], _ => LvC.nothing N
  | σ :: Γ, τ =>
      LvC.union C (if σ = τ then LvC.single N 0 else LvC.nothing N)
        (LvC.pay (LvC.gmap (· + 1) (lookupEnumC N C Γ τ)))

/-- The `TApp`-free fragment at width `N + 1`. -/
def stlcAFStepC (N C : Nat) (natE : LvC Nat) (rec : TyIx → LvC term) : TyIx → LvC term
  | (Γ, .Nat) =>
      LvC.union C (LvC.gmap term.Var (lookupEnumC N C Γ .Nat))
        (LvC.union C (LvC.gmap term.Const natE)
          (LvC.pay (LvC.gmap (fun p => term.Add p.1 p.2)
            (LvC.pair C (rec (Γ, .Nat)) (rec (Γ, .Nat))))))
  | (Γ, .Fun τ1 τ2) =>
      LvC.union C (LvC.gmap term.Var (lookupEnumC N C Γ (.Fun τ1 τ2)))
        (LvC.pay (LvC.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))))

/-- The full system at width `N + 1`. `LvC.bindC C` is the correlated premise, same as at `Lv`. -/
def stlcStepC (N C : Nat) (natE : LvC Nat) (typeE : LvC type) (rec : TyIx → LvC term) :
    TyIx → LvC term
  | (Γ, τ) =>
      LvC.union C (stlcAFStepC N C natE rec (Γ, τ))
        (LvC.pay (LvC.bindC C typeE (fun τ1 =>
          LvC.gmap (fun p => term.App p.1 p.2)
            (LvC.pair C (rec (Γ, .Fun τ1 τ)) (rec (Γ, τ1))))))

/-- `gradedIter` at `LvC`. The base case has to *name* the width — that is the one place the carrier's
explicit size cannot be inferred from an operand. -/
def gradedIterC {α : Type} (N C : Nat) (step : LvC α → LvC α) : Nat → LvC α
  | 0 => LvC.nothing N
  | l + 1 => step (gradedIterC N C step l)

/-- `gradedIterIx` at `LvC`. Same remark about the base case. -/
def gradedIterIxC {α ι : Type} (N C : Nat) (step : (ι → LvC α) → ι → LvC α) : Nat → ι → LvC α
  | 0, _ => LvC.nothing N
  | l + 1, i => step (gradedIterIxC N C step l) i

/-! ## The width invariant

Every enumeration above has width exactly `N + 1`. These are what discharge the size side conditions on
`AgreeC.union` / `.pair` / `.bindC`; without them the carrier change does not go through. -/

@[simp] theorem sizeC_natStepC (N C : Nat) (rec : LvC Nat) : (natStepC N C rec).size = N + 1 := by
  simp [natStepC]

@[simp] theorem sizeC_typeStepC (N C : Nat) (rec : LvC type) : (typeStepC N C rec).size = N + 1 := by
  simp [typeStepC]

@[simp] theorem sizeC_lookupEnumC (N C : Nat) (τ : type) : ∀ Γ : List type,
    (lookupEnumC N C Γ τ).size = N + 1
  | [] => by simp [lookupEnumC]
  | σ :: Γ => by
      rw [lookupEnumC, LvC.size_union]
      by_cases h : σ = τ <;> simp [h]

@[simp] theorem sizeC_stlcAFStepC (N C : Nat) (natE : LvC Nat) (rec : TyIx → LvC term) (i : TyIx) :
    (stlcAFStepC N C natE rec i).size = N + 1 := by
  obtain ⟨Γ, τ⟩ := i
  cases τ <;> simp [stlcAFStepC]

@[simp] theorem sizeC_stlcStepC (N C : Nat) (natE : LvC Nat) (typeE : LvC type)
    (rec : TyIx → LvC term) (i : TyIx) : (stlcStepC N C natE typeE rec i).size = N + 1 := by
  obtain ⟨Γ, τ⟩ := i
  simp [stlcStepC]

theorem sizeC_gradedIterC {α : Type} (N C : Nat) {step : LvC α → LvC α}
    (hs : ∀ x, (step x).size = N + 1) : ∀ l, (gradedIterC N C step l).size = N + 1
  | 0 => by simp [gradedIterC]
  | _ + 1 => hs _

theorem sizeC_gradedIterIxC {α ι : Type} (N C : Nat) {step : (ι → LvC α) → ι → LvC α}
    (hs : ∀ x i, (step x i).size = N + 1) : ∀ l i, (gradedIterIxC N C step l i).size = N + 1
  | 0, _ => by simp [gradedIterIxC]
  | _ + 1, i => hs _ i

/-! ## Agreement with the `Lv` system

Nothing about `Agrees` or `SubE` is reproved: every step below is an application of a closure lemma from
`Basalt/GradedRun.lean`, plus a size obligation discharged by the invariant above. The one piece of
plumbing `GradedRun` does not ship is the `ite` case, needed for `lookupEnum`'s `σ = τ` side condition. -/

theorem agreeC_natStepC (N C : Nat) {rec : LvC Nat} {m : Lv Nat}
    (h : AgreeC rec m) (hsz : rec.size = N + 1) : AgreeC (natStepC N C rec) (natStep m) :=
  (agreeC_single N 0).union ((h.gmap _).pay) (by simp [hsz])

theorem agreeC_typeStepC (N C : Nat) {rec : LvC type} {m : Lv type}
    (h : AgreeC rec m) (hsz : rec.size = N + 1) : AgreeC (typeStepC N C rec) (typeStep m) :=
  (agreeC_single N type.Nat).union (((h.pair h rfl).gmap _).pay) (by simp [hsz])

theorem agreeC_lookupEnumC (N C : Nat) (τ : type) : ∀ Γ : List type,
    AgreeC (lookupEnumC N C Γ τ) (lookupEnum Γ τ)
  | [] => agreeC_nothing N
  | σ :: Γ => by
      rw [lookupEnumC, lookupEnum]
      refine AgreeC.union (AgreeC.ite (agreeC_single N 0) (agreeC_nothing N))
        (((agreeC_lookupEnumC N C τ Γ).gmap _).pay) ?_
      by_cases h : σ = τ <;> simp [h]

theorem agreeC_stlcAFStepC (N C : Nat) {natE : LvC Nat} {natM : Lv Nat}
    (hn : AgreeC natE natM) (hnsz : natE.size = N + 1)
    {rec : TyIx → LvC term} {m : TyIx → Lv term}
    (h : ∀ i, AgreeC (rec i) (m i)) (hsz : ∀ i, (rec i).size = N + 1) :
    ∀ i, AgreeC (stlcAFStepC N C natE rec i) (stlcAFStep natM m i) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
    exact ((agreeC_lookupEnumC N C _ Γ).gmap _).union
      ((hn.gmap _).union
        ((((h (Γ, .Nat)).pair (h (Γ, .Nat)) rfl).gmap _).pay) (by simp [hsz, hnsz]))
      (by simp [hnsz])
  | Fun τ1 τ2 =>
    exact ((agreeC_lookupEnumC N C _ Γ).gmap _).union
      (((h (τ1 :: Γ, τ2)).gmap _).pay) (by simp [hsz])

theorem agreeC_stlcStepC (N C : Nat) {natE : LvC Nat} {natM : Lv Nat}
    (hn : AgreeC natE natM) (hnsz : natE.size = N + 1)
    {typeE : LvC type} {typeM : Lv type}
    (ht : AgreeC typeE typeM) (htsz : typeE.size = N + 1)
    {rec : TyIx → LvC term} {m : TyIx → Lv term}
    (h : ∀ i, AgreeC (rec i) (m i)) (hsz : ∀ i, (rec i).size = N + 1) :
    ∀ i, AgreeC (stlcStepC N C natE typeE rec i) (stlcStep natM typeM m i) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  exact (agreeC_stlcAFStepC N C hn hnsz h hsz (Γ, τ)).union
    ((ht.bindC (fun τ1 => (((h (Γ, .Fun τ1 τ)).pair (h (Γ, τ1)) (by simp [hsz])).gmap _))
        (fun _ => by simp [hsz, htsz])).pay)
    (by simp [htsz])

theorem agreeC_gradedIterC {α : Type} (N C : Nat) {stepT : LvC α → LvC α} {step : Lv α → Lv α}
    (hstep : ∀ x m, AgreeC x m → x.size = N + 1 → AgreeC (stepT x) (step m))
    (hsize : ∀ x, (stepT x).size = N + 1) :
    ∀ l, AgreeC (gradedIterC N C stepT l) (gradedIter step l)
  | 0 => agreeC_nothing N
  | l + 1 =>
      hstep _ _ (agreeC_gradedIterC N C hstep hsize l) (sizeC_gradedIterC N C hsize l)

theorem agreeC_gradedIterIxC {α ι : Type} (N C : Nat) {stepT : (ι → LvC α) → ι → LvC α}
    {step : (ι → Lv α) → ι → Lv α}
    (hstep : ∀ x m, (∀ i, AgreeC (x i) (m i)) → (∀ i, (x i).size = N + 1) →
      ∀ i, AgreeC (stepT x i) (step m i))
    (hsize : ∀ x i, (stepT x i).size = N + 1) :
    ∀ l i, AgreeC (gradedIterIxC N C stepT l i) (gradedIterIx step l i)
  | 0, _ => agreeC_nothing N
  | l + 1, i =>
      hstep _ _ (agreeC_gradedIterIxC N C hstep hsize l) (sizeC_gradedIterIxC N C hsize l) i

/-! ## The executable enumeration, and its agreement -/

/-- **The STLC enumeration that runs.** Array width `N + 1` (levels `0..N`), leaf budget `L`, `levels`
iterations. Definitionally the `Lv` enumeration of `stlc_mem_iff_budget` with `LvC` operations in place of
`Lv` ones and the width threaded. -/
def enumC (N C L levels : Nat) : TyIx → LvC term :=
  gradedIterIxC N C
    (stlcStepC N C (gradedIterC N C (natStepC N C) L) (gradedIterC N C (typeStepC N C) L)) levels

@[simp] theorem sizeC_enumC (N C L levels : Nat) (i : TyIx) : (enumC N C L levels i).size = N + 1 :=
  sizeC_gradedIterIxC N C (fun _ _ => sizeC_stlcStepC ..) levels i

/-- **The carrier change is sound and loses nothing within the width.** Every level the array stores reads
exactly as the `Lv` enumeration does. -/
theorem agreeC_enumC (N C L levels : Nat) (i : TyIx) :
    AgreeC (enumC N C L levels i) (enumLv L levels i) :=
  agreeC_gradedIterIxC N C
    (fun _ _ hx hsz =>
      agreeC_stlcStepC N C
        (agreeC_gradedIterC N C (fun _ _ h hs => agreeC_natStepC N C h hs) (fun _ => sizeC_natStepC ..) L)
        (sizeC_gradedIterC N C (fun _ => sizeC_natStepC ..) L)
        (agreeC_gradedIterC N C (fun _ _ h hs => agreeC_typeStepC N C h hs) (fun _ => sizeC_typeStepC ..) L)
        (sizeC_gradedIterC N C (fun _ => sizeC_typeStepC ..) L)
        hx hsz)
    (fun _ _ => sizeC_stlcStepC ..) levels i

/-- The level-by-level form, for a caller whose width is already fixed. -/
theorem mem_enumC_iff (N C L levels : Nat) (i : TyIx) (n : Nat) (hn : n < N + 1) (e : term) :
    e ∈ (enumC N C L levels i).flat n ↔ e ∈ enumLv L levels i n := by
  rw [agreeC_enumC N C L levels i n (by simpa using hn)]

/-- **`typing` is exactly the enumeration that runs.**

Same content as `stlc_mem_iff_budget`, on `Array (Thunk (List term))` instead of `Nat → List term` — so
the theorem is now about code with the right cost model: levels are memoised by the array and deferred by
the thunks, rather than recomputed `(k+1)^n` times by a function carrier.

The extra `N` is the array width and the extra `n < N + 1` is `Agree`'s bound. Neither weakens the
biconditional: `→` produces its own level and may take `N := n`; `←` is the `Lv` soundness result
transported over one level the array actually stores. -/
theorem stlc_mem_iff_runC (C : Nat) (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ N L levels n, n < N + 1 ∧ e ∈ (enumC N C L levels (Γ, τ)).flat n := by
  rw [stlc_mem_iff_budget Γ e τ]
  constructor
  · rintro ⟨L, levels, n, h⟩
    exact ⟨n, L, levels, n, Nat.lt_succ_self n,
      (mem_enumC_iff n C L levels (Γ, τ) n (Nat.lt_succ_self n) e).mpr h⟩
  · rintro ⟨N, L, levels, n, hn, h⟩
    exact ⟨L, levels, n, (mem_enumC_iff N C L levels (Γ, τ) n hn e).mp h⟩


/-- **Reading chunk by chunk is sound.** Any term among the first `k` read from any level of the chunked
enumeration is well typed — only the chunks up to the `k`-th term are forced. -/
theorem stlc_takeC_sound {C : Nat} {Γ : List type} {τ : type} {N L levels n k : Nat} (hn : n < N + 1)
    {e : term} (h : e ∈ LList.takeC k ((enumC N C L levels (Γ, τ)).get n)) : typing Γ e τ := by
  rw [LList.takeC_eq] at h
  exact (stlc_mem_iff_runC C Γ e τ).2 ⟨N, L, levels, n, hn, List.mem_of_mem_take h⟩

/-! ## The carrier change did not alter the enumeration, checked by evaluation

At three chunk sizes: 1 (every element its own chunk, the merge path always taken), 3 (chunks straddle
level boundaries), and the default 256 (every level here is a single chunk). -/

/-- info: [true, true, true] -/
#guard_msgs in
#eval [1, 3, 256].map fun C => (List.range 4).all fun n =>
  (enumC 3 C 6 4 ([], .Nat)).flat n == (enumT 3 6 4 ([], .Nat)).get n

/-- info: [true, true, true] -/
#guard_msgs in
#eval [1, 3, 256].map fun C => (List.range 4).all fun n =>
  (enumC 3 C 6 4 ([], .Fun .Nat .Nat)).flat n == (enumT 3 6 4 ([], .Fun .Nat .Nat)).get n

-- `takeC` reads exactly the prefix the flattening has.
/-- info: [true, true, true] -/
#guard_msgs in
#eval [1, 3, 256].map fun C =>
  LList.takeC 5 ((enumC 3 C 6 4 ([], .Nat)).get 3) == ((enumT 3 6 4 ([], .Nat)).get 3).take 5
