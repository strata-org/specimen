module

public import Specimen.Enum.Laws.BacktrackWith
public import Specimen.Enum.Search

/-!
# A search answers what the enumeration lists

`SearchesAs y x` relates a generator with labelled failures at `ExceptT ε Finite` to its run at
`Search`: where the enumeration is defined, the search's answer to every continuation is the Kleene
disjunction, in order, of what the enumeration lists, a success answering as the continuation does on
it and a label undecided. It is a `GenRel`, so `walk` proves it of a derived enumerator: a derived
checker's search then answers as reading its premise's whole enumeration would, and stops sooner.
-/

@[expose] public section

open Lean.Order

namespace Specimen

variable {ε α β : Type}

namespace Finite

/-- The disjunction, in order, of `v` on each value of a defined set; `undef` for `undef`. -/
def verdict (x : Finite α) (v : α → Verdict) : Verdict :=
  match x with
  | .undef => .undef
  | .mk _ f => Verdict.any (List.ofFn fun i _ => v (f i))

theorem verdict_mk (n : Nat) (f : Fin n → α) (v : α → Verdict) :
    (Finite.mk n f).verdict v = Verdict.any ((List.ofFn f).map fun a _ => v a) := by
  rw [List.map_ofFn]
  rfl

theorem verdict_singleton (a : α) (v : α → Verdict) : (Finite.singleton a).verdict v = v a := by
  simp [verdict, Finite.singleton, Verdict.any]

theorem ofFn_union (m n : Nat) (f : Fin m → α) (g : Fin n → α) :
    List.ofFn (fun i : Fin (m + n) =>
        if h : i.val < m then f ⟨i.val, h⟩ else g ⟨i.val - m, by have := i.isLt; omega⟩) =
      List.ofFn f ++ List.ofFn g := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]

theorem verdict_union {x y : Finite α} (hx : x ≠ .undef) (hy : y ≠ .undef) (v : α → Verdict) :
    (x.union y).verdict v = Verdict.orElse (x.verdict v) (fun _ => y.verdict v) := by
  cases x with
  | undef => exact absurd rfl hx
  | mk m f =>
    cases y with
    | undef => exact absurd rfl hy
    | mk n g =>
      simp only [union, verdict_mk, ofFn_union, List.map_append, Verdict.any_append]

theorem verdict_flatten {xs : List (Finite α)} (h : flatten xs ≠ .undef) (v : α → Verdict) :
    (flatten xs).verdict v = Verdict.any (xs.map fun x _ => x.verdict v) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hu : x.union (flatten xs) ≠ .undef := h
    obtain ⟨hx, hxs⟩ := union_ne_undef hu
    show (x.union (flatten xs)).verdict v = _
    rw [verdict_union hx hxs, ih hxs]
    rfl

theorem verdict_bind {x : Finite α} {f : α → Finite β} (h : x.bind f ≠ .undef) (v : β → Verdict) :
    (x.bind f).verdict v = x.verdict fun a => (f a).verdict v := by
  cases x with
  | undef => exact absurd rfl h
  | mk n index =>
    have h' : flatten (List.ofFn fun i => f (index i)) ≠ .undef := h
    show (flatten _).verdict v = _
    rw [verdict_flatten h', List.map_ofFn]
    rfl

theorem verdict_congr {x : Finite α} {v w : α → Verdict} (h : ∀ a, x.Mem a → v a = w a) :
    x.verdict v = x.verdict w := by
  cases x with
  | undef => rfl
  | mk n f =>
    show Verdict.any _ = Verdict.any _
    exact congrArg Verdict.any (congrArg List.ofFn
      (funext fun i => funext fun _ => h _ (mem_mk.mpr ⟨i, rfl⟩)))

end Finite

/-- What a search asks of an entry of an enumeration with labelled failures: of a success, the
continuation; of a label, nothing it can decide. -/
def entryVerdict (k : α → Verdict) : Except ε α → Verdict
  | .ok a => k a
  | .error _ => .unknown

/-- `y`, if defined, lists entries whose disjunction is `x`'s answer to every continuation. -/
def SearchesAs {ε : Type} {α : Type} (y : ExceptT ε Finite α) (x : Search α) : Prop :=
  y.run ≠ .undef → ∀ k, x.run k = y.run.verdict (entryVerdict k)

namespace SearchesAs

theorem pure (a : α) : SearchesAs (Pure.pure a : ExceptT ε Finite α) (Pure.pure a) := fun _ k => by
  show k a = (Finite.singleton (Except.ok a : Except ε α)).verdict (entryVerdict k)
  rw [Finite.verdict_singleton]
  rfl

theorem bind {y : ExceptT ε Finite α} {x : Search α} {k' : α → ExceptT ε Finite β}
    {k : α → Search β} (hk : ∀ a, SearchesAs (k' a) (k a)) (hy : SearchesAs y x) :
    SearchesAs (y >>= k') (x >>= k) := fun hd c => by
  obtain ⟨hyd, hkd⟩ := EnumeratesWith.bind_ne_undef hd
  rw [ExceptT.run_bind] at hd
  show x.run (fun a => (k a).run c) = _
  rw [hy hyd, ExceptT.run_bind]
  change _ = (Finite.bind y.run _).verdict _
  rw [Finite.verdict_bind hd]
  apply Finite.verdict_congr
  intro r hr
  cases r with
  | ok a => exact hk a (hkd a hr) c
  | error e =>
    show Verdict.unknown = (Finite.singleton (Except.error e : Except ε β)).verdict (entryVerdict c)
    rw [Finite.verdict_singleton]
    rfl

theorem map {y : ExceptT ε Finite α} {x : Search α} (f : α → β) (hy : SearchesAs y x) :
    SearchesAs (f <$> y) (f <$> x) := by
  rw [EnumeratesWith.map_eq_bind]
  exact bind (fun a => pure (f a)) hy

theorem default (x : Search α) : SearchesAs (Inhabited.default : ExceptT ε Finite α) x :=
  fun h => absurd rfl h

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    SearchesAs (RandomChoice.choose lo hi h : ExceptT ε Finite _) (RandomChoice.choose lo hi h) :=
  fun _ _ => rfl

theorem admissible (x : Search α) :
    Lean.Order.admissible fun y : ExceptT ε Finite α => SearchesAs y x :=
  Finite.admissible_defined (α := Except ε α) _

theorem fail : SearchesAs (Fail.fail : ExceptT ε Finite α) (Fail.fail : Search α) :=
  fun _ _ => rfl

theorem failWith (e : ε) : SearchesAs (FailWith.failWith e : ExceptT ε Finite α)
    (FailWith.failWith e : Search α) :=
  fun _ _ => rfl

theorem seq {f : ExceptT ε Finite (α → β)} {f' : Search (α → β)} {y : ExceptT ε Finite α}
    {x : Search α} (hf : SearchesAs f f') (hy : SearchesAs y x) : SearchesAs (f <*> y) (f' <*> x) :=
  bind (fun g => map g hy) hf

end SearchesAs

@[walk_rel]
theorem genRel_searchesAs : GenRel (ExceptT ε Finite) Search (@SearchesAs ε) where
  pure := SearchesAs.pure
  bind := SearchesAs.bind
  map := SearchesAs.map
  default := SearchesAs.default
  choose := SearchesAs.choose
  admissible := SearchesAs.admissible

attribute [gen_rule] SearchesAs.fail SearchesAs.failWith SearchesAs.seq

/-! ## The rules for choice -/

namespace SearchesAs

/-- The runs of an enumeration's branches of positive weight, in order: what its union lists. -/
def posRuns (gs' : List (Nat × (Unit → ExceptT ε Finite α))) : List (Finite (Except ε α)) :=
  (gs'.map fun p => (p.1, fun u => (p.2 u).run)).filterMap fun p =>
    if p.1 = 0 then none else some (p.2 ())

theorem run_branches (gs : List (Nat × (Unit → Search α))) (c : α → Verdict) :
    (Search.branches gs).run c = Verdict.any ((gs.filter (·.1 != 0)).map fun p _ => (p.2 ()).run c) :=
  rfl

/-- The search's branches of positive weight, in order, answer as the union of the enumeration's. -/
theorem branches {gs' : List (Nat × (Unit → ExceptT ε Finite α))} {gs : List (Nat × (Unit → Search α))}
    (hs : GenRel.Weighted (@SearchesAs ε) gs' gs) :
    Finite.flatten (posRuns gs') ≠ .undef → ∀ c,
      (Search.branches gs).run c = (Finite.flatten (posRuns gs')).verdict (entryVerdict c) := by
  induction hs with
  | nil => intro _ _; rfl
  | @cons w g' g gs' gs h _ ih =>
    intro hd c
    rw [run_branches]
    by_cases hw : w = 0
    · have e : posRuns ((w, g') :: gs') = posRuns gs' := by simp [posRuns, hw]
      rw [e] at hd ⊢
      rw [← ih hd c, run_branches]
      simp [hw]
    · have e : posRuns ((w, g') :: gs') = (g' ()).run :: posRuns gs' := by simp [posRuns, hw]
      rw [e] at hd ⊢
      have hu : ((g' ()).run).union (Finite.flatten (posRuns gs')) ≠ .undef := hd
      obtain ⟨hg, hrest⟩ := Finite.union_ne_undef hu
      show _ = (((g' ()).run).union (Finite.flatten (posRuns gs'))).verdict _
      rw [Finite.verdict_union hg hrest, ← h hg c, ← ih hrest c, run_branches]
      simp [hw, Verdict.any]

/-- The search tries the branches the union lists, in its order. -/
@[gen_rule]
theorem backtrack {gs' : List (Nat × (Unit → ExceptT ε Finite α))} {gs : List (Nat × (Unit → Search α))}
    (hs : GenRel.Weighted (@SearchesAs ε) gs' gs) :
    SearchesAs (Backtrack.backtrack gs' : ExceptT ε Finite α) (Backtrack.backtrack gs) :=
  fun hd c => branches hs hd c

/-- The same for the draw, which at both readings is the choice among its branches. -/
@[gen_rule]
theorem pick {gs' : List (Nat × (Unit → ExceptT ε Finite α))} {gs : List (Nat × (Unit → Search α))}
    (hs : GenRel.Weighted (@SearchesAs ε) gs' gs) {h' : 0 < Backtrack.sumWeights gs'}
    {h : 0 < Backtrack.sumWeights gs} :
    SearchesAs (Pick.pick gs' h' : ExceptT ε Finite α) (Pick.pick gs h) :=
  backtrack hs

end SearchesAs

end Specimen
