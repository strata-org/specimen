import Specimen.Correctness.SearchHits
import Specimen.Correctness.LawClasses
import Specimen.BasaltBridge
import Specimen.Correctness.Combinators

/-!
# Completeness laws for enumerators and the searches checkers make with them

A derived checker that needs a witness for a premise searches for it with the premise's enumerator
(`Specimen.CheckerSearch`, which runs `EnumFor.enum` at `Search`). For the checker to be complete, the
search must find a witness whenever one exists: the enumerator, read at `SGen`, produces it
(`EnumForComplete`, the enumerator's `W.complete` at its instance), the search reaches what the
enumerator produces (`SearchHits`, `EnumForSearch` at the instance), by `walk` over the worker.
`CheckerSearchComplete` is what the checker's proof uses.
-/

open Plausible Basalt Specimen

namespace Specimen.Correctness

variable {α : Type}

/-- Every value satisfying `P` is enumerated, at the `SGen` reading, at every large enough size and
leaf size. The enumerator's counterpart of `BacktrackGenForComplete`. -/
class EnumForComplete (α : Type) (P : α → Prop) [EnumFor α P] : Prop where
  complete : ∀ x, P x → ∃ n, ∀ s l, n ≤ s → n ≤ l →
    Produces (EnumFor.enum (P := P) (G := SGen) s l) x

/-- The enumerator's search reaches what it produces. -/
class EnumForSearch (α : Type) (P : α → Prop) [EnumFor α P] : Prop where
  hits : ∀ s l, SearchHits (EnumFor.enum (P := P) (G := SGen) s l) (EnumFor.enum (P := P) (G := Search) s l)

/-- A search for a witness of `P` accepts, at every large enough size, a continuation that accepts a
witness. -/
class CheckerSearchComplete (α : Type) (P : α → Prop) [Specimen.CheckerSearch α P] : Prop where
  complete : ∀ x, P x → ∃ n, ∀ s l, n ≤ s → n ≤ l → ∀ k : α → Except GenError Bool, k x = .ok true →
    Specimen.CheckerSearch.search (P := P) s l k = .ok true

/-- A call of another enumerator, under the walk of a search: by its instance's law. -/
@[gen_rule] theorem EnumForSearch.hits' {P : α → Prop} [EnumFor α P] [EnumForSearch α P] (s l : Nat) :
    SearchHits (EnumFor.enum (P := P) (G := SGen) s l) (EnumFor.enum (P := P) (G := Search) s l) :=
  EnumForSearch.hits s l

/-! ### An equation's enumerator: `pure` of its one solution -/

theorem reach_enum_eqRight {α : Type} (val : α) (s l : Nat) :
    Produces (EnumFor.enum (P := fun x => x = val) (G := SGen) s l) val :=
  produces_pure_iff.mpr rfl

theorem reach_enum_eqLeft {α : Type} (val : α) (s l : Nat) :
    Produces (EnumFor.enum (P := fun x => val = x) (G := SGen) s l) val :=
  produces_pure_iff.mpr rfl

instance {α : Type} {val : α} : EnumForComplete α (fun x => x = val) :=
  ⟨fun x hx => ⟨0, fun s l _ _ => hx ▸ reach_enum_eqRight val s l⟩⟩
instance {α : Type} {val : α} : EnumForComplete α (fun x => val = x) :=
  ⟨fun x hx => ⟨0, fun s l _ _ => hx ▸ reach_enum_eqLeft val s l⟩⟩
instance {α : Type} {val : α} : EnumForSearch α (fun x => x = val) :=
  ⟨fun _ _ => SearchHits.pure val⟩
instance {α : Type} {val : α} : EnumForSearch α (fun x => val = x) :=
  ⟨fun _ _ => SearchHits.pure val⟩

namespace EnumForComplete
variable {P : α → Prop} [EnumFor α P] [EnumForComplete α P]

noncomputable def bound (x : α) (h : P x) : Nat := Classical.choose (complete x h)

theorem produces {x : α} (h : P x) {s l : Nat} (hs : bound x h ≤ s) (hl : bound x h ≤ l) :
    Produces (EnumFor.enum (P := P) (G := SGen) s l) x :=
  Classical.choose_spec (complete x h) s l hs hl

end EnumForComplete

namespace CheckerSearchComplete
variable {P : α → Prop} [Specimen.CheckerSearch α P] [CheckerSearchComplete α P]

noncomputable def bound (x : α) (h : P x) : Nat := Classical.choose (complete x h)

/-- The search accepts: from the witness, which a hypothesis supplies, and the continuation's verdict
on it. -/
theorem ok {x : α} (h : P x) {s l : Nat} (hs : bound x h ≤ s) (hl : bound x h ≤ l)
    {k : α → Except GenError Bool} (hk : k x = .ok true) :
    Specimen.CheckerSearch.search (P := P) s l k = .ok true :=
  Classical.choose_spec (complete x h) s l hs hl k hk

end CheckerSearchComplete

/-- The search an enumerator's checker makes is complete, from the enumerator's laws. -/
instance (priority := low) {P : α → Prop} [EnumFor α P] [EnumForComplete α P] [EnumForSearch α P] :
    CheckerSearchComplete α P where
  complete x hx := by
    obtain ⟨n, hn⟩ := EnumForComplete.complete (P := P) x hx
    exact ⟨n, fun s l hs hl k hk =>
      search_yes (EnumForSearch.hits s l) (hn s l hs hl) hk⟩

/-- A checker's search with an enumerator of its own block (`Specimen.searchWorker`) accepts what the
enumerator produces and the continuation accepts. -/
theorem searchWorker_ok {g : SGen α} {x : Search α} (hh : SearchHits g x) {a : α}
    (ha : Produces g a) {k : α → Except GenError Bool} (hk : k a = .ok true) :
    Specimen.searchWorker x k = .ok true :=
  search_yes hh ha hk

/-- An unconstrained draw's search reaches what the draw produces: what a derived
enumerator's searches need of the types it draws freely (the completeness counterpart of
`ArbitrarySizedSearch`). -/
class ArbitrarySizedHits (α : Type) [Basalt.ArbitrarySized α] : Prop where
  hits : ∀ n, SearchHits (Basalt.ArbitrarySized.arbitrarySized (G := SGen) n : SGen α)
    (Basalt.ArbitrarySized.arbitrarySized (G := Search) n : Search α)

attribute [gen_rule] ArbitrarySizedHits.hits

/-- The law of an instance whose body `walk` relates. -/
macro "arbitrary_hits" : term => `(⟨by intro n; unfold_arbitrary; walk⟩)

instance : ArbitrarySizedHits Nat := arbitrary_hits
instance : ArbitrarySizedHits Bool := arbitrary_hits
instance : ArbitrarySizedHits Unit := arbitrary_hits
instance : ArbitrarySizedHits Int := arbitrary_hits
instance : ArbitrarySizedHits Char := arbitrary_hits
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedHits α] : ArbitrarySizedHits (Option α) :=
  arbitrary_hits
instance {α β : Type} [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [ArbitrarySizedHits α]
    [ArbitrarySizedHits β] : ArbitrarySizedHits (α × β) := arbitrary_hits
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedHits α] : ArbitrarySizedHits (List α) :=
  arbitrary_hits
instance : ArbitrarySizedHits String := arbitrary_hits

/-- A checker's search over the unconstrained values of `α` (`CheckerSearchAll`, for a premise's
witness its inputs do not fix) accepts a value the draw reaches at the leaf size and the rest of the
check accepts: the completeness counterpart of `checkerSearchAll_accepts`. -/
theorem checkerSearchAll_ok {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedHits α]
    [ArbitrarySizedComplete α] {x : α} {l : Nat} (hl : ArbitrarySizedComplete.bound x ≤ l)
    {k : α → Except GenError Bool} (hk : k x = .ok true) :
    Specimen.CheckerSearchAll.search (α := α) l k = .ok true :=
  search_yes (ArbitrarySizedHits.hits l) (ArbitrarySizedComplete.produces hl) hk


end Specimen.Correctness
