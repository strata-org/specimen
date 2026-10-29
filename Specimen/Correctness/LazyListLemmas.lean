import Specimen.LazyList

/-!
# Bridge lemmas from `List` to `LazyList`

`LazyList` recurses under `Thunk`, so its induction principle is a mutual recursor that is awkward
to drive directly, and `bindLazyList`/`roundRobinConcat` are `partial`. For correctness proofs we
therefore build finite enumerations as ordinary `List`s (clean recursor, rich core `List.mem_*`
API) and convert to `LazyList` with `fromList` at the boundary. These lemmas are the bridge:
`fromList` preserves membership, so all reasoning happens over `List`.
-/

namespace LazyList

@[simp] theorem fromList_nil {α} : fromList ([] : List α) = lnil := rfl

@[simp] theorem fromList_cons {α} (a : α) (l : List α) :
    fromList (a :: l) = lcons a ⟨fun _ => fromList l⟩ := rfl

/-- Membership in a cons cell: the element is the head, or is (distinct from the head and) in the
    tail. The `a ≠ b` in `InLNext` is discharged by classical case analysis. -/
theorem mem_lcons {α} {a b : α} {tl : Thunk (LazyList α)} :
    a ∈ lcons b tl ↔ a = b ∨ a ∈ tl.get := by
  constructor
  · intro h
    cases h with
    | InLHead _ => exact Or.inl rfl
    | InLNext _ _ _ hin => exact Or.inr hin
  · intro h
    rcases h with rfl | hin
    · exact InLazyList.InLHead _
    · by_cases hab : a = b
      · subst hab; exact InLazyList.InLHead _
      · exact InLazyList.InLNext _ _ hab hin

/-- `fromList` preserves membership: `LazyList` membership of `fromList l` matches `List` membership
    of `l`. This is the only `LazyList`-level fact enumerator proofs need. -/
theorem mem_fromList {α} {a : α} {l : List α} : a ∈ fromList l ↔ a ∈ l := by
  induction l with
  | nil => constructor <;> intro h <;> cases h
  | cons b l ih =>
    rw [fromList_cons, mem_lcons, List.mem_cons]
    simp only [Thunk.get, ih]

/-- Membership distributes over `append`.

Unlike `bindLazyList`, `append` is *total* — it recurses under `Thunk` but structurally, so `LazyList`
gives it a usable induction principle. That matters because `EnumeratorCombinators.enumerate` is built
only from `append` (`enumerateAll` is a `foldr` of it), so the emitted enumerator's **branch-combining**
step is equationally reachable even though its `bind` is not. See the note in `ProducerInterp.lean` on
what is and is not bridgeable for enumerators. -/
theorem mem_append {α} {a : α} : ∀ (xs ys : LazyList α),
    a ∈ LazyList.append xs ys ↔ a ∈ xs ∨ a ∈ ys
  | lnil, ys => by
    simp only [LazyList.append]
    constructor
    · exact Or.inr
    · intro h; rcases h with h | h
      · cases h
      · exact h
  | lcons x xs, ys => by
    simp only [LazyList.append]
    rw [mem_lcons, mem_lcons]
    show a = x ∨ a ∈ LazyList.append xs.get ys ↔ (a = x ∨ a ∈ xs.get) ∨ a ∈ ys
    rw [mem_append xs.get ys]
    constructor
    · rintro (rfl | h | h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((rfl | h) | h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end LazyList
