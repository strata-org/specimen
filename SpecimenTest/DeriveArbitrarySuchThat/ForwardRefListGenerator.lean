import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer

/-!
# Forward-referencing variable lists

A list of variables where each variable refers to *one* other variable in the
list.  The point of interest is that an *earlier* variable is allowed to refer
to a *later* one (a forward reference), which a naive left-to-right inductive
construction cannot express directly.

The trick is to thread two accumulators through the relation:

* `seen`  — names already emitted (the prefix), and
* `owed`  — names referenced *forward* but not yet emitted (outstanding promises).

Following the two-rule pitch, each element is added by one of:

* `prefixRef`  — its target is already in `seen` (a backward edge), or
* `forwardRef` — its target is not yet in the list, so we record the name in
  `owed` as a promise to define it later.

plus `fulfillBack`/`fulfillFwd` rules that *define* an arbitrary owed name
(pulling it back out of `owed`) — which is what lets outstanding promises actually
be discharged — and `done`, which may only fire once every promise has been kept
(`owed = []`).  A fulfilling step may itself refer forward (`fulfillFwd`), creating
a new promise, so discharging one obligation can introduce another.

## Efficient fresh names

Rather than "generate a random `Nat` and hope it is fresh" (what a bare
`NotInNat x l` generator does — it rejects almost everything), a *new* name is
chosen by scanning `0, 1, 2, …` and taking any free slot: the least, or the
2nd-least, or the nth-least natural number **not** in `seen ++ owed`.  This keeps
names in a small, bounded pool and never wastes samples.  Here `In`/`NotIn` are
used only as cheap *checks* while scanning; they never have to generate anything.

Per the request, list membership (`InNat`) and non-membership (`NotInNat`) are
given as *concrete inductive relations* over `List Nat` rather than via `∈`/`∉`.
-/

open Plausible
open ArbitrarySizedSuchThat
open Scoring Schedules

/-- `InNat x l` : `x` occurs in `l`. -/
inductive InNat : Nat → List Nat → Prop where
  | here  : InNat x (x :: l)
  | there : InNat x l → InNat x (y :: l)

/-- `NotInNat x l` : `x` does not occur in `l`. -/
inductive NotInNat : Nat → List Nat → Prop where
  | nil  : NotInNat x []
  | cons : x ≠ y → NotInNat x l → NotInNat x (y :: l)

/-- `Fresh cur avoid x` : `x ≥ cur` and `x ∉ avoid`.  Scanning upward from `cur`,
    each free slot may be *taken* or *skipped*, so `x` can be the least, 2nd-least,
    … i.e. *any* nth-smallest natural missing from `avoid`.  `In`/`NotIn` appear
    only as checks, so no candidate is ever generated and rejected. -/
inductive Fresh : Nat → List Nat → Nat → Prop where
  | take     : NotInNat cur avoid → Fresh cur avoid cur
  | skipFree : NotInNat cur avoid → Fresh (cur.succ) avoid x → Fresh cur avoid x
  | skipUsed : InNat cur avoid → Fresh (cur.succ) avoid x → Fresh cur avoid x

/-- Each element is a `(name, ref)` pair: the variable's own name and the name
    of the single variable it refers to. -/
abbrev Var := Nat × Nat

/-- `Chain seen owed l` builds the remaining list `l` given the names already
    emitted (`seen`) and the outstanding forward-reference promises (`owed`).

    Invariant: `seen` and `owed` are disjoint, so a name drawn `Fresh` from
    `seen ++ owed` is genuinely new, and a name drawn from `owed` is guaranteed
    absent from `seen`. -/
inductive Chain : List Nat → List Nat → List Var → Prop where
  /-- Finish only when there are no outstanding promises. -/
  | done {seen} : Chain seen [] []
  /-- Backward edge: a fresh name referring to a name already in the prefix.
      The prefix is matched as `s :: seen` so Specimen knows `seen ≠ []` (a
      backward reference is impossible with an empty prefix anyway). -/
  | prefixRef {s seen owed rest} (x r : Nat) :
      Fresh 0 ((s :: seen) ++ owed) x →
      InNat r (s :: seen) →
      Chain (x :: s :: seen) owed rest →
      Chain (s :: seen) owed ((x, r) :: rest)
  /-- Forward edge: a fresh name referring to another fresh (future) name, which
      is recorded in `owed` as a promise. -/
  | forwardRef {seen owed rest} (x r : Nat) :
      Fresh 0 (seen ++ owed) x →
      Fresh 0 (x :: (seen ++ owed)) r →
      Chain (x :: seen) (r :: owed) rest →
      Chain seen owed ((x, r) :: rest)
  /-- Discharge a promise with a *backward* reference: define an arbitrary owed
      name `o` (removing it from `owed`), referring back into the prefix.  `owed`
      is matched as `ow :: owed` so Specimen knows `owed ≠ []`. -/
  | fulfillBack {seen ow owed rest} (o r : Nat) :
      InNat o (ow :: owed) →
      InNat r seen →
      Chain (o :: seen) ((ow :: owed).erase o) rest →
      Chain seen (ow :: owed) ((o, r) :: rest)
  /-- Discharge a promise with a *forward* reference: define an arbitrary owed
      name `o`, but point it at a fresh future name `r` (added to `owed`).  So a
      fulfilling step can itself create a new promise rather than referring to an
      already-`seen` name. -/
  | fulfillFwd {seen ow owed rest} (o r : Nat) :
      InNat o (ow :: owed) →
      Fresh 0 (o :: (seen ++ (ow :: owed).erase o)) r →
      Chain (o :: seen) (r :: (ow :: owed).erase o) rest →
      Chain seen (ow :: owed) ((o, r) :: rest)

/-- A well-formed forward-referencing list starts with empty accumulators. -/
abbrev WellFormed (l : List Var) : Prop := Chain [] [] l

/-- Weight modifier to steer `Chain` away from the empty list.

    With the default (`balanced`) weights, `done` dominates the root — and at
    `size = 0` the balanced weight function zeroes out every recursive
    constructor, leaving `done` as the *only* option, so ~85% of samples came out
    `[]`.  This modifier only rewrites `Chain`'s own constructors (every other
    relation — `Fresh`, `InNat`, … — passes through untouched):

    * `done` is pinned to weight `1`: available as a terminator (including at
      `size = 0`) but never boosted;
    * the recursive rules get a multiplicative boost *plus an additive floor*, so
      they stay positively weighted even at `size = 0` and can outcompete `done`
      rather than being zeroed out.  `fulfillBack` (the drainer) is floored
      highest so outstanding promises get discharged and `done` can validly fire.

    This drops the empty-list rate from ~85% to ~12% with no generation failures.

    Pattern-matching on the constructor's last name component (`.str _ name`) —
    the modifier fires for every relation in the mutual derivation, so `Chain`'s
    rules and `Fresh`'s rules are both retuned here; everything else falls through
    to `baseWeight`.

    Steering knobs:
    * forward references (`forwardRef`, `fulfillFwd`) are the most likely edges;
    * `fulfillBack` is kept strong (with an additive floor) so promises still drain
      and the chain can terminate;
    * `done` is a rare terminator (weight 1);
    * `Fresh` is tuned (`take = 1`, `skipFree = size`) so the chosen free slot is
      *uniform* over the available range, rather than piling up at the smallest
      value or the size ceiling. -/
def favorNonEmptyChain (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  | .str _ "done"        => 1
  | .str _ "forwardRef"  => baseWeight * 8 + 6   -- favour forward edges most
  | .str _ "fulfillFwd"  => baseWeight * 6 + 4   -- discharge-with-a-new-forward-edge
  | .str _ "fulfillBack" => baseWeight * 5 + 4   -- the drainer: keep it strong
  | .str _ "prefixRef"   => baseWeight * 2 + 1   -- backward fresh edge: least likely
  -- Fresh names: make the chosen free slot *uniform* over the available range.
  -- With `take = 1` and `skipFree = size` (the current fuel), the probability of
  -- taking at fuel `f` is `1/(f+1)`, and the number of skips telescopes to a
  -- uniform distribution over `0..fuel` — so no pile-up at either the smallest
  -- value or the size ceiling.  (At `size = 0`, `skipFree = 0` so `take` fires.)
  | .str _ "skipFree"    => size
  | .str _ "take"        => 1
  | _                    => baseWeight

initialize registerWeightModifier `favorNonEmptyChain favorNonEmptyChain ``favorNonEmptyChain

-- The main event: a generator for whole forward-referencing lists.
set_option specimen.autoDeriveDeps true in
set_option specimen.multiOutput true in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
set_option specimen.weightModifier "favorNonEmptyChain" in
#guard_msgs(drop error, drop info) in
derive_mutual (∃ (l : List Var), Chain [] [] l)

/-! ## Well-formedness theorems

Two properties of any list produced by `Chain [] [] l`:
* its keys are unique (no duplicate variable names), and
* every reference points at some key in the list.

We first bridge the `In`/`NotIn`/`Fresh` relations to list membership, then prove
a generalized invariant by induction on the `Chain` derivation, then specialize to
`Chain [] []`. -/

/-- The keys (defined names) of a chain list. -/
def keys (l : List Var) : List Nat := l.map Prod.fst

@[simp] theorem keys_nil : keys [] = [] := rfl
@[simp] theorem keys_cons (p : Var) (l : List Var) : keys (p :: l) = p.1 :: keys l := rfl

theorem inNat_iff_mem {x : Nat} {l : List Nat} : InNat x l ↔ x ∈ l := by
  constructor
  · intro h
    induction h with
    | here => exact List.mem_cons.mpr (Or.inl rfl)
    | there _ ih => exact List.mem_cons.mpr (Or.inr ih)
  · intro h
    induction l with
    | nil => exact absurd h (by simp)
    | cons y ys ih =>
      rcases List.mem_cons.mp h with rfl | h2
      · exact .here
      · exact .there (ih h2)

theorem notInNat_iff_not_mem {x : Nat} {l : List Nat} : NotInNat x l ↔ x ∉ l := by
  constructor
  · intro h
    induction h with
    | nil => simp
    | cons hne _ ih =>
      simp only [List.mem_cons, not_or]
      exact ⟨hne, ih⟩
  · intro h
    induction l with
    | nil => exact .nil
    | cons y ys ih =>
      simp only [List.mem_cons, not_or] at h
      exact .cons h.1 (ih h.2)

theorem fresh_not_mem {cur x : Nat} {avoid : List Nat} (h : Fresh cur avoid x) : x ∉ avoid := by
  induction h with
  | take hn => exact notInNat_iff_not_mem.mp hn
  | skipFree _ _ ih => exact ih
  | skipUsed _ _ ih => exact ih

/-- If `l₁ ++ l₂` is duplicate-free, `l₁` and `l₂` share no element. -/
theorem nodup_append_disjoint {l₁ l₂ : List Nat} (h : (l₁ ++ l₂).Nodup)
    {a : Nat} (h₁ : a ∈ l₁) (h₂ : a ∈ l₂) : False :=
  (List.nodup_append.mp h).2.2 a h₁ a h₂ rfl

/-- Generalized invariant, proved by induction on the `Chain` derivation.

    The precondition `(seen ++ owed).Nodup` (equivalently: `seen`, `owed` are each
    duplicate-free and disjoint) holds trivially at the top level `[] ++ []` and is
    preserved by every constructor.  It rules out ill-founded sub-derivations like
    `Chain [3] [3] [(3,3)]`, for which the invariant genuinely fails. -/
theorem chain_inv {seen owed : List Nat} {l : List Var} (hc : Chain seen owed l) :
    (seen ++ owed).Nodup →
      (keys l).Nodup ∧
      (∀ k ∈ keys l, k ∉ seen) ∧
      (∀ n ∈ owed, n ∈ keys l) ∧
      (∀ p ∈ l, p.2 ∈ seen ∨ p.2 ∈ keys l) := by
  induction hc with
  | @done seen =>
    intro _; refine ⟨List.nodup_nil, by simp, by simp, by simp⟩
  | @prefixRef s seen owed rest x r hx hr _ ih =>
    intro hnd
    have hxmem : x ∉ (s :: seen) ++ owed := fresh_not_mem hx
    have hnd' : ((x :: s :: seen) ++ owed).Nodup :=
      List.nodup_cons.mpr ⟨hxmem, hnd⟩
    obtain ⟨ihNodup, ihNotSeen, ihOwed, ihRefs⟩ := ih hnd'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [keys_cons]
      exact List.nodup_cons.mpr ⟨fun hxk => ihNotSeen x hxk (List.mem_cons_self ..), ihNodup⟩
    · intro k hk
      simp only [keys_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact fun hks => hxmem (List.mem_append_left _ hks)
      · exact fun hks => ihNotSeen k hk (List.mem_cons_of_mem _ hks)
    · intro n hn
      simp only [keys_cons]
      exact List.mem_cons_of_mem _ (ihOwed n hn)
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inl (inNat_iff_mem.mp hr)
      · rcases ihRefs p hp with h1 | h2
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inr (by simp [keys_cons])
          · exact Or.inl h1
        · exact Or.inr (by simp only [keys_cons]; exact List.mem_cons_of_mem _ h2)
  | @forwardRef seen owed rest x r hx hr _ ih =>
    intro hnd
    have hxmem : x ∉ seen ++ owed := fresh_not_mem hx
    have hrmem : r ∉ x :: (seen ++ owed) := fresh_not_mem hr
    obtain ⟨ndSeen, ndOwed, _⟩ := List.nodup_append.mp hnd
    have hxs : x ∉ seen := fun h => hxmem (List.mem_append_left _ h)
    have hxo : x ∉ owed := fun h => hxmem (List.mem_append_right _ h)
    have hrx : r ≠ x := fun h => hrmem (h ▸ List.mem_cons_self ..)
    have hrs : r ∉ seen := fun h => hrmem (List.mem_cons_of_mem _ (List.mem_append_left _ h))
    have hro : r ∉ owed := fun h => hrmem (List.mem_cons_of_mem _ (List.mem_append_right _ h))
    have hnd' : ((x :: seen) ++ (r :: owed)).Nodup := by
      refine List.nodup_append.mpr ⟨List.nodup_cons.mpr ⟨hxs, ndSeen⟩,
        List.nodup_cons.mpr ⟨hro, ndOwed⟩, ?_⟩
      intro a ha b hb hab
      subst hab
      rcases List.mem_cons.mp ha with rfl | ha
      · rcases List.mem_cons.mp hb with hb | hb
        · exact hrx hb.symm
        · exact hxo hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact hrs ha
        · exact nodup_append_disjoint hnd ha hb
    obtain ⟨ihNodup, ihNotSeen, ihOwed, ihRefs⟩ := ih hnd'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [keys_cons]
      exact List.nodup_cons.mpr ⟨fun hxk => ihNotSeen x hxk (List.mem_cons_self ..), ihNodup⟩
    · intro k hk
      simp only [keys_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact hxs
      · exact fun hks => ihNotSeen k hk (List.mem_cons_of_mem _ hks)
    · intro n hn
      simp only [keys_cons]
      exact List.mem_cons_of_mem _ (ihOwed n (List.mem_cons_of_mem _ hn))
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine Or.inr ?_
        simp only [keys_cons]
        exact List.mem_cons_of_mem _ (ihOwed r (List.mem_cons_self ..))
      · rcases ihRefs p hp with h1 | h2
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inr (by simp [keys_cons])
          · exact Or.inl h1
        · exact Or.inr (by simp only [keys_cons]; exact List.mem_cons_of_mem _ h2)
  | @fulfillBack seen ow owed rest o r ho hr _ ih =>
    intro hnd
    obtain ⟨ndSeen, ndOwed, _⟩ := List.nodup_append.mp hnd
    have homem : o ∈ ow :: owed := inNat_iff_mem.mp ho
    have hos : o ∉ seen := fun h => nodup_append_disjoint hnd h homem
    have hoe : o ∉ (ow :: owed).erase o := ndOwed.not_mem_erase
    have hnd' : ((o :: seen) ++ (ow :: owed).erase o).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨ndSeen, ndOwed.erase o, ?_⟩⟩
      · intro h
        rcases List.mem_append.mp h with h | h
        · exact hos h
        · exact hoe h
      · intro a ha b hb hab
        subst hab
        exact nodup_append_disjoint hnd ha (List.mem_of_mem_erase hb)
    obtain ⟨ihNodup, ihNotSeen, ihOwed, ihRefs⟩ := ih hnd'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [keys_cons]
      exact List.nodup_cons.mpr ⟨fun hok => ihNotSeen o hok (List.mem_cons_self ..), ihNodup⟩
    · intro k hk
      simp only [keys_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact hos
      · exact fun hks => ihNotSeen k hk (List.mem_cons_of_mem _ hks)
    · intro n hn
      simp only [keys_cons]
      by_cases hno : n = o
      · exact hno ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ihOwed n ((List.mem_erase_of_ne hno).mpr hn))
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inl (inNat_iff_mem.mp hr)
      · rcases ihRefs p hp with h1 | h2
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inr (by simp [keys_cons])
          · exact Or.inl h1
        · exact Or.inr (by simp only [keys_cons]; exact List.mem_cons_of_mem _ h2)
  | @fulfillFwd seen ow owed rest o r ho hr _ ih =>
    intro hnd
    obtain ⟨ndSeen, ndOwed, _⟩ := List.nodup_append.mp hnd
    have homem : o ∈ ow :: owed := inNat_iff_mem.mp ho
    have hos : o ∉ seen := fun h => nodup_append_disjoint hnd h homem
    have hoe : o ∉ (ow :: owed).erase o := ndOwed.not_mem_erase
    have hrmem : r ∉ o :: (seen ++ (ow :: owed).erase o) := fresh_not_mem hr
    have hro : r ≠ o := fun h => hrmem (h ▸ List.mem_cons_self ..)
    have hrs : r ∉ seen := fun h => hrmem (List.mem_cons_of_mem _ (List.mem_append_left _ h))
    have hre : r ∉ (ow :: owed).erase o :=
      fun h => hrmem (List.mem_cons_of_mem _ (List.mem_append_right _ h))
    have hnd' : ((o :: seen) ++ (r :: (ow :: owed).erase o)).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr
        ⟨ndSeen, List.nodup_cons.mpr ⟨hre, ndOwed.erase o⟩, ?_⟩⟩
      · intro h
        rcases List.mem_append.mp h with h | h
        · exact hos h
        · rcases List.mem_cons.mp h with h | h
          · exact hro h.symm
          · exact hoe h
      · intro a ha b hb hab
        subst hab
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hrs ha
        · exact nodup_append_disjoint hnd ha (List.mem_of_mem_erase hb)
    obtain ⟨ihNodup, ihNotSeen, ihOwed, ihRefs⟩ := ih hnd'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [keys_cons]
      exact List.nodup_cons.mpr ⟨fun hok => ihNotSeen o hok (List.mem_cons_self ..), ihNodup⟩
    · intro k hk
      simp only [keys_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact hos
      · exact fun hks => ihNotSeen k hk (List.mem_cons_of_mem _ hks)
    · intro n hn
      simp only [keys_cons]
      by_cases hno : n = o
      · exact hno ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _
          (ihOwed n (List.mem_cons_of_mem _ ((List.mem_erase_of_ne hno).mpr hn)))
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine Or.inr ?_
        simp only [keys_cons]
        exact List.mem_cons_of_mem _ (ihOwed r (List.mem_cons_self ..))
      · rcases ihRefs p hp with h1 | h2
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inr (by simp [keys_cons])
          · exact Or.inl h1
        · exact Or.inr (by simp only [keys_cons]; exact List.mem_cons_of_mem _ h2)

/-- Keys are unique: a well-formed chain never repeats a variable name. -/
theorem chain_keys_nodup {l : List Var} (h : Chain [] [] l) : (keys l).Nodup :=
  (chain_inv h (by simp)).1

/-- Every reference points at a key that is present in the list. -/
theorem chain_refs_mem_keys {l : List Var} (h : Chain [] [] l) :
    ∀ p ∈ l, p.2 ∈ keys l := by
  intro p hp
  rcases (chain_inv h (by simp)).2.2.2 p hp with h1 | h2
  · exact absurd h1 (by simp)
  · exact h2

-- Validate the statements against the Specimen-derived generator before trusting
-- the proofs: draw many well-formed chains and check both invariants hold.
def checkInvariants (n : Nat) (size : Nat := 8) : IO Unit := do
  let mut badNodup := 0
  let mut badRefs := 0
  for _ in [:n] do
    let l ← Gen.run (arbitrarySizedST (fun l => Chain [] [] l) size) size
    let ks := keys l
    unless ks.Nodup do badNodup := badNodup + 1
    unless l.all (fun p => ks.contains p.2) do badRefs := badRefs + 1
  IO.println s!"checked {n} chains: {badNodup} with duplicate keys, {badRefs} with a dangling reference"

#eval checkInvariants 2000

/-- Sample some generated lists to see whether the derived generator actually
    produces well-formed forward-referencing lists. -/
def sample (n : Nat) (size : Nat) : IO Unit := do
  let mut empties := 0
  let mut firstSum := 0
  -- Buckets 0..size, plus a final bucket collecting every name > size.
  let mut hist : Array Nat := Array.replicate (size + 2) 0
  for i in [:n] do
    let l ← Gen.run (arbitrarySizedST (fun l => Chain [] [] l) size) size
    if l.isEmpty then empties := empties + 1
    match l.head? with
    | some (nm, _) =>
      firstSum := firstSum + nm
      let b := min nm (size + 1)
      hist := hist.set! b (hist[b]! + 1)
    | none => pure ()
    if i < 12 then IO.println s!"sample {i}: {repr l}"
  let nonEmpty := n - empties
  IO.println s!"empty lists: {empties}/{n}"
  IO.println s!"first var name: avg {firstSum.toFloat / nonEmpty.toFloat} (over {nonEmpty} non-empty)"
  IO.println s!"first-name histogram [name:count]: {(List.range (size + 2)).map (fun k => (k, hist[k]!))}"

#eval sample 200 8
