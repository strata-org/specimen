import Specimen.Enumerators
import Specimen.LazyList
import Specimen.GeneratorCombinators
import Plausible.Gen
import Plausible.ArbitraryFueled

open LazyList Plausible

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/master/src/Enumerators.v

namespace EnumeratorCombinators

/-- `pickDrop xs n` and returns the `n`-th enumerator from the list `xs`,
    and returns the tail of the list from the `n+1`-th element onwards
    - Note: this is a variant of `Gen.pickDrop` where the input list does not contain weights
      (enumerators don't have weights attached to them, unlike generators) -/
def pickDrop (xs : List (ExceptT GenError Enumerator α)) (n : Nat) : ExceptT GenError Enumerator α × List (ExceptT GenError Enumerator α) :=
  match xs with
  | [] => (throw <| .genError "EnumeratorCombinators.pickDrop: Empty list", [])
  | x :: xs =>
    match n with
    | .zero => (x, xs)
    | .succ n' =>
      let (x', xs') := pickDrop xs n'
      (x', x::xs')

/-- Picks one out of `total` enumerators, retrying with the rest on failure until `fuel` runs out.

    Unused outside its own recursive call: `enumerate`, and so all derived enumerator code, goes
    through `enumerateAll` instead, which concatenates every branch rather than picking one. Kept as
    the enumerator counterpart of `GeneratorCombinators.backtrack`. -/
def enumerateFuel (fuel : Nat) (total : Nat) (es : List (ExceptT GenError Enumerator α)) : ExceptT GenError Enumerator α :=
  match fuel with
  | .zero => throw (.genError "out of fuel")
  | .succ fuel' => do
    let n ← monadLift $ enumNatRange 0 (total - 1)
    let (e, es') := pickDrop es n
    -- Try to enumerate a value using `e`, if it fails, backtrack with `fuel'`
    -- and pick one out of the `total - k` remaining enumerators
    tryCatch e (fun _ => enumerateFuel fuel' (total - 1) es')

/-- Combines all enumerators into a single lazy list, **preserving the order of `es`**.

    The fold has to be a `foldr`: a `foldl` builds
    `append (e₃ …) (append (e₂ …) (append (e₁ …) lnil))`, putting the last branch first. Derived code
    emits a relation's constructors in declaration order, so the cheap non-recursive base cases come
    first and the failure-prone recursive ones last. Reversing that buries every success behind the
    failures, and a consumer taking a prefix sees `.error` entries almost exclusively. -/
def enumerateAll (es : List (ExceptT GenError Enumerator α)) (fuel : Nat) : LazyList (Except GenError α) :=
  es.foldr (fun e acc => LazyList.append (e fuel) acc) .lnil

/-- Drops every failure except the first *inconclusive* one, which moves to the end. Values keep their
    order.

    Why this is safe: the only consumer that reads failures is the checker's `lazyListBacktrackOpt`, which
    skips a definitive failure outright and otherwise asks only whether *any* inconclusive one appeared —
    and a `true` anywhere wins regardless. So one inconclusive entry, anywhere, carries all the information
    the list had. Enumerator consumers discard failures entirely.

    Why it matters: every failed `match` in an emitted branch is an `.error` entry, and an enumerator's bind
    carries each one through, so failures multiply with the values around them. Measured on the derived STLC
    enumerator (`SpecimenTest/GradedVsDerivedConcatAblation.lean`, goal `Fun Nat Nat`, budget 11): carrying
    them costs ~6×. Squashing at every `enumerate` bounds them to one per call.

    A run of failures is skipped by a direct call, not through a thunk, so a long run cannot nest forces. -/
def squashErrors (l : LazyList (Except GenError α)) : LazyList (Except GenError α) := go none l
where
  go (pending : Option GenError) : LazyList (Except GenError α) → LazyList (Except GenError α)
    | .lnil => match pending with
      | some e => .lcons (.error e) (Thunk.pure .lnil)
      | none => .lnil
    | .lcons (.ok a) t => .lcons (.ok a) ⟨fun _ => go pending t.get⟩
    | .lcons (.error e) t =>
      go (if pending.isNone && Gen.GenError.isInconclusive e then some e else pending) t.get

/-- Concatenates *every* enumerator in `es`, in order, into a single lazy enumeration — each branch
    contributes all of its values. Failures do not cause a retry; definitive ones are dropped and at most
    one inconclusive one is kept (`squashErrors`).

    Note this is emphatically **not** "pick one branch, retrying on failure": that is
    `enumerateFuel`, which nothing currently calls. Nor are branches weighted — unlike the
    generator's `GeneratorCombinators.backtrack`, every branch is enumerated exactly once, so
    constructor weights have no effect below the generator. -/
def enumerate (es : List (ExceptT GenError Enumerator α)) : ExceptT GenError Enumerator α :=
  fun fuel => squashErrors (enumerateAll es fuel)

/-- Applies the checker `f` to a `LazyList l` of values, returning the resultant `Except ε Bool`
    (the parameter `anyNone` is used to indicate whether any of the elements examined previously have been `none`) -/
def lazyListBacktrack (l : LazyList α) (f : α → Except GenError Bool) (anyNone : Bool) : Except GenError Bool :=
  let err := GenError.genError "EnumeratorCombinators.lazyListBackTrack: failure"
  match l with
  | .lnil => if anyNone then throw err else .ok false
  | .lcons x xs =>
    match f x with
    | .ok true => .ok true
    | .ok false => lazyListBacktrack xs.get f anyNone
    | .error _ => lazyListBacktrack xs.get f true

/-- An enumerator error is "inconclusive" (ran out of fuel / couldn't decide) vs
    "disproved" (this constructor path definitively doesn't apply).

    Delegates to `Gen.GenError.isInconclusive`, the one classifier all three producer sorts use, so
    that an error means the same thing on every path. A sort-local copy would be free to disagree
    about an error such as `"Gen.runUntil: Out of attempts"`, and a path that reads it as definite
    turns something never determined into an `ok false`: a refutation of a true proposition. -/
def isInconclusiveError : GenError → Bool := Gen.GenError.isInconclusive

/-- Variant of `lazyListBacktrack` where the input `LazyList` contains `Except ε α` values instead of `α`.

    Error handling distinguishes two failure modes:
    - **Disproved** (enumerator `.error` that is NOT inconclusive): this constructor path
      definitively doesn't apply. Treated like `.ok false` — skip to next, don't poison.
    - **Inconclusive** (enumerator `.error` from fuel exhaustion, or continuation `.error`):
      couldn't determine truth. Sets `anyNone := true` so the final result is `error`. -/
def lazyListBacktrackOpt (l : LazyList (Except GenError α)) (f : α → Except ε Bool) (anyNone : Bool) : Except GenError Bool :=
  let err := GenError.genError "EnumeratorCombinators.lazyListBackTrackOpt: failure"
  match l with
  | .lnil => if anyNone then throw err else .ok false
  | .lcons mx xs =>
    match mx with
    | .ok x =>
      match f x with
      | .ok true => .ok true
      | .ok false => lazyListBacktrackOpt xs.get f anyNone
      | .error _ => lazyListBacktrackOpt xs.get f true
    | .error e =>
      let poisoned := if isInconclusiveError e then true else anyNone
      lazyListBacktrackOpt xs.get f poisoned

/-- Iterates through all the results of the enumerator `e`, applies the checker `f` to them,
    and returns the resultant `Except GenError Bool`. -/
def enumerating (e : Enumerator α) (f : α → Except GenError Bool) (size : Nat) : Except GenError Bool :=
  lazyListBacktrack (e size) f false

/-- Variant of `enumerating`, except the input enumerator `e` may fail and has type `ExceptT GenError Enumerator α`
    - This corresponds to `bind_EC` in the Computing Correctly paper (section 4) -/
def enumeratingOpt (e : ExceptT GenError Enumerator α) (f : α → Except GenError Bool) (size : Nat) : Except GenError Bool :=
  lazyListBacktrackOpt (e size) f false

end EnumeratorCombinators
