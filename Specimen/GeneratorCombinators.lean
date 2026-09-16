import Plausible.Gen
import Plausible.ArbitraryFueled
open Plausible

namespace Gen
/-- Error thrown when a derived generator runs out of fuel (should not happen in practice) -/
def outOfFuelError : GenError := .genError "Specimen: out of fuel (termination limit reached)"

/-- Advance the generator's PRNG to a *decorrelated* state by splitting off a
    fresh independent generator (via `RandomGen.split`) and keeping it.

    Motivation: the `Gen` monad is `StateT StdGen` over `Except`, so when a
    generation attempt throws, the PRNG state is rolled back to exactly where the
    attempt began. A naive retry therefore replays the *identical* failing draw,
    and a single `Rand.next` only nudges the state one step — for a large
    generation that usually reproduces the same high-level (failing) structure,
    so retry loops with a fixed seed can spin without making progress. `randSkip`
    instead jumps to an independent stream, so each retry explores a genuinely
    different input while remaining deterministic in the starting seed. -/
def randSkip : Gen Unit := do
  let _ ← (Plausible.Rand.split : Gen StdGen)
  pure ()

/-- Whether a `GenError` indicates an inconclusive result (ran out of fuel/attempts)
    vs a definitive failure (the constraint is unsatisfiable for this input). -/
def GenError.isInconclusive : GenError → Bool
  | .genError "Specimen: out of fuel (termination limit reached)" => true
  | .genError "out of fuel" => true
  | .genError "Gen.runUntil: Out of attempts" => true
  | _ => false

/-- Result of running a generator with error classification. -/
inductive GenResult (α : Type) where
  | ok : α → GenResult α
  | insufficientFuel : String → GenResult α
  | impossible : String → GenResult α
  deriving Repr

/-- Run a generator, classifying failure into `insufficientFuel` (might succeed with more fuel)
    or `impossible` (the constraint is unsatisfiable for this input). -/
def runChecked (x : Gen α) (size : Nat) : IO (GenResult α) := do
  let result ← (Gen.run x size).toBaseIO
  match result with
  | .ok a => return .ok a
  | .error (.userError msg) =>
    let stripped := (msg.dropPrefix? "Generation failure:").map (·.toString) |>.getD msg
    if GenError.isInconclusive (.genError stripped) then
      return .insufficientFuel stripped
    else
      return .impossible stripped
  | .error e => throw e

end Gen

namespace GeneratorCombinators

/-- `pick default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
    If `xs` is empty, the `default` generator with weight 0 is returned. -/
def pick (default : Gen α) (xs : List (Nat × Gen α)) (n : Nat) : Nat × Gen α :=
  match xs with
  | [] => (0, default)
  | (k, x) :: xs =>
    if n < k then
      (k, x)
    else
      pick default xs (n - k)


/-- `pickDrop xs n` returns a weight & its generator `(k, gen)` from the list `xs`
     such that `n < k`, and also returns the other elements of the list after `(k, gen)` -/
def pickDrop (xs : List (Nat × Gen α)) (n : Nat) : Nat × Gen α × List (Nat × Gen α) :=
  let fail : GenError := .genError "Plausible.Specimen.GeneratorCombinators: failure."
  match xs with
  | [] => (0, throw fail, [])
  | (k, x) :: xs =>
    if n < k then
      (k, x, xs)
    else
      let (k', x', xs') := pickDrop xs (n - k)
      (k', x', (k, x)::xs')

/-- Sums all the weights in an association list containing `Nat`s and `α`s -/
def sumFst (gs : List (Nat × α)) : Nat := List.sum <| List.map Prod.fst gs

/-- Picks one of the generators in `gs` at random, returning the `default` generator
    if `gs` is empty.

    (This is a more ergonomic version of Plausible's `Gen.oneOf` which doesn't
    require the caller to supply a proof that the list index is in bounds.) -/
def oneOfWithDefault (default : Gen α) (gs : List (Gen α)) : Gen α :=
  match gs with
  | [] => default
  | _ => do
    let idx ← Gen.choose Nat 0 (gs.length - 1) (by omega)
    List.getD gs idx.val default

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    If `gs` is empty, the `default` generator is returned.  -/
def frequency (default : Gen α) (gs : List (Nat × Gen α)) : Gen α := do
  let total := sumFst gs
  let n ← Gen.choose Nat 0 (total - 1) (by omega)
  (pick default gs n).snd

/-- `sized f` constructs a generator that depends on its `size` parameter -/
def sized (f : Nat → Gen α) : Gen α :=
  Gen.getSize >>= f

/-- Helper function for `backtrack` which picks one out of `total` generators with some initial amount of `fuel`.
    Tracks whether any branch was inconclusive (fuel exhaustion) vs all branches definitively impossible. -/
def backtrackFuel (fuel : Nat) (total : Nat) (gs : List (Nat × Gen α)) (anyInconclusive : Bool := false) : Gen α :=
  match fuel with
  | .zero =>
    if anyInconclusive then throw Gen.outOfFuelError
    else throw (.genError "Specimen.GeneratorCombinators.backtrack: all branches failed")
  | .succ fuel' => do
    let n ← Gen.choose Nat 0 (total - 1) (by omega)
    let (k, g, gs') := pickDrop gs n
    tryCatch g (fun e =>
      let inconclusive := anyInconclusive || Gen.GenError.isInconclusive e
      backtrackFuel fuel' (total - k) gs' inconclusive)

/-- Tries all generators until one returns a `Some` value or all the generators failed once with `None`.
   The generators are picked at random according to their weights (like `frequency` in Haskell QuickCheck),
   and each generator is run at most once.
   If all branches fail: returns "out of fuel" if any branch was inconclusive, or
   "all branches failed" if all were definitively impossible. -/
def backtrack (gs : List (Nat × Gen α)) : Gen α :=
  backtrackFuel (gs.length) (sumFst gs) gs

/-- Sum the weights in an `Array` of `(weight, _)` pairs. -/
def sumFstArr (gs : Array (Nat × α)) : Nat := gs.foldl (fun s x => s + x.1) 0

/-- Array-based `pickDrop`: scan the active prefix `arr[0:len]` for the weighted index of `n`,
    then remove that entry in O(1) by moving the last active element into its slot (swap-remove).
    Unlike the `List` version, removal allocates nothing — no per-pick list rebuild. -/
def pickDropArr (default : Gen α) (arr : Array (Nat × Gen α)) (len : Nat) (n : Nat) :
    (Nat × Gen α) × Array (Nat × Gen α) × Nat := Id.run do
  let mut acc := 0
  let mut idx := len - 1            -- fallback: last active element (covers n ≥ total rounding)
  for i in [0:len] do
    let k := ((arr[i]?).getD (0, default)).1
    if n < acc + k then
      idx := i
      break
    acc := acc + k
  let chosen := (arr[idx]?).getD (0, default)
  let last   := (arr[len - 1]?).getD (0, default)
  (chosen, arr.set! idx last, len - 1)

/-- Fuel-driven core of `backtrackArr`; recurses structurally on `steps` (= initial branch count). -/
def backtrackArrFuel (steps : Nat) (default : Gen α) (arr : Array (Nat × Gen α))
    (len total : Nat) (anyInconclusive : Bool := false) : Gen α :=
  match steps with
  | .zero =>
    if anyInconclusive then throw Gen.outOfFuelError
    else throw (.genError "Specimen.GeneratorCombinators.backtrackArr: all branches failed")
  | .succ steps' => do
    if len == 0 then
      if anyInconclusive then throw Gen.outOfFuelError
      else throw (.genError "Specimen.GeneratorCombinators.backtrackArr: all branches failed")
    else
      let ⟨n, _⟩ ← Gen.choose Nat 0 (total - 1) (by omega)
      let ((k, g), arr', len') := pickDropArr default arr len n
      tryCatch g (fun e =>
        backtrackArrFuel steps' default arr' len' (total - k)
          (anyInconclusive || Gen.GenError.isInconclusive e))

/-- `Array`-backed `backtrack`: identical semantics to `backtrack` (weighted, without-replacement,
    retry-on-failure), but the working set shrinks via O(1) swap-remove instead of the `List`
    version's O(len) rebuild per pick — so total selection overhead is O(n) allocation-free rather
    than O(n²) with per-pick list churn. Derived generators can emit `backtrackArr #[…]` in place
    of `backtrack […]`. -/
def backtrackArr (gs : Array (Nat × Gen α)) : Gen α :=
  let default : Gen α := throw (.genError "Specimen.GeneratorCombinators.backtrackArr: empty")
  backtrackArrFuel gs.size default gs gs.size (sumFstArr gs)

/-- Delays the evaluation of a generator by taking in a function `f : Unit → Gen α` -/
def thunkGen (f : Unit → Gen α) : Gen α :=
  f ()

/-- `elementsWithDefault` constructs a generator from a list `xs` and a `default` element.
    If `xs` is non-empty, the generator picks an element from `xs` uniformly; otherwise it returns the `default` element.

    Remarks:
    - this is a version of Plausible's `Gen.elements` where the caller doesn't have
      to supply a proof that the list index is in bounds
    - This is a version of QuickChick's `elems_` combinator -/
def elementsWithDefault [Inhabited α] (default : α) (xs : List α) : Gen α :=
  match xs with
  | [] => return default
  | _ => do
    let i ← Subtype.val <$> Gen.choose Nat 0 (xs.length - 1) (by omega)
    return xs[i]!

end GeneratorCombinators
