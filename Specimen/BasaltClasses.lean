import Specimen.Enum.Pick
import Basalt.Combinators

/-!
# The classes Basalt-derived generators are found by

A derived generator under `specimen.emitBasalt` is polymorphic in its generator monad `G`. It asks of
`G` only what derived code does: Basalt's `Gen`, and from `Specimen.Enum` `Fail` for a refutation,
`FailWith Exhaustion` for a failure that is not one, and `Backtrack` (with `MonoBacktrack`) for the
choice among rules. These classes find such a generator by what it produces, and give the
unconstrained values it draws.

Basalt keeps generation generic and has no lookup classes of its own, so they live here.
-/

/-- Why a derived generator gave up without refuting. A refutation is `Fail.fail`; these are the
`FailWith` labels, which a search retries past and a checker reads as inconclusive. -/
inductive Specimen.Exhaustion where
  /-- The fuel bounding the recursion ran out. -/
  | fuel
  /-- At size `0`, a rule that needs to recurse was cut off after its conclusion matched. -/
  | truncated
  /-- A premise's checker could not decide. -/
  | inconclusive
  deriving Repr, DecidableEq, Inhabited

namespace Specimen.Exhaustion

/-- Running out of fuel outranks truncation, which outranks an undecided premise. -/
def rank : Exhaustion → Nat
  | .inconclusive => 0
  | .truncated => 1
  | .fuel => 2

/-- The labels a search saw, joined; the sampler's `backtrack` needs one so the order it tried its
branches in does not show. -/
instance : Max Exhaustion := ⟨fun a b => if a.rank < b.rank then b else a⟩

end Specimen.Exhaustion

namespace Specimen

/-! ## The failures derived code emits -/

variable {G : Type → Type} {α : Type}

/-- This rule does not apply. -/
abbrev refute [Fail G] : G α := Fail.fail

/-- The fuel bounding the recursion ran out. -/
abbrev outOfFuel [FailWith Exhaustion G] : G α := FailWith.failWith Exhaustion.fuel

/-- At size `0`, a rule that needs to recurse was cut off. -/
abbrev truncated [FailWith Exhaustion G] : G α := FailWith.failWith Exhaustion.truncated

/-- A premise's checker could not decide. -/
abbrev inconclusive [FailWith Exhaustion G] : G α := FailWith.failWith Exhaustion.inconclusive

end Specimen

/-- A generator for `α` whose successes satisfy `P`; the Basalt counterpart of
`ArbitrarySizedSuchThat`. It takes two sizes: the search's, which bounds the structure and is split
among recursive calls, and the leaf size, which bounds every unconstrained value and is passed
unchanged, as Plausible's ambient size is. -/
class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G] [Specimen.Fail G] [Specimen.FailWith Specimen.Exhaustion G]
    [Specimen.Backtrack G] [Specimen.MonoBacktrack G] [Specimen.Pick G], (size leafSize : Nat) → G α

namespace Basalt

/-- An unconstrained generator for `α`.

Under `Basalt` rather than at the root: a root `Arbitrary` is ambiguous with `Plausible.Arbitrary` in
any file that opens `Plausible`. -/
class Arbitrary (α : Type) where
  arbitrary : ∀ {G : Type → Type} [Gen G], G α

/-- An unconstrained generator for `α` bounded by a size: finitely many values at each size, so the
same term is a generator when sampled and every value up to the size, each once, at an enumeration.
Derived generators and enumerators both draw unconstrained values through it. `Pick` is there for a
weighted instance: at an enumeration it lists each branch once, where `frequency` repeats it per unit
of weight. -/
class ArbitrarySized (α : Type) where
  arbitrarySized : ∀ {G : Type → Type} [Gen G] [Specimen.Pick G], Nat → G α

/-- An unfueled generator ignores the fuel. Low priority, so an instance that uses it wins. -/
instance (priority := low) [Arbitrary α] : ArbitrarySized α where
  arbitrarySized _ := Arbitrary.arbitrary

open RandomChoice

/-! ## Base instances -/

/-- A geometric `Nat`: stop with probability `1/2` at each step. -/
protected def Nat.arbitraryGen [Gen G] : G Nat :=
  oneOf [fun () => pure 0, fun () => do let n ← Nat.arbitraryGen; pure (n + 1)]
partial_fixpoint

instance : Arbitrary Nat where
  arbitrary := Nat.arbitraryGen

instance : Arbitrary Bool where
  arbitrary := do pure ((← chooseNat 0 1) == 0)

instance : Arbitrary Unit where
  arbitrary := pure ()

instance : Arbitrary (Fin (n + 1)) where
  arbitrary := do
    let m ← choose 0 n (Nat.zero_le n)
    pure ⟨m.down.val, Nat.lt_succ_of_le m.down.property.2⟩

instance [Arbitrary α] : Arbitrary (Option α) where
  arbitrary := oneOf [fun () => pure none, fun () => some <$> Arbitrary.arbitrary]

instance [Arbitrary α] [Arbitrary β] : Arbitrary (α × β) where
  arbitrary := do
    let a ← Arbitrary.arbitrary
    let b ← Arbitrary.arbitrary
    pure (a, b)

instance [Arbitrary α] [Arbitrary β] : Arbitrary (α ⊕ β) where
  arbitrary := oneOf [fun () => Sum.inl <$> Arbitrary.arbitrary,
    fun () => Sum.inr <$> Arbitrary.arbitrary]

instance : Arbitrary Int where
  arbitrary := oneOf [fun () => Int.ofNat <$> Arbitrary.arbitrary,
    fun () => Int.negSucc <$> Arbitrary.arbitrary]

/-- Printable ASCII, `' '` through `'~'`: the full `Char` range is mostly unassigned code points and
surrogates, which make useless test data. -/
instance : Arbitrary Char where
  arbitrary := do pure (Char.ofNat (← chooseNat 32 126))

/-- A geometric-length list. -/
protected def List.arbitraryGen [Gen G] [Arbitrary α] : G (List α) :=
  oneOf [fun () => pure [], fun () => do
    let x ← Arbitrary.arbitrary
    let xs ← List.arbitraryGen
    pure (x :: xs)]
partial_fixpoint

instance [Arbitrary α] : Arbitrary (List α) where
  arbitrary := List.arbitraryGen

instance : Arbitrary String where
  arbitrary := do pure (String.ofList (← Arbitrary.arbitrary (α := List Char)))

/-! ## Sized instances

Bounded by the size, as Plausible's are by its ambient size: `Nat` is uniform on `0..n`, a list's length
uniform on `0..n` with each element at size `n`. A component of a compound type gets the size
unchanged: components are siblings, not nested. -/

instance : ArbitrarySized Nat := ⟨fun n => chooseNat 0 n⟩

instance : ArbitrarySized Bool := ⟨fun _ => do pure ((← chooseNat 0 1) == 0)⟩

instance : ArbitrarySized Unit := ⟨fun _ => pure ()⟩

instance : ArbitrarySized (Fin (n + 1)) := ⟨fun _ => do
  let m ← choose 0 n (Nat.zero_le n)
  pure ⟨m.down.val, Nat.lt_succ_of_le m.down.property.2⟩⟩

/-- `-n` to `n`. -/
instance : ArbitrarySized Int := ⟨fun n => do pure ((← chooseNat 0 (2 * n) : Nat) - (n : Int))⟩

/-- Printable ASCII, `' '` through `'~'`, at every size. -/
instance : ArbitrarySized Char := ⟨fun _ => do pure (Char.ofNat (← chooseNat 32 126))⟩

instance [ArbitrarySized α] : ArbitrarySized (Option α) where
  arbitrarySized n := oneOf [fun () => pure none, fun () => some <$> ArbitrarySized.arbitrarySized n]

instance [ArbitrarySized α] [ArbitrarySized β] : ArbitrarySized (α × β) where
  arbitrarySized n := do
    let a ← ArbitrarySized.arbitrarySized n
    let b ← ArbitrarySized.arbitrarySized n
    pure (a, b)

instance [ArbitrarySized α] [ArbitrarySized β] : ArbitrarySized (α ⊕ β) where
  arbitrarySized n := oneOf [fun () => Sum.inl <$> ArbitrarySized.arbitrarySized n,
    fun () => Sum.inr <$> ArbitrarySized.arbitrarySized n]

instance [ArbitrarySized α] : ArbitrarySized (List α) where
  arbitrarySized n := do
    let k ← chooseNat 0 n
    vectorOf k (ArbitrarySized.arbitrarySized n)

instance : ArbitrarySized String where
  arbitrarySized n := do pure (String.ofList (← ArbitrarySized.arbitrarySized (α := List Char) n))

end Basalt

/-- An enumerator for `α` whose successes satisfy `P`, taking the two sizes `BacktrackGenFor` does:
the Basalt counterpart of `EnumSizedSuchThat`. The same code as a generator's, over the same classes, written with the
enumerator's schedule; which reading it runs at is the caller's (`Specimen.BasaltBridge` reads it at
`ExceptT Exhaustion Finite`, everything up to the size). -/
class EnumFor (α : Type) (P : α → Prop) where
  enum : ∀ {G : Type → Type} [Gen G] [Specimen.Fail G] [Specimen.FailWith Specimen.Exhaustion G]
    [Specimen.Backtrack G] [Specimen.MonoBacktrack G] [Specimen.Pick G], (size leafSize : Nat) → G α

