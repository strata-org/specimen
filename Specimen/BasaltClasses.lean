import Specimen.Enum.Backtrack
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

/-- A generator for `α` whose successes satisfy `P`, taking a fuel; the Basalt counterpart of
`ArbitrarySizedSuchThat`. -/
class BacktrackGenFor (α : Type) (P : α → Prop) where
  gen : ∀ {G : Type → Type} [Gen G] [Specimen.Fail G] [Specimen.FailWith Specimen.Exhaustion G]
    [Specimen.Backtrack G] [Specimen.MonoBacktrack G], Nat → G α

namespace Basalt

/-- An unconstrained generator for `α`.

Under `Basalt` rather than at the root: a root `Arbitrary` is ambiguous with `Plausible.Arbitrary` in
any file that opens `Plausible`. -/
class Arbitrary (α : Type) where
  arbitrary : ∀ {G : Type → Type} [Gen G], G α

/-- An unconstrained generator for `α` whose fuel bounds its recursion depth. -/
class ArbitraryFueled (α : Type) where
  arbitraryFueled : ∀ {G : Type → Type} [Gen G], Nat → G α

/-- An unfueled generator ignores the fuel. Low priority, so an instance that uses it wins. -/
instance (priority := low) [Arbitrary α] : ArbitraryFueled α where
  arbitraryFueled _ := Arbitrary.arbitrary

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

/-! ## Fueled instances for compound types

Each exists because the `Arbitrary` instance for the compound type needs `Arbitrary` components, and a
type that only has `ArbitraryFueled` would otherwise have no generator for, say, its lists. Fuel passes
to each component unchanged: components are siblings, not nested. -/

/-- A list whose length is bounded by the fuel. Nil and cons are weighted `1 : n+1`, so the expected
length grows with the fuel; a fair coin would give mean length 1 at every fuel. -/
protected def List.arbitraryFueledGen [Gen G] [ArbitraryFueled α] : Nat → G (List α)
  | 0 => pure []
  | n + 1 =>
    frequency [(1, fun () => pure []), (n + 1, fun () => do
      let x ← ArbitraryFueled.arbitraryFueled (α := α) (n + 1)
      let xs ← List.arbitraryFueledGen n
      pure (x :: xs))] (by simp; omega)

instance [ArbitraryFueled α] : ArbitraryFueled (List α) where
  arbitraryFueled := List.arbitraryFueledGen

instance [ArbitraryFueled α] [ArbitraryFueled β] : ArbitraryFueled (α × β) where
  arbitraryFueled n := do
    let a ← ArbitraryFueled.arbitraryFueled (α := α) n
    let b ← ArbitraryFueled.arbitraryFueled (α := β) n
    pure (a, b)

instance [ArbitraryFueled α] : ArbitraryFueled (Option α) where
  arbitraryFueled n :=
    oneOf [fun () => pure none, fun () => some <$> ArbitraryFueled.arbitraryFueled (α := α) n]

instance [ArbitraryFueled α] [ArbitraryFueled β] : ArbitraryFueled (α ⊕ β) where
  arbitraryFueled n := oneOf [fun () => Sum.inl <$> ArbitraryFueled.arbitraryFueled (α := α) n,
    fun () => Sum.inr <$> ArbitraryFueled.arbitraryFueled (α := β) n]

end Basalt

/-- An enumerator for `α` whose successes satisfy `P`, taking a size: the Basalt counterpart of
`EnumSizedSuchThat`. The same code as a generator's, over the same classes, written with the
enumerator's schedule; which reading it runs at is the caller's (`Specimen.BasaltBridge` reads it at
`ExceptT Exhaustion Finite`, everything up to the size). -/
class EnumFor (α : Type) (P : α → Prop) where
  enum : ∀ {G : Type → Type} [Gen G] [Specimen.Fail G] [Specimen.FailWith Specimen.Exhaustion G]
    [Specimen.Backtrack G] [Specimen.MonoBacktrack G], Nat → G α

namespace Specimen

open RandomChoice

/-- Every value of `α` up to a size, for a derived enumerator's unconstrained values: finitely many at
each size, each once, at an enumeration. Not `Basalt.ArbitraryFueled`, whose base generators are
geometric (infinite at an enumeration) or weighted (each value once per unit of weight); a datatype gets
one with `deriving instance Specimen.EnumFueled for T`. -/
class EnumFueled (α : Type) where
  enumFueled : ∀ {G : Type → Type} [Gen G], Nat → G α

instance : EnumFueled Nat := ⟨fun n => chooseNat 0 n⟩

instance : EnumFueled Bool := ⟨fun _ => do pure ((← chooseNat 0 1) == 0)⟩

instance : EnumFueled Unit := ⟨fun _ => pure ()⟩

instance : EnumFueled (Fin (n + 1)) := ⟨fun _ => do
  let m ← choose 0 n (Nat.zero_le n)
  pure ⟨m.down.val, Nat.lt_succ_of_le m.down.property.2⟩⟩

/-- `-n` to `n`. -/
instance : EnumFueled Int := ⟨fun n => do pure ((← chooseNat 0 (2 * n) : Nat) - (n : Int))⟩

/-- Printable ASCII, `' '` through `'~'`, at every size. -/
instance : EnumFueled Char := ⟨fun _ => do pure (Char.ofNat (← chooseNat 32 126))⟩

instance [EnumFueled α] : EnumFueled (Option α) where
  enumFueled n := oneOf [fun () => pure none, fun () => some <$> EnumFueled.enumFueled n]

instance [EnumFueled α] [EnumFueled β] : EnumFueled (α × β) where
  enumFueled n := do
    let a ← EnumFueled.enumFueled n
    let b ← EnumFueled.enumFueled n
    pure (a, b)

instance [EnumFueled α] [EnumFueled β] : EnumFueled (α ⊕ β) where
  enumFueled n := oneOf [fun () => Sum.inl <$> EnumFueled.enumFueled n,
    fun () => Sum.inr <$> EnumFueled.enumFueled n]

/-- Lists of length at most the size, each element up to the size. -/
protected def List.enumFueledGen [Gen G] [EnumFueled α] (m : Nat) : Nat → G (List α)
  | 0 => pure []
  | k + 1 => oneOf [fun () => pure [], fun () => do
      let x ← EnumFueled.enumFueled m
      let xs ← List.enumFueledGen m k
      pure (x :: xs)]

instance [EnumFueled α] : EnumFueled (List α) := ⟨fun n => List.enumFueledGen n n⟩

instance : EnumFueled String := ⟨fun n => do pure (String.ofList (← EnumFueled.enumFueled (α := List Char) n))⟩

end Specimen
