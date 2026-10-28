/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Basalt.RandomChoice

/-!
# Generators That Can Fail

`Fail` is the one thing a generator needs to say "no value here", and like `Sized` it is opt-in:
a generator that never fails never asks for it. What failure *is* is up to the interpretation.

* At `OptionT G` it is `none`: a value with a probability, kept apart from divergence. A random or
  `SPMF` run of a failing generator goes through `OptionT`; plain `SPMF` and `IO` have no instance,
  so failure cannot be mistaken for nontermination there.
* At an enumeration it is `∅`: nothing to enumerate, which keeps the enumeration's counts and its
  products cheap (`Basalt/Enum`).

`FailWith ε` is a failure that is not a refutation, `e : ε` saying why (out of fuel, say); it is
data, an `.error` at `ExceptT ε G` (`Basalt/ExceptT.lean`), so a search can retry past it and a
checker need not mistake it for "no". Raising only: there is no catch, which at an enumeration would
turn a label the union keeps into a value the distribution never produces.

Not `Alternative`: its `<|>` is union at an enumeration and left-biased fallback at `OptionT`, so a
generator using it would enumerate values its distribution never produces. Choice between branches
goes through `choose` (`pickFrom`, `branches`), which every interpretation reads the same way.
-/

@[expose] public section

namespace Specimen

/-- A generator monad in which a branch can produce nothing. -/
class Fail (G : Type → Type) where
  /-- No value here. -/
  fail : G α

/-- A generator monad in which a branch can fail without refuting: out of fuel, say, so a search
should look elsewhere and not conclude there is nothing. `e` says why. -/
class FailWith (ε : Type) (G : Type → Type) where
  failWith : ε → G α

instance [Monad G] : Fail (OptionT G) := ⟨failure⟩

open RandomChoice in
/-- One of the values of a list, uniformly; `fail` for the empty list. At an enumeration, all of
them, in order. -/
def pickFrom [Monad G] [RandomChoice G] [Fail G] : List β → G β
  | [] => Fail.fail
  | x :: xs => do
    let i ← choose 0 xs.length (by omega)
    pure ((x :: xs)[i.down.val]'(by have := i.down.property; simp; omega))

/-- One of the branches, uniformly; `fail` for none. At an enumeration, their disjoint union. -/
def branches [Monad G] [RandomChoice G] [Fail G] (bs : List (Unit → G α)) : G α := do
  (← pickFrom bs) ()

end Specimen
