/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Fail
public import Basalt.Gen

/-!
# Failures That Say Why: `ExceptT ε G`

A labelled failure as data over any generator monad `G`: `ExceptT ε G` is a generator monad, `failWith`
is an `.error`, and `G`'s own `Fail.fail` is lifted unchanged, so a refutation stays what `G` makes it.
-/

@[expose] public section

namespace Specimen

open Lean.Order RandomChoice

instance instRandomChoiceExceptT {ε : Type} {G : Type → Type} [Monad G] [RandomChoice G] :
    RandomChoice (ExceptT ε G) where
  choose lo hi h := ExceptT.lift (RandomChoice.choose lo hi h)

/-- `default` is `G`'s, the bottom of its order, not core's `throw default`. -/
instance instGenExceptT {ε : Type} {G : Type → Type} [Gen G] : Gen (ExceptT ε G) where
  instInhabited := fun _ => ⟨ExceptT.mk default⟩
  instMonad := inferInstance
  instRandomChoice := instRandomChoiceExceptT
  instCCPO := fun _ => inferInstance
  instMonoBind := inferInstanceAs (MonoBind (ExceptT ε G))

/-- `G`'s refutation, unchanged. -/
instance instFailExceptT {ε : Type} {G : Type → Type} [Monad G] [Fail G] : Fail (ExceptT ε G) :=
  ⟨ExceptT.lift Fail.fail⟩

instance instFailWithExceptT {ε : Type} {G : Type → Type} [Monad G] : FailWith ε (ExceptT ε G) :=
  ⟨fun e => ExceptT.mk (pure (.error e))⟩

end Specimen
