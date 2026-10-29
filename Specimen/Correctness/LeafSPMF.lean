import Specimen.Correctness.GenInterpSPMF
import Basalt.Walk.Entry
import Basalt.Walk.Complete

/-!
# Unconstrained draws at `SGen`

A derived generator draws an unconstrained value at its own monad: `Basalt.ArbitraryFueled` is
polymorphic in `G`, so at `SGen` it runs there rather than being lifted from `SPMF`. `ReachesAll`
carries a draw's completeness at `SPMF` over to `SGen`: it is a `GenRel`, so `walk fixpoint` proves it
of any generator that cannot fail, and the base instances' completeness follows.
-/

open Lean.Order RandomChoice

namespace Specimen.Correctness

variable {α β : Type}

/-- Everything `x` can produce at `SPMF`, `y` succeeds with at `SGen`. -/
def ReachesAll {α : Type} (x : SPMF α) (y : SGen α) : Prop := ∀ a ∈ x.support, Produces y a

namespace ReachesAll

theorem pure (a : α) : ReachesAll (Pure.pure a) (Pure.pure a : SGen α) := fun b hb => by
  rw [SPMF.mem_support_pure_iff] at hb
  exact produces_pure_iff.mpr hb

theorem bind {x : SPMF α} {y : SGen α} {k : α → SPMF β} {k' : α → SGen β}
    (hk : ∀ a, ReachesAll (k a) (k' a)) (hx : ReachesAll x y) :
    ReachesAll (x >>= k) (y >>= k') := fun b hb => by
  obtain ⟨a, ha, hb⟩ := SPMF.mem_support_bind_iff.mp hb
  exact produces_bind_of (hx a ha) (hk a b hb)

theorem map {x : SPMF α} {y : SGen α} (f : α → β) (hx : ReachesAll x y) :
    ReachesAll (f <$> x) (f <$> y) := by
  rw [← LawfulMonad.bind_pure_comp, Specimen.EnumeratesWith.map_eq_bind]
  exact bind (fun a => pure (f a)) hx

theorem default (y : SGen α) : ReachesAll Inhabited.default y := fun a ha => by
  simp [SPMF.mem_support_iff, SPMF.default_apply] at ha

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    ReachesAll (RandomChoice.choose lo hi h) (RandomChoice.choose lo hi h : SGen _) := fun a ha => by
  show some (.ok a) ∈
    (ExceptT.lift (OptionT.lift (RandomChoice.choose lo hi h : SPMF _)) : SGen _).run.run.support
  simp only [ExceptT.lift, ExceptT.run_mk, OptionT.lift, OptionT.run_map, OptionT.run_mk]
  rw [SPMF.mem_support_map_iff]
  exact ⟨some a, SPMF.mem_support_bind_iff.mpr ⟨a, ha, SPMF.mem_support_pure_iff.mpr rfl⟩, rfl⟩

theorem admissible (y : SGen α) : Lean.Order.admissible fun x : SPMF α => ReachesAll x y :=
  admissible_iff.2 fun _ hc ih a ha =>
    let ⟨x, hxc, hxa⟩ := (SPMF.mem_support_csup_iff hc).mp ha
    ih x hxc a hxa

end ReachesAll

@[walk_rel]
theorem genRel_reachesAll : GenRel SPMF (ExceptT Exhaustion (OptionT SPMF)) @ReachesAll where
  pure := ReachesAll.pure
  bind := ReachesAll.bind
  map := ReachesAll.map
  default := ReachesAll.default
  choose := ReachesAll.choose
  admissible := ReachesAll.admissible

/-! ## The base instances -/

theorem nat_arbitraryGen_sound_complete :
    IsSoundAndComplete (Basalt.Nat.arbitraryGen (G := SPMF)) ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro n
  induction n with
  | zero => intro _; rw [Basalt.Nat.arbitraryGen, SPMF.mem_support_iff_may]; walk
  | succ n ih =>
    intro _
    rw [Basalt.Nat.arbitraryGen, SPMF.mem_support_iff_may]; walk
    exact ⟨n, ih trivial, rfl⟩

theorem nat_arbitraryGen_reachesAll :
    ReachesAll (Basalt.Nat.arbitraryGen (G := SPMF)) (Basalt.Nat.arbitraryGen (G := SGen)) := by
  walk fixpoint

/-- An unconstrained `Nat` draw produces every number, at any fuel. -/
theorem produces_arbitraryFueled_nat (fuel n : Nat) :
    Produces (Basalt.ArbitraryFueled.arbitraryFueled (α := Nat) (G := SGen) fuel) n :=
  nat_arbitraryGen_reachesAll n (nat_arbitraryGen_sound_complete.complete n trivial)

end Specimen.Correctness
