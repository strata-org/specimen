/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public import Specimen.Enum.Finite

/-!
# Exact Distributions: `WFinite`

`Finite` with the probability of the path that reached each entry: a `choose` gives each value of its
range `1 / (hi - lo + 1)`, and `bind` multiplies along the path. A generator run here is its exact
distribution, wherever its choices form a finite tree. Two paths to one value are two entries; summing
them is the value's probability.

Under `WithSize`, a bucket is whatever the generator reads with `sized`, and a generator that biases
its choices by size is, bucket by bucket, the distribution it draws from at that size.
-/

@[expose] public section

open Lean.Order

namespace Specimen


/-- A `Finite` set whose entries carry the probability of the path that reached them. -/
def WFinite (α : Type) : Type := Finite (α × Rat)

namespace WFinite

def bind (x : WFinite α) (f : α → WFinite β) : WFinite β :=
  Finite.bind x fun p => Finite.map (fun q => (q.1, p.2 * q.2)) (f p.1)

instance : Monad WFinite where
  pure a := Finite.singleton (a, 1)
  bind := WFinite.bind

instance : Inhabited (WFinite α) := ⟨.undef⟩

instance instCCPO : CCPO (WFinite α) := inferInstanceAs (CCPO (Finite (α × Rat)))

instance : MonoBind WFinite where
  bind_mono_left h := MonoBind.bind_mono_left (m := Finite) h
  bind_mono_right h := MonoBind.bind_mono_right (m := Finite) fun _ => Finite.map_mono (h _)

/-- Every value of the range, each with probability `1 / (hi - lo + 1)`. -/
instance : RandomChoice WFinite where
  choose lo hi _ :=
    Finite.mk (hi - lo + 1) fun i => (.up ⟨lo + i.val, by have := i.isLt; omega⟩, 1 / (hi - lo + 1))

instance : Fail WFinite := ⟨Finite.empty⟩

/-- The entries, if defined. -/
def entries? (x : WFinite α) : Option (List (α × Rat)) := Finite.toList? x

/-- Each value's probability: the weights of its entries summed, in order of first appearance. -/
def dist [BEq α] (es : List (α × Rat)) : List (α × Rat) :=
  es.foldl (fun acc (a, w) =>
    if acc.any (·.1 == a) then acc.map fun (b, v) => if b == a then (b, v + w) else (b, v)
    else acc ++ [(a, w)]) []

/-- The distribution of `m` over the entries, in increasing order of `m`. -/
def pushforward (m : α → Nat) (es : List (α × Rat)) : List (Nat × Rat) :=
  let top := es.foldl (fun t (a, _) => max t (m a)) 0
  (List.range (top + 1)).filterMap fun k =>
    let w := (es.filter (m ·.1 == k)).foldl (fun s (_, w) => s + w) 0
    if w == 0 then none else some (k, w)

end WFinite

end Specimen
