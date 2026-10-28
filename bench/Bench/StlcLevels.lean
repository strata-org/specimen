import SpecimenTest.CommonDefinitions.STLCDefinitions
import Std.Data.HashSet

/-!
# The STLC levels both derived-vs-levels benchmarks compare against

`lvA Γ τ n` is the exact level — the well-typed terms whose budget is exactly `n` under the derived
enumerator's own rule (`Add`/`App` at the halved budget through the `max` convolution, `Abs` at
`n - 1`, `τ1` for `App` from the two-type alphabet) — over the restricted leaf alphabets the
benchmark files install as instances. `sameSet` is the comparison both files `#guard` with: same
set, no duplicates on either side. Pure definitions only; the high-priority instances that make the
ablation rungs comparable stay in the files that need them.
-/

namespace StlcLevels

/-- Restricted leaf alphabets, matching the instances the benchmark files install. -/
def natLeaves : List Nat := [0]
def tyLeaves : List type := [.Nat, .Fun .Nat .Nat]

def varsAt (Γ : List type) (τ : type) : List term :=
  (Γ.zipIdx.filter fun (σ, _) => σ = τ).map fun (_, x) => .Var x


/-- `max` convolution at `m`: `x(m) × y(≤ m) ∪ x(< m) × y(m)`, from exact-level functions. -/
def maxPair (x y : Nat → List α) (m : Nat) : List (α × α) :=
  let yle := (List.range (m + 1)).flatMap y
  let xlt := (List.range m).flatMap x
  ((x m).flatMap fun a => yle.map (a, ·)) ++ (xlt.flatMap fun a => (y m).map (a, ·))

mutual
/-- Level exactly `n`. -/
partial def lvA (Γ : List type) (τ : type) (n : Nat) : List term :=
  if n = 0 then
    (match τ with | .Nat => natLeaves.map .Const | _ => []) ++ varsAt Γ τ
  else
    let abs := match τ with
      | .Fun τ1 τ2 => (lvA (τ1 :: Γ) τ2 (n - 1)).map (.Abs τ1)
      | .Nat => []
    if n % 2 = 1 then
      let m := (n - 1) / 2
      let add := match τ with
        | .Nat => maxPair (lvA Γ .Nat) (lvA Γ .Nat) m |>.map fun (a, b) => .Add a b
        | _ => []
      -- `τ1` from `Enum type`, then `e1 : τ1 → τ` and `e2 : τ1`, both at `m`.
      let app := tyLeaves.flatMap fun τ1 =>
        maxPair (lvA Γ (.Fun τ1 τ)) (lvA Γ τ1) m |>.map fun (e1, e2) => .App e1 e2
      abs ++ add ++ app
    else abs

partial def lvAle (Γ : List type) (τ : type) (m : Nat) : List term :=
  (List.range (m + 1)).flatMap (lvA Γ τ)
end

def levelsUpTo (Γ : List type) (τ : type) (s : Nat) : List term :=
  (List.range (s + 1)).flatMap (lvA Γ τ)

def keys (l : List term) : Std.HashSet String :=
  l.foldl (fun s t => s.insert (toString (repr t))) {}

/-- Same set, and no duplicates on either side. -/
def sameSet (a b : List term) : Bool :=
  let ka := keys a
  let kb := keys b
  ka.size == a.length && kb.size == b.length && ka.size == kb.size && ka.toList.all kb.contains

end StlcLevels
