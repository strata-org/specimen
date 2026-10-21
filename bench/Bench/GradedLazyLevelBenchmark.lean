import Specimen.LazyList
import SpecimenTest.BasaltPort.GradedStlcAdequacy

/-!
# Strict levels vs lazy levels, when a single level is huge

`Basalt/GradedRun.lean` stores each level as a strict `List` behind a `Thunk`:
`LvT α = Array (Thunk (List α))`. That keeps the proofs on `List`, and it made "the first `k`" cheap in
every earlier measurement — but only because those levels were small, so the first `k` terms fit in the
bottom few. Nothing guarantees that. A wide leaf pool (Cedar's identifier pools, a `String` alphabet) puts
a huge number of values in one level, and the product of two such levels is quadratically worse.

This file builds the lazy-within-level carrier `LvL α = Array (Thunk (LazyList α))` alongside `LvT`, runs
STLC on both with a leaf pool of width `W` at level 0, checks they enumerate the same terms in the same
order, and measures the first `k` terms.

`LazyList.append`/`mapLazyList`/`concat` are total defs, so nothing here needs `partial` — the round-robin
bind is never used; a finite level needs plain concatenation only.

The carriers here are local copies rather than Basalt's proved `GradedLazy`/`GradedChunked`
because the measurement wants variants the proved modules do not export: the `pair2` convolution,
and levels over Specimen's own `LazyList` (the type the derived enumerators run on) rather than
Basalt's `LList`. The `check` mode pins the copies to the strict carrier, so a drift fails the run.
Not imported by the test suite: it is a measurement. Compiled by
`lake build Bench`; run with `lake exe bench-lazy-levels CARRIER W K N [CHUNK]` (see `bench/README.md`).
-/

namespace GradedLazyLevel

open Basalt LazyList

/-! ## The lazy-within-level carrier, operation for operation against `LvT` -/

abbrev LvL (α : Type) := Array (Thunk (LazyList α))

def LvL.get (x : LvL α) (n : Nat) : LazyList α :=
  if h : n < x.size then (x[n]'h).get else .lnil

def LvL.build (N : Nat) (f : Nat → Thunk (LazyList α)) : LvL α := ((List.range N).map f).toArray

def LvL.nothing (N : Nat) : LvL α := LvL.build (N + 1) fun _ => Thunk.mk fun _ => .lnil

def LvL.single (N : Nat) (a : α) : LvL α :=
  LvL.build (N + 1) fun n => Thunk.mk fun _ => if n = 0 then LazyList.singleton a else .lnil

def LvL.union (x y : LvL α) : LvL α :=
  LvL.build x.size fun n => Thunk.mk fun _ => (x.get n).append (y.get n)

def LvL.pay (x : LvL α) : LvL α :=
  LvL.build x.size fun n => Thunk.mk fun _ => if n = 0 then .lnil else x.get (n - 1)

def LvL.gmap (g : α → β) (x : LvL α) : LvL β :=
  LvL.build x.size fun n => Thunk.mk fun _ => mapLazyList g (x.get n)

def LvL.pair (x : LvL α) (y : LvL β) : LvL (α × β) :=
  LvL.build x.size fun n => Thunk.mk fun _ =>
    concat (mapLazyList (fun i =>
      concat (mapLazyList (fun a => mapLazyList (a, ·) (y.get (n - i))) (x.get i))) (range (n + 1)))

def LvL.bindC (x : LvL α) (k : α → LvL β) : LvL β :=
  LvL.build x.size fun n => Thunk.mk fun _ =>
    concat (mapLazyList (fun i =>
      concat (mapLazyList (fun a => (k a).get (n - i)) (x.get i))) (range (n + 1)))


/-! ## A cheaper lazy flatMap

`LazyList.concat` re-conses the outer list on every element (`lcons as.get l'`), so a flattened product
pays two allocations per term. `flatMapL` appends each inner list onto a *thunk* of the rest: one cons per
term, and the rest is not built until reached. Both are total — recursion through `Thunk.get` is
structural. -/

def appendT : LazyList α → Thunk (LazyList α) → LazyList α
  | .lnil, ys => ys.get
  | .lcons x xs, ys => .lcons x ⟨fun _ => appendT xs.get ys⟩

/-- Empty inner lists are skipped by a direct (tail) call rather than through a thunk: going through
    `appendT .lnil ys = ys.get` for each one nests a `Thunk.get` per empty list and overflows the stack
    on a long run of them. -/
def flatMapL (f : α → LazyList β) : LazyList α → LazyList β
  | .lnil => .lnil
  | .lcons a t =>
    match f a with
    | .lnil => flatMapL f t.get
    | .lcons b bs => .lcons b ⟨fun _ => appendT bs.get ⟨fun _ => flatMapL f t.get⟩⟩

def LvL.pair2 (x : LvL α) (y : LvL β) : LvL (α × β) :=
  LvL.build x.size fun n => Thunk.mk fun _ =>
    flatMapL (fun i => flatMapL (fun a => mapLazyList (a, ·) (y.get (n - i))) (x.get i)) (range (n + 1))

def LvL.bindC2 (x : LvL α) (k : α → LvL β) : LvL β :=
  LvL.build x.size fun n => Thunk.mk fun _ =>
    flatMapL (fun i => flatMapL (fun a => (k a).get (n - i)) (x.get i)) (range (n + 1))


/-! ## Chunked levels: a lazy list of strict chunks

A level is `LazyList (List α)`: strict chunks of at least `chunkSize` elements (the last may be short),
produced lazily. A level smaller than one chunk is a single strict list — the strict carrier's behaviour —
and a huge level is only ever built one chunk ahead of the reader. Operations work chunk-wise with
ordinary `List` functions, then `coalesce` merges small chunks so the per-element thunk cost of `LvL`
becomes a per-chunk cost. -/

/-- Chunk size, runtime-settable so one binary can sweep it. -/
initialize chunkSizeRef : IO.Ref Nat ← IO.mkRef 256

@[noinline] def chunkSizeImpl (_ : Unit) : Nat := unsafe (unsafeBaseIO chunkSizeRef.get)
def chunkSize : Nat := chunkSizeImpl ()

abbrev Chunks (α : Type) := LazyList (List α)

/-- Merge consecutive chunks until each holds at least `c` elements. Empty chunks vanish. -/
def coalesce (c : Nat) : Chunks α → Chunks α := go [] 0
where
  go (accRev : List (List α)) (len : Nat) : Chunks α → Chunks α
    | .lnil => if len = 0 then .lnil else .lcons (accRev.reverse.flatten) (Thunk.pure .lnil)
    | .lcons xs t =>
      if len + xs.length ≥ c then
        .lcons ((xs :: accRev).reverse.flatten) ⟨fun _ => go [] 0 t.get⟩
      else go (xs :: accRev) (len + xs.length) t.get

def Chunks.ofList (xs : List α) : Chunks α := if xs.isEmpty then .lnil else .lcons xs (Thunk.pure .lnil)

def Chunks.map (g : α → β) (l : Chunks α) : Chunks β := mapLazyList (List.map g) l

/-- Every element of every chunk, fed to `f`, results concatenated — lazily per input element. -/
def Chunks.flatMap (f : α → Chunks β) (l : Chunks α) : Chunks β :=
  flatMapL (fun xs => xs.foldr (fun a acc => appendT (f a) ⟨fun _ => acc⟩) .lnil) l

abbrev LvC (α : Type) := Array (Thunk (Chunks α))

def LvC.get (x : LvC α) (n : Nat) : Chunks α :=
  if h : n < x.size then (x[n]'h).get else .lnil

def LvC.build (N : Nat) (f : Nat → Thunk (Chunks α)) : LvC α := ((List.range N).map f).toArray

def LvC.nothing (N : Nat) : LvC α := LvC.build (N + 1) fun _ => Thunk.mk fun _ => .lnil

def LvC.single (N : Nat) (a : α) : LvC α :=
  LvC.build (N + 1) fun n => Thunk.mk fun _ => if n = 0 then Chunks.ofList [a] else .lnil

def LvC.union (x y : LvC α) : LvC α :=
  LvC.build x.size fun n => Thunk.mk fun _ => coalesce chunkSize (appendT (x.get n) ⟨fun _ => y.get n⟩)

def LvC.pay (x : LvC α) : LvC α :=
  LvC.build x.size fun n => Thunk.mk fun _ => if n = 0 then .lnil else x.get (n - 1)

def LvC.gmap (g : α → β) (x : LvC α) : LvC β :=
  LvC.build x.size fun n => Thunk.mk fun _ => mapLazyList (List.map g) (x.get n)

/-- For each `a` in `x`'s level `i`, one output chunk per chunk of `y`'s level `n - i`, each built with a
    strict `List.map`; then coalesced. -/
def LvC.pair (x : LvC α) (y : LvC β) : LvC (α × β) :=
  LvC.build x.size fun n => Thunk.mk fun _ =>
    coalesce chunkSize <| flatMapL (fun i =>
      Chunks.flatMap (fun a => mapLazyList (List.map (a, ·)) (y.get (n - i))) (x.get i)) (range (n + 1))

def LvC.bindC (x : LvC α) (k : α → LvC β) : LvC β :=
  LvC.build x.size fun n => Thunk.mk fun _ =>
    coalesce chunkSize <| flatMapL (fun i => Chunks.flatMap (fun a => (k a).get (n - i)) (x.get i)) (range (n + 1))

/-! ## STLC on both carriers, with a leaf pool of width `W` at level 0

The pool is flat — every value at level 0, nothing above — which is the shape of Cedar's `identPool`. -/

def natWideT (N W : Nat) : LvT Nat :=
  LvT.build (N + 1) fun n => Thunk.mk fun _ => if n = 0 then List.range W else []

def natWideL (N W : Nat) : LvL Nat :=
  LvL.build (N + 1) fun n => Thunk.mk fun _ => if n = 0 then range W else .lnil

def typeStepL (N : Nat) (rec : LvL type) : LvL type :=
  LvL.union (LvL.single N type.Nat)
    (LvL.pay (LvL.gmap (fun p => type.Fun p.1 p.2) (LvL.pair rec rec)))

def lookupEnumL (N : Nat) : List type → type → LvL Nat
  | [], _ => LvL.nothing N
  | σ :: Γ, τ =>
      LvL.union (if σ = τ then LvL.single N 0 else LvL.nothing N)
        (LvL.pay (LvL.gmap (· + 1) (lookupEnumL N Γ τ)))

def stlcAFStepL (N : Nat) (natE : LvL Nat) (rec : TyIx → LvL term) : TyIx → LvL term
  | (Γ, .Nat) =>
      LvL.union (LvL.gmap term.Var (lookupEnumL N Γ .Nat))
        (LvL.union (LvL.gmap term.Const natE)
          (LvL.pay (LvL.gmap (fun p => term.Add p.1 p.2)
            (LvL.pair (rec (Γ, .Nat)) (rec (Γ, .Nat))))))
  | (Γ, .Fun τ1 τ2) =>
      LvL.union (LvL.gmap term.Var (lookupEnumL N Γ (.Fun τ1 τ2)))
        (LvL.pay (LvL.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))))

def stlcStepL (N : Nat) (natE : LvL Nat) (typeE : LvL type) (rec : TyIx → LvL term) :
    TyIx → LvL term
  | (Γ, τ) =>
      LvL.union (stlcAFStepL N natE rec (Γ, τ))
        (LvL.pay (LvL.bindC typeE (fun τ1 =>
          LvL.gmap (fun p => term.App p.1 p.2)
            (LvL.pair (rec (Γ, .Fun τ1 τ)) (rec (Γ, τ1))))))

def gradedIterL (N : Nat) (step : LvL α → LvL α) : Nat → LvL α
  | 0 => LvL.nothing N
  | l + 1 => step (gradedIterL N step l)

def gradedIterIxL (N : Nat) (step : (ι → LvL α) → ι → LvL α) : Nat → ι → LvL α
  | 0, _ => LvL.nothing N
  | l + 1, i => step (gradedIterIxL N step l) i

def typeStepC (N : Nat) (rec : LvC type) : LvC type :=
  LvC.union (LvC.single N type.Nat)
    (LvC.pay (LvC.gmap (fun p => type.Fun p.1 p.2) (LvC.pair rec rec)))

def lookupEnumC (N : Nat) : List type → type → LvC Nat
  | [], _ => LvC.nothing N
  | σ :: Γ, τ =>
      LvC.union (if σ = τ then LvC.single N 0 else LvC.nothing N)
        (LvC.pay (LvC.gmap (· + 1) (lookupEnumC N Γ τ)))

def stlcAFStepC (N : Nat) (natE : LvC Nat) (rec : TyIx → LvC term) : TyIx → LvC term
  | (Γ, .Nat) =>
      LvC.union (LvC.gmap term.Var (lookupEnumC N Γ .Nat))
        (LvC.union (LvC.gmap term.Const natE)
          (LvC.pay (LvC.gmap (fun p => term.Add p.1 p.2)
            (LvC.pair (rec (Γ, .Nat)) (rec (Γ, .Nat))))))
  | (Γ, .Fun τ1 τ2) =>
      LvC.union (LvC.gmap term.Var (lookupEnumC N Γ (.Fun τ1 τ2)))
        (LvC.pay (LvC.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))))

def stlcStepC (N : Nat) (natE : LvC Nat) (typeE : LvC type) (rec : TyIx → LvC term) :
    TyIx → LvC term
  | (Γ, τ) =>
      LvC.union (stlcAFStepC N natE rec (Γ, τ))
        (LvC.pay (LvC.bindC typeE (fun τ1 =>
          LvC.gmap (fun p => term.App p.1 p.2)
            (LvC.pair (rec (Γ, .Fun τ1 τ)) (rec (Γ, τ1))))))

def gradedIterC (N : Nat) (step : LvC α → LvC α) : Nat → LvC α
  | 0 => LvC.nothing N
  | l + 1 => step (gradedIterC N step l)

def gradedIterIxC (N : Nat) (step : (ι → LvC α) → ι → LvC α) : Nat → ι → LvC α
  | 0, _ => LvC.nothing N
  | l + 1, i => step (gradedIterIxC N step l) i

def typeStepL2 (N : Nat) (rec : LvL type) : LvL type :=
  LvL.union (LvL.single N type.Nat)
    (LvL.pay (LvL.gmap (fun p => type.Fun p.1 p.2) (LvL.pair2 rec rec)))

def lookupEnumL2 (N : Nat) : List type → type → LvL Nat
  | [], _ => LvL.nothing N
  | σ :: Γ, τ =>
      LvL.union (if σ = τ then LvL.single N 0 else LvL.nothing N)
        (LvL.pay (LvL.gmap (· + 1) (lookupEnumL2 N Γ τ)))

def stlcAFStepL2 (N : Nat) (natE : LvL Nat) (rec : TyIx → LvL term) : TyIx → LvL term
  | (Γ, .Nat) =>
      LvL.union (LvL.gmap term.Var (lookupEnumL2 N Γ .Nat))
        (LvL.union (LvL.gmap term.Const natE)
          (LvL.pay (LvL.gmap (fun p => term.Add p.1 p.2)
            (LvL.pair2 (rec (Γ, .Nat)) (rec (Γ, .Nat))))))
  | (Γ, .Fun τ1 τ2) =>
      LvL.union (LvL.gmap term.Var (lookupEnumL2 N Γ (.Fun τ1 τ2)))
        (LvL.pay (LvL.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))))

def stlcStepL2 (N : Nat) (natE : LvL Nat) (typeE : LvL type) (rec : TyIx → LvL term) :
    TyIx → LvL term
  | (Γ, τ) =>
      LvL.union (stlcAFStepL2 N natE rec (Γ, τ))
        (LvL.pay (LvL.bindC2 typeE (fun τ1 =>
          LvL.gmap (fun p => term.App p.1 p.2)
            (LvL.pair2 (rec (Γ, .Fun τ1 τ)) (rec (Γ, τ1))))))

def gradedIterL2 (N : Nat) (step : LvL α → LvL α) : Nat → LvL α
  | 0 => LvL.nothing N
  | l + 1 => step (gradedIterL2 N step l)

def gradedIterIxL2 (N : Nat) (step : (ι → LvL α) → ι → LvL α) : Nat → ι → LvL α
  | 0, _ => LvL.nothing N
  | l + 1, i => step (gradedIterIxL2 N step l) i

/-- Strict levels (`LvT`), width `N + 1`, leaf pool `W`. -/
def enumStrict (N W : Nat) : TyIx → LvT term :=
  gradedIterIxT N (stlcStepT N (natWideT N W) (gradedIterT N (typeStepT N) (N + 1))) (N + 1)

/-- Lazy levels (`LvL`), same everything. -/
def enumLazy (N W : Nat) : TyIx → LvL term :=
  gradedIterIxL N (stlcStepL N (natWideL N W) (gradedIterL N (typeStepL N) (N + 1))) (N + 1)

def natWideC (N W : Nat) : LvC Nat :=
  LvC.build (N + 1) fun n => Thunk.mk fun _ =>
    if n = 0 then coalesce chunkSize (mapLazyList (fun i => [i]) (range W)) else .lnil

def enumChunked (N W : Nat) : TyIx → LvC term :=
  gradedIterIxC N (stlcStepC N (natWideC N W) (gradedIterC N (typeStepC N) (N + 1))) (N + 1)

def enumLazy2 (N W : Nat) : TyIx → LvL term :=
  gradedIterIxL2 N (stlcStepL2 N (natWideL N W) (gradedIterL2 N (typeStepL2 N) (N + 1))) (N + 1)

/-! ## Same terms, same order, level by level -/

#eval (List.range 4).all fun n =>
  (enumStrict 3 5 ([], .Nat)).get n == ((enumLazy 3 5 ([], .Nat)).get n).toList

#eval (List.range 4).all fun n =>
  (enumStrict 3 5 ([], .Fun .Nat .Nat)).get n == ((enumLazy 3 5 ([], .Fun .Nat .Nat)).get n).toList

#eval (List.range 5).all fun n =>
  (enumStrict 4 5 ([], .Nat)).get n == ((enumLazy2 4 5 ([], .Nat)).get n).toList &&
  (enumStrict 4 5 ([], .Fun .Nat .Nat)).get n == ((enumLazy2 4 5 ([], .Fun .Nat .Nat)).get n).toList

/-! ## First `k`: walk levels upward, stop when `k` are in hand -/

def firstKStrict (x : LvT term) (N k : Nat) : Nat := Id.run do
  let mut got := 0
  for n in List.range (N + 1) do
    if got ≥ k then break
    got := got + ((x.get n).take (k - got)).length
  return got

def firstKLazy (x : LvL term) (N k : Nat) : Nat := Id.run do
  let mut got := 0
  for n in List.range (N + 1) do
    if got ≥ k then break
    got := got + ((x.get n).take (k - got)).length
  return got

/-- First `k` from chunked levels: read whole chunks until `k` are in hand. -/
def firstKChunked (x : LvC term) (N k : Nat) : Nat := Id.run do
  let mut got := 0
  for n in List.range (N + 1) do
    if got ≥ k then break
    let mut l := x.get n
    while got < k do
      match l with
      | .lnil => break
      | .lcons xs t => got := got + min xs.length (k - got); l := t.get
  return got

end GradedLazyLevel

open GradedLazyLevel in
def main (args : List String) : IO Unit := do
  let z ← IO.rand 0 0   -- runtime value, so nothing is evaluated at elaboration
  let carrier := args.headD ""
  let W := ((args.drop 1).head?.bind String.toNat?).getD 10 + z
  let k := ((args.drop 2).head?.bind String.toNat?).getD 100
  let N := ((args.drop 3).head?.bind String.toNat?).getD 4
  let t0 ← IO.monoNanosNow
  let n ← match carrier with
    | "strict" => IO.lazyPure fun _ => firstKStrict (enumStrict N W ([], .Nat)) N k
    | "lazy" => IO.lazyPure fun _ => firstKLazy (enumLazy N W ([], .Nat)) N k
    | "check" => do
        -- Chunked levels flatten to the strict ones, same order, at several chunk sizes.
        let mut ok := true
        for c in [1, 2, 7, 256] do
          chunkSizeRef.set c
          for n in List.range 6 do
            for τ in [type.Nat, .Fun .Nat .Nat] do
              ok := ok && (enumStrict 5 (W - z) ([], τ)).get n == ((enumChunked 5 (W - z) ([], τ)).get n).toList.flatten
        pure (if ok then 1 else 0)
    | "chunked" => do
        chunkSizeRef.set (((args.drop 4).head?.bind String.toNat?).getD 256)
        IO.lazyPure fun _ => firstKChunked (enumChunked N W ([], .Nat)) N k
    | "lazy2" => IO.lazyPure fun _ => firstKLazy (enumLazy2 N W ([], .Nat)) N k
    | _ => pure 0
  let t1 ← IO.monoNanosNow
  let hwm := (← IO.FS.readFile "/proc/self/status").splitOn "\n"
    |>.find? (·.startsWith "VmHWM") |>.getD "VmHWM: ?"
  IO.println s!"{carrier} W={W} k={k} N={N}: got {n} in {(t1 - t0) / 1000000}ms  {hwm}"
