import Specimen

/-!
# Regression: recursive indices written with arithmetic

A recursive constructor's index can be written `.succ n` or `n + 1`. These are the same proposition,
and they used not to derive the same things: only the constructor spelling worked.

`n + 1` is `HAdd.hAdd … n 1`, whose head is a **definition**, so `collectUnmatchableSubterms` classed
it as unmatchable and `linearizeAndFlatten` replaced it with a fresh variable plus an equality
hypothesis `v = n + 1`. Discharging that means inverting addition, which the scheduler can only do by
*enumerating* — so `derive_checker` failed with an unrelated-looking
`failed to synthesize EnumSizedSuchThat`. `Nat.succ n` is a constructor application and was matched as
a pattern instead.

The fix normalises `n + k` to a `Nat.succ` chain *before* linearization (`Utils.normalizeNatSuccIndices`);
normalising later is too late, since the subterm has already been replaced.

This mattered in practice, not just in principle: `lookup` in `STLCDefinitions.lean` is written
`.succ n` and always derived a checker, while an evenness relation written `n + 2` could not derive one
and had to have its checker written out by hand.
-/

open Plausible

/-- `+ 1`: the spelling that used to fail. -/
inductive ArithIdxSucc : Nat → Prop where
  | z : ArithIdxSucc 0
  | s : ∀ n, ArithIdxSucc n → ArithIdxSucc (n + 1)

/-- `+ 2`, so the normalisation has to iterate rather than peel one constructor. -/
inductive ArithIdxTwo : Nat → Prop where
  | z : ArithIdxTwo 0
  | s : ∀ n, ArithIdxTwo n → ArithIdxTwo (n + 2)

/-- The constructor spelling, which always worked — kept so a regression in either direction shows. -/
inductive ArithIdxCtor : Nat → Prop where
  | z : ArithIdxCtor 0
  | s : ∀ n, ArithIdxCtor n → ArithIdxCtor (Nat.succ n)

/-- The exact shape of `Ev` in `Specimen/Correctness/EvSlice.lean`: `n + 2` *and* an implicit binder,
    since binder info is a separate axis from the index spelling. This is the case that motivated the
    fix — that file's checker had to be hand-written. -/
inductive ArithIdxImplicit : Nat → Prop
  | z : ArithIdxImplicit 0
  | ss {n : Nat} : ArithIdxImplicit n → ArithIdxImplicit (n + 2)

#guard_msgs(drop info) in
derive_checker (fun n => ArithIdxSucc n)

#guard_msgs(drop info) in
derive_checker (fun n => ArithIdxTwo n)

#guard_msgs(drop info) in
derive_checker (fun n => ArithIdxCtor n)

#guard_msgs(drop info) in
derive_checker (fun n => ArithIdxImplicit n)

-- The derived checkers are not merely well-typed — they decide correctly. `ArithIdxSucc` holds of
-- every `Nat`; `ArithIdxTwo` holds of exactly the even ones, so `two 3` must be a definite `no`
-- rather than `unknown`.
/-- info: succ 3 = yes, two 4 = yes, two 3 = no, ctor 3 = yes, impl 4 = yes, impl 5 = no -/
#guard_msgs in
#eval (do
  -- `Except GenError Bool` has no `ToString`, so report the verdict as a tag.
  let tag (r : Except GenError Bool) : String :=
    match r with | .ok true => "yes" | .ok false => "no" | .error _ => "unknown"
  let dec (p : Prop) [DecOpt p] (sz : Nat) : Except GenError Bool := DecOpt.decOpt p sz
  IO.println s!"succ 3 = {tag (dec (ArithIdxSucc 3) 10)}, \
    two 4 = {tag (dec (ArithIdxTwo 4) 10)}, \
    two 3 = {tag (dec (ArithIdxTwo 3) 10)}, \
    ctor 3 = {tag (dec (ArithIdxCtor 3) 10)}, \
    impl 4 = {tag (dec (ArithIdxImplicit 4) 10)}, \
    impl 5 = {tag (dec (ArithIdxImplicit 5) 10)}"
  : IO Unit)
