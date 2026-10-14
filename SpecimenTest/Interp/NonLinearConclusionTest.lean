import Specimen.Interp

/-!
# A variable repeated inside one conclusion argument

Cedar's `HasType.binaryAppEqLitSame` concludes `HasType (.binaryApp .eq (.lit p) (.lit p)) c env
(.bool .tt) []`. Both `p`s sit inside *one* argument, and the interpreter lowered that argument to the
non-linear pattern `binaryApp eq (lit p) (lit p)`: `schedulePrologue` renamed repeats by name and only
counted a variable as repeated if an *earlier* position had bound it. At run time `matchPattern` let the
second `p` overwrite the first, so `.binaryApp .eq (.lit 1) (.lit 2)` was accepted as `.bool .tt` — in
seven `HasType` generator modes, found by lowering the deriver's own premise orders and comparing. The
compile-time deriver never had the bug: `linearizeAndFlatten` renames by occurrence and emits `p_1 = p`.

`PairEq` is the smallest relation with the same shape, and each half of the fix is pinned:

1. **The lowering is linear.** The second `n` becomes `n_dup`, and `n = n_dup` is checked after every
   input `Match` — the order derived code uses, and the one that keeps the dispatch guard's view of the
   input matches whole.
2. **The matcher does not overwrite.** A repeated variable must agree with its first binding, so a
   non-linear pattern that reaches `matchPattern` anyway is still sound.

Then the semantics, in both modes that go through the prologue: the generator never tags `(1, 2)` as
equal, and the checker refutes `PairEq (1, 2) true`. `Triple` checks that the fresh name avoids a binder
the walk has not reached yet.

Sampling is seeded from `IO`, so the generator assertions are invariants (every sample), not counts.
-/

open Plausible Schedules Specimen Specimen.Interp

namespace SpecimenTest.InterpNonLinear

/-- Tags a pair with whether its components agree. `same` repeats `n` inside its first argument — the
    shape of `binaryAppEqLitSame`; `diff` is `binaryAppEqLitDiff`. -/
inductive PairEq : Nat × Nat → Bool → Prop where
  | same : ∀ n, PairEq (n, n) true
  | diff : ∀ a b, a ≠ b → PairEq (a, b) false

/-- A repeated `n` beside a binder already called `n_dup`, the name a freshening that only looked at
    what was bound so far would pick for the repeat. -/
inductive Triple : Nat × Nat × Nat → Prop where
  | mk : ∀ n n_dup, Triple (n, n, n_dup)

derive_relspec PairEq
derive_relspec Triple

def pairEqGen : SpecKey :=
  { inductiveName := ``PairEq, outputIndices := [1], deriveSort := .Generator }
def pairEqCheck : SpecKey :=
  { inductiveName := ``PairEq, outputIndices := [], deriveSort := .Checker }
def tripleCheck : SpecKey :=
  { inductiveName := ``Triple, outputIndices := [], deriveSort := .Checker }

/-! ## The lowering -/

-- The second `n` is renamed apart and the equality asserted. `linearizeAndFlatten` does the same at
-- compile time from the other end (`(n_1, n)`, then `n_1 = n`).
/-- info: "do\n    match a_1 with (n, n_dup)\n    check n = n_dup\n    return true" -/
#guard_msgs in
#eval match pairEqRelSpec.deriveMode pairEqGen with
  | .error e => e
  | .ok rel => (rel.ctorSchedule? ``PairEq.same).elim "missing" ppSchedule

-- In the checker both positions are inputs, and the check comes after *both* matches, so the input
-- `Match`es stay one contiguous run for `guardPassesWith`.
/-- info: "do\n    match a_1 with (n, n_dup)\n    match b_1 with true\n    check n = n_dup\n    return ok" -/
#guard_msgs in
#eval match pairEqRelSpec.deriveMode pairEqCheck with
  | .error e => e
  | .ok rel => (rel.ctorSchedule? ``PairEq.same).elim "missing" ppSchedule

/-! ## The matcher -/

-- A repeat must agree with its first binding, and a variable already in the environment must agree with
-- the value: neither is overwritten. Before the fix all four were `true`, and `x` ended up `2`.
/-- info: (false, true, false, true) -/
#guard_msgs in
#eval
  let x : Lean.Name := `x
  let pat : Pattern := .CtorPattern ``Prod.mk [.UnknownPattern x, .UnknownPattern x]
  let env : ValEnv := (∅ : ValEnv).insert x (toVal (2 : Nat))
  ((matchPattern pat (toVal ((1, 2) : Nat × Nat)) ∅).isSome,
   ((matchPattern pat (toVal ((3, 3) : Nat × Nat)) ∅).bind (fun b => b[x]?)) == some (toVal (3 : Nat)),
   (matchPattern (.UnknownPattern x) (toVal (1 : Nat)) env).isSome,
   (matchPattern (.UnknownPattern x) (toVal (2 : Nat)) env).isSome)

/-! ## Generation -/

def genEnv : Except String InterpEnv :=
  ({} : InterpEnv).deriveClosure [pairEqRelSpec] [pairEqGen]

-- `(1, 2)` is never tagged `true`; before the fix `same` accepted it about half the time. `(3, 3)` is
-- always tagged `true` — the control, which fails if the equality reads a name the `Match` did not
-- bind.
/-- info: (true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool) from do
  match genEnv with
  | .error _ => return (false, false, false)
  | .ok env => do
    let differ ← env.sample pairEqGen 3 [toVal ((1, 2) : Nat × Nat)] 60 60
    let agree ← env.sample pairEqGen 3 [toVal ((3, 3) : Nat × Nat)] 60 60
    return (env.check.isEmpty,
      differ.successes == 60 && differ.samples.all (· == [toVal false]),
      agree.successes == 60 && agree.samples.all (· == [toVal true]))

/-! ## Checking -/

def checkEnv : Except String InterpEnv :=
  ({} : InterpEnv).deriveClosureWith [pairEqRelSpec, tripleRelSpec] [pairEqCheck, tripleCheck]
    ({} : PlanBook)

-- `PairEq (1, 2) true` is refuted; before the fix it was accepted. The other three are controls.
/-- info: [some false, some true, some true, some false] -/
#guard_msgs in
#eval match checkEnv with
  | .error _ => []
  | .ok env =>
    let cases : List ((Nat × Nat) × Bool) :=
      [((1, 2), true), ((3, 3), true), ((1, 2), false), ((3, 3), false)]
    cases.map fun ((p, b) : (Nat × Nat) × Bool) =>
      match env.decide pairEqCheck 5 [toVal p, toVal b] with
      | .ok r => some r
      | .error _ => none

-- The fresh name for the second `n` is not `n_dup`, which the third position binds. Had it been, the
-- third component would be checked against the second and `Triple (1, 1, 5)` refuted.
/-- info: [some true, some false, some true] -/
#guard_msgs in
#eval match checkEnv with
  | .error _ => []
  | .ok env =>
    let cases : List (Nat × Nat × Nat) := [(1, 1, 5), (1, 2, 5), (4, 4, 4)]
    cases.map fun t =>
      match env.decide tripleCheck 5 [toVal t] with
      | .ok r => some r
      | .error _ => none

/-! ## The same repeat in a premise

`P x x` with `x` unbound is the premise-side twin: both positions would be outputs, the producer returns
one value per position, and `bindVars` keeps only the last, dropping the equality the premise states. The
deriver makes such a variable must-bind (`constructHypothesis`'s `repeatedNames`), so `x` is generated
first and the premise becomes a check. Lowering now raises the repairable `repeatedOutput`, and `repair`
does the same. -/

/-- Holds of equal naturals. -/
inductive SameNat : Nat → Nat → Prop where
  | refl : ∀ n, SameNat n n

/-- Every natural is its own twin — through a premise that repeats its variable. -/
inductive Twin : Nat → Prop where
  | mk : ∀ x, SameNat x x → Twin x

derive_relspec SameNat
derive_relspec Twin

def twinGen : SpecKey :=
  { inductiveName := ``Twin, outputIndices := [0], deriveSort := .Generator }

-- The plain order is refused for the right reason, and the repaired plan generates `x` first so that
-- `SameNat x x` becomes a check.
/-- info: (true, true) -/
#guard_msgs in
#eval match twinRelSpec.ctors with
  | [c] =>
    let plain := (reschedule twinRelSpec twinGen c [.use 0]).toOption.isNone
    let repaired := match repair twinRelSpec twinGen c [.use 0] with
      | .ok (plan, _) => plan.contains (.inst `x)
      | .error _ => false
    (plain, repaired)
  | _ => (false, false)

end SpecimenTest.InterpNonLinear
