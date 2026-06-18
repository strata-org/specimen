import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

/-! Experiment: confirm that Specimen's scheduler ALREADY emits a mode-directed
    producer step for a bare-predicate hypothesis (here `freshDef x l`, with `l`
    an input and `x` the output). The only thing missing in `DefWrappedExp.lean`
    was an instance for that mode. If we supply a *sound, efficient* producer for
    the mode `freshDef(+l, -x)`, the same derivation should compile and generate
    genuinely fresh variables — no generate-and-check, no backtracking. -/

open Plausible

set_option guard_msgs.diff true

def myFreeVars (l : List Nat) : List Nat := l
def freshDef (x : Nat) (l : List Nat) : Prop := x ∉ myFreeVars l

/-- A mode-directed producer for `freshDef(+l, -x)`: given the input `l`,
    compute its "free variables" and return one guaranteed not to be in the list
    (here: one more than the maximum). This is sound by construction — every
    value it produces satisfies `freshDef x l` — and needs no candidate from the
    caller, unlike a `DecOpt` check. -/
instance (l : List Nat) : ArbitrarySizedSuchThat Nat (fun x => freshDef x l) where
  arbitrarySizedST _ := return (l.foldr Nat.max 0) + 1

inductive WantsFreshDef : List Nat → Nat → Prop where
  | mk : ∀ l x, freshDef x l → WantsFreshDef l x

-- With the mode-directed producer in scope, this now compiles (cf. DefWrappedExp).
derive_generator (fun (l : List Nat) => ∃ (x : Nat), WantsFreshDef l x)

-- And it produces fresh variables directly, every time:
#eval show IO Unit from do
  let mut i := 0
  while i < 5 do
    let x ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun x => WantsFreshDef [3, 7, 2] x) 4) 4
    IO.println s!"fresh w.r.t. [3,7,2] => {repr x}"
    i := i + 1
