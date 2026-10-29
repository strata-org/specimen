import Specimen
import Specimen.Basalt

/-!
# A checker's search agrees with the enumeration, and stops early

Under `specimen.emitBasalt` a derived checker asks its premises' enumerators through
`Specimen.CheckerSearch`, which runs them at `Specimen.Search`. Here the search's answer is checked
against the strict reading's, the Kleene disjunction of every entry `Finite` lists, for a derived
enumerator across inputs, sizes and continuations; and a checker answers at a size whose enumeration
the strict reading would have to build in full first.
-/

set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true

namespace CheckerSearchTest

open Specimen

inductive Between : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, lo ≤ hi → Between lo hi lo
  | there : ∀ lo hi n, Between (lo + 1) hi n → Between lo hi n

#guard_msgs(drop info, drop warning) in
derive_mutual enumerator (fun lo hi => ∃ n, Between lo hi n)

/-- The strict reading's answer: the disjunction of every entry, in order, a label undecided. -/
def finiteVerdict (x : ExceptT Exhaustion Finite α) (k : α → Verdict) : Verdict :=
  match x.run.toList? with
  | none => .undef
  | some l => Verdict.any (l.map fun e _ => match e with | .ok a => k a | .error _ => .unknown)

def agree (lo hi sz : Nat) (k : Nat → Verdict) : Bool :=
  (EnumFor.enum (P := fun n => Between lo hi n) (G := Search) sz sz).run k ==
    finiteVerdict (EnumFor.enum (P := fun n => Between lo hi n) (G := ExceptT Exhaustion Finite) sz sz) k

def continuations : List (Nat → Verdict) :=
  [fun n => if n == 2 then .yes else .no, fun _ => .no, fun _ => .yes,
   fun n => if n % 2 == 0 then .yes else .unknown, fun _ => .unknown]

#guard (List.range 4).all fun lo => (List.range 6).all fun hi => (List.range 6).all fun sz =>
  continuations.all (agree lo hi sz)

/-! ## A checker that stops at the first success -/

inductive Mem {α : Type} : α → List α → Prop where
  | here : ∀ x xs, Mem x (x :: xs)
  | there : ∀ x y xs, Mem x xs → Mem x (y :: xs)

inductive Uses : Nat → Prop where
  | mk : ∀ n l, Mem n l → Uses n

#guard_msgs(drop info) in
derive_mutual checker (fun n => Uses n)

-- The enumeration of lists for `∃ l, Mem 3 l` at size 8 runs to the hundreds of millions.
#guard match DecOpt.decOpt (Uses 3) 8 with | .ok true => true | _ => false

end CheckerSearchTest
