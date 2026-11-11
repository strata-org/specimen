import SpecimenTest.Correctness.Suite.BST
import SpecimenTest.Correctness.Suite.STLC
import SpecimenTest.Correctness.Suite.RegExp
import SpecimenTest.Correctness.Suite.Perm
import SpecimenTest.Correctness.Suite.Balanced
import SpecimenTest.Correctness.Suite.Poly

open Plausible

/-- Of `n` runs of `g` at size `sz`, how many return a value, and the first few. -/
def sample {α : Type} [Repr α] (name : String) (g : Gen α) (n sz : Nat := 200) (sz' : Nat := 8) : IO Unit := do
  let mut ok := 0
  let mut shown : Array String := #[]
  for _ in [:n] do
    try
      let x ← Gen.run g sz'
      ok := ok + 1
      if shown.size < 3 then shown := shown.push (toString (repr x))
    catch _ => pure ()
  IO.println s!"{name}: {ok}/{n} {shown.toList.map (·.take 80)}"

#eval sample "BST 0 20" (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => Suite.BSTs.BST 0 20 t) 8)
#eval sample "STLC [] Nat→Nat" (ArbitrarySizedSuchThat.arbitrarySizedST
  (fun e => Suite.STLC.typing [] e (.Fun .Nat .Nat)) 8)
#eval sample "RegExp (1|2)*" (ArbitrarySizedSuchThat.arbitrarySizedST
  (fun s => Suite.RegExp.ExpMatch s (.Star (.Union (.Char 1) (.Char 2)))) 8)
#eval sample "Perm [1,2,3]" (ArbitrarySizedSuchThat.arbitrarySizedST
  (fun l => Suite.Perm.Permutation l [1, 2, 3]) 8)
#eval sample "balanced 3" (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => Suite.Balanced.balancedTree 3 t) 8)
#eval sample "Interleaves" (ArbitrarySizedSuchThat.arbitrarySizedST
  (fun zs => Suite.Poly.Interleaves ([1, 2] : List Nat) ['a'] zs) 8)
