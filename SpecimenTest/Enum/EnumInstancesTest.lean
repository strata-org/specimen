import Specimen.Enumerators

/-! Tests for basic `Enum` instances on `Nat`, `Bool`, `Fin`, pairs, sums, and lists. -/

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat) 15)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat) 7)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Fin 5) 5)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Fin 10) 10)



#guard_msgs(error, drop info) in
#eval (runEnum (α := Bool) 10)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat × Bool) 5)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat ⊕ Bool) 5)

#guard_msgs(error, drop info) in
#eval (runEnum (α := List Nat) 3)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Char) 20)
