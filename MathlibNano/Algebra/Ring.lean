module

public import Init.Grind.Ring.Basic

public section

/-!
Basic (semi)ring lemmas, stated for `Lean.Grind`'s algebraic classes
(so that `grind`, and hence `ring`, work on every instance).
-/

open Lean.Grind

section Semiring
variable {α : Type u} [Semiring α]

theorem add_comm (a b : α) : a + b = b + a := Semiring.add_comm a b
theorem add_assoc (a b c : α) : a + b + c = a + (b + c) := Semiring.add_assoc a b c
theorem mul_assoc (a b c : α) : a * b * c = a * (b * c) := Semiring.mul_assoc a b c
theorem mul_add (a b c : α) : a * (b + c) = a * b + a * c := Semiring.left_distrib a b c
theorem add_mul (a b c : α) : (a + b) * c = a * c + b * c := Semiring.right_distrib a b c

end Semiring

section CommSemiring
variable {α : Type u} [CommSemiring α]

theorem mul_comm (a b : α) : a * b = b * a := CommSemiring.mul_comm a b

theorem add_pow_two (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by grind

end CommSemiring
