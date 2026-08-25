import Lean

namespace MathlibNano.Tactic
open Lean Elab Tactic Parser.Tactic

-- A minimalist "nano" version of Mathlib's ring tactic that can solve
-- simple commutative ring identities (like n * 2 = 2 * n) by relying on the simplifier
macro (name := ring) "ring" : tactic =>
  `(tactic| (simp [Nat.add_comm, Nat.mul_comm, Nat.add_assoc, Nat.mul_assoc, Nat.add_left_comm, Nat.mul_left_comm, Nat.add_mul, Nat.mul_add, Nat.right_distrib, Nat.left_distrib]))

end MathlibNano.Tactic
