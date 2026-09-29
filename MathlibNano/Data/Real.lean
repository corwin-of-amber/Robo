module

public import Init.Grind.Ring.Field

public section

/-!
# Real numbers (axiomatic)

A placeholder for Mathlib's `ℝ`: an abstract type postulated to be a field of
characteristic zero. This is enough for purely algebraic reasoning (`rw`, `ring`);
replace it by a construction (or extend the axioms, e.g. with an order) as needed.
-/

axiom Real : Type

notation "ℝ" => Real

namespace Real

axiom instField : Lean.Grind.Field ℝ
noncomputable instance : Lean.Grind.Field ℝ := instField

axiom instIsCharP : Lean.Grind.IsCharP ℝ 0
instance : Lean.Grind.IsCharP ℝ 0 := instIsCharP

end Real
