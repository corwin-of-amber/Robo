module

public import Init.Grind.Ring.Basic

@[expose] public section

/-!
# Multivariate polynomials

`MvPolynomial σ R` is the free commutative `R`-algebra on variables `X i` for `i : σ`,
constructed as expression trees modulo the commutative semiring laws
(and the requirement that `C : R → MvPolynomial σ R` is a semiring homomorphism).
-/

open Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast

namespace MvPolynomial

/-- Raw polynomial expressions, before quotienting by the semiring laws. -/
inductive Pre (σ : Type u) (R : Type v) : Type (max u v)
  | C : R → Pre σ R
  | X : σ → Pre σ R
  | add : Pre σ R → Pre σ R → Pre σ R
  | mul : Pre σ R → Pre σ R → Pre σ R

variable {σ : Type u} {R : Type v} [CommSemiring R]

/-- The smallest congruence on `Pre σ R` containing the commutative semiring laws. -/
inductive Rel : Pre σ R → Pre σ R → Prop
  | refl p : Rel p p
  | symm : Rel p q → Rel q p
  | trans : Rel p q → Rel q r → Rel p r
  | add_congr : Rel p p' → Rel q q' → Rel (.add p q) (.add p' q')
  | mul_congr : Rel p p' → Rel q q' → Rel (.mul p q) (.mul p' q')
  | add_zero p : Rel (.add p (.C 0)) p
  | add_comm p q : Rel (.add p q) (.add q p)
  | add_assoc p q r : Rel (.add (.add p q) r) (.add p (.add q r))
  | mul_assoc p q r : Rel (.mul (.mul p q) r) (.mul p (.mul q r))
  | mul_comm p q : Rel (.mul p q) (.mul q p)
  | mul_one p : Rel (.mul p (.C 1)) p
  | zero_mul p : Rel (.mul (.C 0) p) (.C 0)
  | left_distrib p q r : Rel (.mul p (.add q r)) (.add (.mul p q) (.mul p r))
  | C_add (a b : R) : Rel (.C (a + b)) (.add (.C a) (.C b))
  | C_mul (a b : R) : Rel (.C (a * b)) (.mul (.C a) (.C b))

instance setoid (σ : Type u) (R : Type v) [CommSemiring R] : Setoid (Pre σ R) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

end MvPolynomial

/-- Multivariate polynomials in variables indexed by `σ` with coefficients in `R`. -/
def MvPolynomial (σ : Type u) (R : Type v) [CommSemiring R] : Type (max u v) :=
  Quotient (MvPolynomial.setoid σ R)

namespace MvPolynomial

variable {σ : Type u}

section Semiring

variable {R : Type v} [CommSemiring R]

/-- The constant polynomial `a`. -/
def C (a : R) : MvPolynomial σ R := Quotient.mk _ (.C a)

/-- The variable `X i`. -/
def X (i : σ) : MvPolynomial σ R := Quotient.mk _ (.X i)

instance : Add (MvPolynomial σ R) where
  add := Quotient.lift₂ (fun p q => Quotient.mk _ (.add p q))
    fun _ _ _ _ hp hq => Quotient.sound (Rel.add_congr hp hq)

instance : Mul (MvPolynomial σ R) where
  mul := Quotient.lift₂ (fun p q => Quotient.mk _ (.mul p q))
    fun _ _ _ _ hp hq => Quotient.sound (Rel.mul_congr hp hq)

instance : NatCast (MvPolynomial σ R) := ⟨fun n => C (n : R)⟩
instance (n : Nat) : OfNat (MvPolynomial σ R) n := ⟨C (OfNat.ofNat n)⟩
instance : SMul Nat (MvPolynomial σ R) := ⟨fun n p => C (n : R) * p⟩

/-- `p ^ n`, by repeated multiplication. -/
protected def npow (p : MvPolynomial σ R) : Nat → MvPolynomial σ R
  | 0 => 1
  | n + 1 => p.npow n * p

/-- A high-priority default instance (like Mathlib's `Monoid.Pow`), so that in `X 0 ^ 2`
the result type is fixed to the base type before the numeral `0 : σ` defaults to `ℕ`. -/
@[default_instance high] instance : Pow (MvPolynomial σ R) Nat := ⟨MvPolynomial.npow⟩

theorem C_add (a b : R) : (C (a + b) : MvPolynomial σ R) = C a + C b :=
  Quotient.sound (Rel.C_add a b)

theorem C_mul (a b : R) : (C (a * b) : MvPolynomial σ R) = C a * C b :=
  Quotient.sound (Rel.C_mul a b)

protected theorem add_zero (a : MvPolynomial σ R) : a + 0 = a := by
  induction a using Quotient.ind; exact Quotient.sound (Rel.add_zero _)

protected theorem add_comm (a b : MvPolynomial σ R) : a + b = b + a := by
  induction a using Quotient.ind; induction b using Quotient.ind
  exact Quotient.sound (Rel.add_comm _ _)

protected theorem add_assoc (a b c : MvPolynomial σ R) : a + b + c = a + (b + c) := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind
  exact Quotient.sound (Rel.add_assoc _ _ _)

protected theorem mul_assoc (a b c : MvPolynomial σ R) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind
  exact Quotient.sound (Rel.mul_assoc _ _ _)

protected theorem mul_comm (a b : MvPolynomial σ R) : a * b = b * a := by
  induction a using Quotient.ind; induction b using Quotient.ind
  exact Quotient.sound (Rel.mul_comm _ _)

protected theorem mul_one (a : MvPolynomial σ R) : a * 1 = a := by
  induction a using Quotient.ind; exact Quotient.sound (Rel.mul_one _)

protected theorem one_mul (a : MvPolynomial σ R) : 1 * a = a := by
  rw [MvPolynomial.mul_comm, MvPolynomial.mul_one]

protected theorem zero_mul (a : MvPolynomial σ R) : 0 * a = 0 := by
  induction a using Quotient.ind; exact Quotient.sound (Rel.zero_mul _)

protected theorem left_distrib (a b c : MvPolynomial σ R) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind
  exact Quotient.sound (Rel.left_distrib _ _ _)

protected theorem right_distrib (a b c : MvPolynomial σ R) : (a + b) * c = a * c + b * c := by
  rw [MvPolynomial.mul_comm, MvPolynomial.left_distrib, MvPolynomial.mul_comm c,
    MvPolynomial.mul_comm c]

instance : CommSemiring (MvPolynomial σ R) where
  add_zero := MvPolynomial.add_zero
  add_comm := MvPolynomial.add_comm
  add_assoc := MvPolynomial.add_assoc
  mul_assoc := MvPolynomial.mul_assoc
  mul_one := MvPolynomial.mul_one
  one_mul := MvPolynomial.one_mul
  left_distrib := MvPolynomial.left_distrib
  right_distrib := MvPolynomial.right_distrib
  zero_mul := MvPolynomial.zero_mul
  mul_zero a := by rw [MvPolynomial.mul_comm, MvPolynomial.zero_mul]
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    show C _ = C _ + C _
    rw [← C_add, Semiring.ofNat_succ]
  ofNat_eq_natCast n := congrArg C (Semiring.ofNat_eq_natCast n)
  nsmul_eq_natCast_mul _ _ := rfl
  mul_comm := MvPolynomial.mul_comm

end Semiring

section Ring

variable {R : Type v} [CommRing R]

instance : Neg (MvPolynomial σ R) := ⟨fun p => C (-1) * p⟩
instance : Sub (MvPolynomial σ R) := ⟨fun p q => p + -q⟩
instance : IntCast (MvPolynomial σ R) := ⟨fun i => C (i : R)⟩
instance : SMul Int (MvPolynomial σ R) := ⟨fun i p => C (i : R) * p⟩

instance : CommRing (MvPolynomial σ R) where
  neg_add_cancel a := by
    show C (-1) * a + a = C 0
    conv => lhs; rhs; rw [← MvPolynomial.one_mul a]
    show C (-1) * a + C 1 * a = C 0
    rw [← MvPolynomial.right_distrib, ← C_add, show (-1 + 1 : R) = 0 by grind]
    exact MvPolynomial.zero_mul a
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i a := by
    show C _ * a = C (-1) * (C _ * a)
    rw [← MvPolynomial.mul_assoc, ← C_mul, show ((-i : Int) : R) = -1 * (i : R) by grind]
  zsmul_natCast_eq_nsmul n a := by
    show C _ * a = C _ * a
    rw [Ring.intCast_natCast]
  intCast_ofNat n := congrArg C (Ring.intCast_ofNat n)
  intCast_neg i := by
    show C _ = C (-1) * C _
    rw [← C_mul, show ((-i : Int) : R) = -1 * (i : R) by grind]
  mul_comm := MvPolynomial.mul_comm

end Ring

end MvPolynomial
