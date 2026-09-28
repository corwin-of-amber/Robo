module

public import MathlibNano.Notation

public section

/-- `Even n` means `n = r + r` for some `r`. -/
def Even {α : Type u} [Add α] (n : α) : Prop := ∃ r, n = r + r

/-- `Odd n` means `n = 2 * r + 1` for some `r`. -/
def Odd {α : Type u} [Add α] [Mul α] [OfNat α 1] [OfNat α 2] (n : α) : Prop :=
  ∃ r, n = 2 * r + 1

namespace Nat

theorem even_iff {n : ℕ} : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨r, h⟩ => by omega, fun h => ⟨n / 2, by omega⟩⟩

theorem odd_iff {n : ℕ} : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨r, h⟩ => by omega, fun h => ⟨n / 2, by omega⟩⟩

instance : DecidablePred (Even : ℕ → Prop) := fun _ => decidable_of_iff _ even_iff.symm
instance : DecidablePred (Odd : ℕ → Prop) := fun _ => decidable_of_iff _ odd_iff.symm

theorem not_even_iff_odd {n : ℕ} : ¬Even n ↔ Odd n := by
  rw [even_iff, odd_iff]; omega

theorem not_odd_iff_even {n : ℕ} : ¬Odd n ↔ Even n := by
  rw [even_iff, odd_iff]; omega

end Nat

theorem Int.neg_pow_add_self {r : ℕ} (a : ℤ) : (-a) ^ (r + r) = a ^ (r + r) := by
  induction r with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + (k + 1) = (k + k) + 1 + 1 by omega,
      Int.pow_succ, Int.pow_succ, Int.pow_succ, Int.pow_succ, ih]
    grind

theorem Even.neg_pow {n : ℕ} (hn : Even n) (a : ℤ) : (-a) ^ n = a ^ n := by
  obtain ⟨r, rfl⟩ := hn
  exact Int.neg_pow_add_self a

theorem Odd.neg_pow {n : ℕ} (hn : Odd n) (a : ℤ) : (-a) ^ n = -a ^ n := by
  obtain ⟨r, rfl⟩ := hn
  rw [Int.pow_succ, Int.pow_succ, show 2 * r = r + r by omega, Int.neg_pow_add_self]
  grind
