module

import MathlibNano.Tactic.Tauto
public import MathlibNano.Notation
-- import Init.Grind.Module.Basic -- For AddCommMonoid if it exists, or just use Add and Zero

public section

def Multiset (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset

def ofList : List α → Multiset α :=
  Quot.mk _

instance : Coe (List α) (Multiset α) := ⟨ofList⟩

def map (f : α → β) (m : Multiset α) : Multiset β :=
  Quotient.liftOn m (fun l => ofList (l.map f)) (fun _ _ p => Quotient.sound (p.map f))

def Nodup (m : Multiset α) : Prop :=
  Quotient.liftOn m List.Nodup (fun _ _ p => propext (List.Perm.nodup_iff p))

def sum [Add α] [Zero α] (m : Multiset α) : α :=
  Quotient.liftOn m List.sum (fun _ _ _ => sorry)

end Multiset

structure Finset (α : Type u) where
  val : Multiset α
  nodup : Multiset.Nodup val

namespace Finset

instance : Coe (Finset α) (Multiset α) := ⟨val⟩

def sum [Add β] [Zero β] (s : Finset α) (f : α → β) : β :=
  (s.val.map f).sum

end Finset

syntax (name := bigsum) "∑ " ident " ∈ " term ", " term:67 : term
macro_rules
| `(∑ $x:ident ∈ $s, $f) => `(Finset.sum $s (fun $x => $f))


class Fintype (α : Type u) where
  elems : Finset α

def Finset.univ [Fintype α] : Finset α := Fintype.elems

instance {n : Nat} : Fintype (Fin n) where
  elems := sorry


syntax (name := bigsum_univ) "∑ " ident " : " term ", " term:67 : term
macro_rules
| `(∑ $x:ident : $t, $f) => `(Finset.sum (Finset.univ : Finset $t) (fun ($x : $t) => $f))


def Multiset.card (m : Multiset α) : Nat :=
  Quotient.liftOn m List.length (fun _ _ p => p.length_eq)

@[simp] theorem Finset.sum_const_nat (s : Finset α) (c : Nat) : (∑ i ∈ s, c) = s.val.card * c := sorry
@[simp] theorem Finset.card_univ {n : Nat} : (Finset.univ : Finset (Fin n)).val.card = n := sorry
