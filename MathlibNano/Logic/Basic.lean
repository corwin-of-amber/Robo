module

public section

@[simp] theorem not_not {a : Prop} : ¬¬a ↔ a :=
  Classical.not_not

theorem imp_iff_or_not {b a : Prop} : b → a ↔ a ∨ ¬b :=
  @Decidable.imp_iff_or_not b a (Classical.propDecidable b)
