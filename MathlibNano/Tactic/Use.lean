module

public import Lean

public section

/-- Discharger run by `use` after providing the witnesses (as in Mathlib). -/
syntax "use_discharger" : tactic
macro_rules | `(tactic| use_discharger) => `(tactic| apply And.intro <;> use_discharger)
macro_rules | `(tactic| use_discharger) => `(tactic| rfl)
macro_rules | `(tactic| use_discharger) => `(tactic| assumption)
macro_rules | `(tactic| use_discharger) => `(tactic| exact True.intro)

/-- `use e₁, e₂, …` fills in the first fields of an anonymous constructor
(e.g. the witness of an `∃`) and then tries to close trivial remaining goals. -/
syntax (name := use) "use " term,+ : tactic

macro_rules
  | `(tactic| use $es,*) => do
    let steps ← es.getElems.mapM fun e =>
      `(tactic| first | refine ⟨$e, ?_⟩ | exact ⟨$e⟩)
    `(tactic| ($[$steps]*; try with_reducible use_discharger))
