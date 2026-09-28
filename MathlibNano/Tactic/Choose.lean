module

public import Lean

public section

/-- `choose x hx using h` decomposes `h : ∃ x, P x` into `x` and `hx : P x`.
For `h : ∀ a, ∃ b, P a b` it produces a choice function `f` with `hf : ∀ a, P a (f a)`. -/
syntax (name := choose) "choose " (ppSpace colGt Lean.binderIdent)+ " using " term : tactic

macro_rules
  | `(tactic| choose $xs* using $h) => do
    let pats ← xs.mapM fun
      | `(Lean.binderIdent| $x:ident) => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)
      | _ => `(Lean.Parser.Tactic.rcasesPatLo| _)
    `(tactic| first
      | obtain ⟨$pats,*⟩ := $h
      | (obtain ⟨$pats,*⟩ := Classical.axiomOfChoice $h; try clear $h))
