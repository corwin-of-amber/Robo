module

public meta import Lean

public meta section

open Lean Meta Elab Tactic

/-- A "nano" version of Mathlib's `ring`: proves equalities in commutative (semi)rings.
It discards all propositional hypotheses (so, like `ring`, it does not use assumptions)
and then relies on `grind`'s commutative ring solver. -/
elab (name := ring) "ring" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for ldecl in (← getLCtx).getFVarIds.reverse do
      let decl ← ldecl.getDecl
      unless decl.isImplementationDetail do
        if ← isProp decl.type then
          g ← g.tryClear ldecl
    pure g
  replaceMainGoal [g]
  try evalTactic (← `(tactic| grind))
  catch _ => throwError "ring failed to prove the goal"
