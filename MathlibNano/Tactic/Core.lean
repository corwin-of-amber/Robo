module

import Lean.Elab.Term
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.RCases
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Clear
public import Batteries.Lean.Expr

open Lean.Elab.Tactic Lean Elab Meta

public section

namespace Lean.MVarId

partial def intros! (mvarId : MVarId) : MetaM (Array FVarId × MVarId) :=
  run #[] mvarId
where
  run (acc : Array FVarId) (g : MVarId) :=
    try
      let ⟨f, g⟩ ← g.intro1
      run (acc.push f) g
    catch _ =>
      pure (acc, g)

end Lean.MVarId

namespace Lean.Elab.Tactic

def liftMetaTactic' (tac : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic fun g => do pure [← tac g]

def allGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList

def andThenOnSubgoals (tac1 : TacticM Unit) (tac2 : TacticM Unit) : TacticM Unit :=
  focus do tac1; allGoals tac2

partial def iterateUntilFailure (tac : m Unit) [Monad m] [MonadExcept Exception m] : m Unit :=
  try tac; iterateUntilFailure tac catch _ => pure ()

end Lean.Elab.Tactic
