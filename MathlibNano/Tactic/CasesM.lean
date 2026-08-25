import Lean.Elab.Tactic.Conv.Pattern

open Lean Meta Elab Tactic MVarId

namespace Lean.MVarId

partial def casesMatching (matcher : Expr → MetaM Bool) (recursive := false) (allowSplit := true)
    (throwOnNoMatch := true) (g : MVarId) : MetaM (List MVarId) := do
  let result := (← go g).toList
  if throwOnNoMatch && result == [g] then
    throwError "no match"
  else
    return result
where
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if ← matcher ldecl.type then
          let mut acc := acc
          let subgoals ← if allowSplit then
            g.cases ldecl.fvarId
          else
            let s ← saveState
            let subgoals ← g.cases ldecl.fvarId (givenNames := #[⟨true, [ldecl.userName]⟩])
            if subgoals.size > 1 then
              s.restore
              continue
            else
              pure subgoals
          for subgoal in subgoals do
            let g ← match subgoal.fields with
            | #[.fvar fvarId] => subgoal.mvarId.rename fvarId ldecl.userName
            | _ => pure subgoal.mvarId
            if recursive then
              acc ← go g acc
            else
              acc := acc.push g
          return acc
      return (acc.push g)

end Lean.MVarId

namespace MathlibNano.Tactic
open Lean Meta Elab Tactic MVarId

partial def constructorMatching (g : MVarId) (matcher : Expr → MetaM Bool)
    (recursive := false) (throwOnNoMatch := true) : MetaM (List MVarId) := do
  let result ←
    (if recursive then (do
      let result ← go g
      pure result.toList)
     else
      (g.withContext do
          if ← matcher (← g.getType) then g.constructor else pure [g]))
  if throwOnNoMatch && [g] == result then
    throwError "no match"
  else
    return result
where
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      if ← matcher (← g.getType) then
        let mut acc := acc
        for g' in ← g.constructor do
          acc ← go g' acc
        return acc
      return (acc.push g)

end MathlibNano.Tactic
