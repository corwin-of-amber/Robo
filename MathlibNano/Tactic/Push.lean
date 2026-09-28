module

public meta import Lean
public import MathlibNano.Logic.Basic

public meta section

open Lean Meta Elab Tactic

/-- Lemmas used by `push Not` to move negations inwards. -/
def pushNotLemmas : List Name :=
  [``not_not, ``not_and, ``not_or, ``Classical.not_forall, ``not_exists, ``Classical.not_imp,
   ``Nat.not_le, ``Nat.not_lt, ``Int.not_le, ``Int.not_lt]

def pushNotCtx : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in pushNotLemmas do
    thms ← thms.addConst n
  Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- Simplify `e` using only `pushNotLemmas` (no simprocs, so e.g. `A ↔ A` is not closed). -/
def pushNot (e : Expr) : MetaM Simp.Result := do
  let (r, _) ← Simp.main (← instantiateMVars e) (← pushNotCtx)
    (methods := Simp.mkDefaultMethodsCore #[])
  return r

/-- `push Not` (or `push ¬ _`) pushes negations past quantifiers and connectives,
in the goal or (with `at h`) in hypotheses. Unlike `simp`, it never closes the goal. -/
syntax (name := push) "push " term (Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| push $t $[$loc?]?) => withMainContext do
    match t with
    | `(Not) | `(¬ _) => pure ()
    | _ => throwErrorAt t "push: only `push Not` is supported"
    let (hyps, type) ← match expandOptLocation (mkOptionalNode loc?) with
      | .targets hyps type => pure (hyps, type)
      | .wildcard => throwError "push Not at *: not supported"
    let mut goal ← getMainGoal
    if type then
      let tgt ← goal.getType
      let r ← pushNot tgt
      if r.expr == (← instantiateMVars tgt) then throwError "push Not made no progress"
      goal ← applySimpResultToTarget goal tgt r
    for h in hyps do
      let fvarId ← goal.withContext <| getFVarId h
      let r ← goal.withContext <| pushNot (← fvarId.getType)
      match ← applySimpResultToLocalDecl goal fvarId r false with
      | none => replaceMainGoal []; return  -- hypothesis became `False`
      | some (_, g) => goal := g
    replaceMainGoal [goal]
