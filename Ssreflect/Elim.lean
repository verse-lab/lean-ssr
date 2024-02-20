import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic
import Lean.HeadIndex

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic
-- open Lean.Elab.Tactic.Conv.PatternMatchState
open Lean.Elab.Tactic.Conv Lean.Parser.Tactic.Conv

elab "scase" : tactic => newTactic do
    let hyps <- getLCtx
    let name <- fresh "H"
    run `(tactic| intro $name:ident)
    run `(tactic| unhygienic cases $name:ident)
    allGoal do
      let hypsNew <- getLCtx
      for hyp in hypsNew do
        unless hyps.contains hyp.fvarId do
          run `(tactic| try revert $(mkIdent hyp.userName):ident)


elab "elim" : tactic => newTactic do
    let hyps <- getLCtx
    let name <- fresh "H"
    run `(tactic| intro $name:ident)
    run `(tactic| unhygienic induction $name:ident)
    newTactic $ allGoal do
      let hypsNew <- getLCtx
      -- IO.println s! "{hypsNew.decls.toArray.map (fun x => LocalDecl.userName <$> x)}"
      for hyp in hypsNew do
        unless hyps.findFromUserName? hyp.userName |> Option.isSome do
          tryGoal $ run `(tactic| revert $(mkIdent hyp.userName):ident)


private def getContext : MetaM Simp.Context := do
  return {
    simpTheorems  := {}
    congrTheorems := (← getSimpCongrTheorems)
    config        := Simp.neutralConfig
  }

private def pre (pattern : AbstractMVarsResult) (state : IO.Ref PatternMatchState) (e : Expr) : SimpM Simp.Step := do
  if (← state.get).isDone then
    return Simp.Step.done { expr := e }
  else if let some (e, extraArgs) ← matchPattern? pattern e then
    if (← state.get).isReady then
      let (rhs, newGoal) ← mkConvGoalFor e
      state.modify (·.accept newGoal.mvarId!)
      let mut proof := newGoal
      for extraArg in extraArgs do
        proof ← mkCongrFun proof extraArg
      return Simp.Step.done { expr := mkAppN rhs extraArgs, proof? := proof }
    else
      state.modify (·.skip)
      -- Note that because we return `visit` here and `done` in the other case,
      -- it is possible for skipping an earlier match to affect what later matches
      -- refer to. For example, matching `f _` in `f (f a) = f b` with occs `[1, 2]`
      -- yields `[f (f a), f b]`, but `[2, 3]` yields `[f a, f b]`, and `[1, 3]` is an error.
      return Simp.Step.continue
  else
    return Simp.Step.continue

declare_syntax_cat caseIf
syntax ocs := (occsWildcard <|> occsIndexed)
syntax (ocs)? ".": caseIf

private def evalP : TacticM Expr := withMainContext do
  let p <- `(term| ite _ _ _)
  let occs <- `(Parser.Tactic.Conv.occsIndexed| 1)
  let patternA ←
      withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
      Term.withoutModifyingElabMetaStateWithInfo <| withRef p <|
      Term.withoutErrToSorry do
        abstractMVars (← Term.elabTerm p none)
  let occs ← match some occs with
  | none => pure (PatternMatchState.occs #[] 0 [(0, 0)])
  | some occs => match occs with
    | `(Parser.Tactic.Conv.occsWildcard| *) => pure (.all #[])
    | `(Parser.Tactic.Conv.occsIndexed| $ids*) => do
      let ids ← ids.mapIdxM fun i id =>
        match id.getNat with
        | 0 => throwErrorAt id "positive integer expected"
        | n+1 => pure (n, i.1)
      let ids := ids.qsort (·.1 < ·.1)
      unless @Array.allDiff _ ⟨(·.1 == ·.1)⟩ ids do
        throwError "occurrence list is not distinct"
      pure (.occs #[] 0 ids.toList)
    | _ => throwUnsupportedSyntax
  let state ← IO.mkRef occs
  let ctx <- getContext
  let ctx := { ctx with config.memoize := occs matches PatternMatchState.all _ }
  let _ ← Simp.main (<- getMainTarget) ctx (methods := { pre := pre patternA state })
  let subgoals ← match ← state.get with
  | .all #[] | .occs _ 0 _ =>
    throwError "case_if tactic failed, pattern was not found{indentExpr patternA.expr}"
  | .all subgoals => pure subgoals
  | .occs subgoals idx remaining =>
    if let some (i, _) := remaining.getLast? then
      throwError "'pattern' conv tactic failed, pattern was found only {idx} times but {i+1} expected"
    pure <| (subgoals.qsort (·.1 < ·.1)).map (·.2)
  newTactic do
    let [subgoal] := subgoals.toList | throwError "Something wnt wrong"
    let s <- subgoal.getType
    let fvarIds := (<-getLCtx).getFVarIds
    let names ← fvarIds.mapM (fun fid => do
    match ← fid.findDecl? with
    | .some decl => return decl.userName
    | .none => throwError "Expr.formatWithUsername :: Unknown free variable {(Expr.fvar fid).dbgToString}")
    let s := s.replaceFVars (fvarIds.map Expr.fvar) (names.map (Expr.const · []))
    newTactic do
      tryGoal $ allGoal $ run `(tactic| rfl)
    setGoals [<- getMainGoal]
    newTactic do
    return s.consumeMData.getAppArgs[1]!.getAppArgs[1]!

elab "scase_if" : tactic => do
  let ifc <- evalP
  let t <- PrettyPrinter.delab ifc
  let name <- fresh "H"
  run `(tactic| by_cases $name : $t)
  allGoal $ run `(tactic| try simp only [↓reduceIte, $name:term])
  allGoal $ run `(tactic| revert $name)

-- def store : StateRefT Expr MetaM Unit

-- example (n : Nat) : if n = 0 then True else False := by
--   scase_if
