import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic
-- open Lean.Elab.Tactic.Conv.PatternMatchState

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

structure stateVisit where
  idx : Nat := 1
  exps : Array Expr := #[]

private def kpattern (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  if p.isFVar && occs == Occurrences.all then
    return e.abstract #[p] -- Easy case
  else
    let pHeadIdx := p.toHeadIndex
    let pNumArgs := p.headNumArgs
    let rec visit (e : Expr) (offset : Nat) : StateRefT stateVisit MetaM Unit := do
      let visitChildren : Unit → StateRefT stateVisit MetaM Unit := fun _ => do
        match e with
        | .app f a         => visit f offset; visit a offset
        | .mdata _ b       => visit b offset
        | .proj _ _ b      => visit b offset
        | .letE _ t v b _  => visit t offset; visit v offset; visit b (offset+1)
        | .lam _ d b _     => visit d offset; visit b (offset+1)
        | .forallE _ d b _ => visit d offset; visit b (offset+1)
        | _                => return ()
      if e.hasLooseBVars then
        visitChildren ()
      else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
        visitChildren ()
      else
        -- We save the metavariable context here,
        -- so that it can be rolled back unless `occs.contains i`.
        let mctx ← getMCtx
        if (← isDefEq e p) then
          let i := (← get).idx
          modify $ fun st => { st with idx := i+1 }
          if occs.contains i then
            modify $ fun st => { st with exps := st.exps.push e }
          else
            -- Revert the metavariable context,
            -- so that other matches are still possible.
            setMCtx mctx
            visitChildren ()
        else
          visitChildren ()
    let (_, e) <- visit e 0 |>.run {}
    if e.exps.size = 0 then
      throwError "Pattern was not found"
    else return e.exps[0]!

elab "scase_if" : tactic => newTactic do
  let t <- `(term| ite _ _ _)
  let t <- Term.elabTerm t none
  let ifc <- kpattern (<-getMainTarget) t
  let t <- PrettyPrinter.delab ifc.getAppArgs[1]!
  let name <- fresh "H"
  run `(tactic| by_cases $name : $t)
  allGoal $ run `(tactic| try simp only [↓reduceIte, $name:term])
  tryGoal $ allGoal $ run `(tactic| revert $name)

-- def store : StateRefT Expr MetaM Unit

-- example (n : Nat) : if n = 0 then False else False := by
--   scase_if
