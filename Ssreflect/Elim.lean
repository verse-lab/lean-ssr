import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

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
      IO.println s! "{hypsNew.decls.toArray.map (fun x => LocalDecl.userName <$> x)}"
      for hyp in hypsNew do
        unless hyps.findFromUserName? hyp.userName |> Option.isSome do
          tryGoal $ run `(tactic| revert $(mkIdent hyp.userName):ident)
