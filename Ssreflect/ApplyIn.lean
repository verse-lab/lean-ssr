import Mathlib
import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import «Ssreflect».Utils
import «Ssreflect».Elim

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

def applyIn (stx : Syntax) (ldecl : LocalDecl) : TacticM Expr := do
  withNewMCtxDepth do
    let f ← elabTermForApply stx
    let (mvs, bis, _) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
    for (m, b) in mvs.zip bis do
      if b.isInstImplicit && !(← m.mvarId!.isAssigned) then
        try m.mvarId!.inferInstance
        catch _ => continue
    let t <- mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map some)
    return (<- abstractMVars t).expr

elab "apply" t:term "in" name:ident : tactic => newTactic do
  let i := (<- getLCtx).findFromUserName? name.getId
  let t <- applyIn t i.get!; let ty <- inferType t
  setGoals [<- (<- getMainGoal).assert name.getId ty t]
  tryGoal $ run `(tactic| clear $name:ident)
