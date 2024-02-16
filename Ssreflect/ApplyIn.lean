-- import Mathlib
import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Elim

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

private def Lean.Meta.forallMetaTelescopeReducingUntilDefEq
    (e t : Expr) (kind : MetavarKind := MetavarKind.natural) :
    MetaM (Array Expr × Array BinderInfo × Expr) := do
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do
    if ms.size == 0 then throwError m!"Failed: {← ppExpr e} is not the type of a function."
    else throwError m!"Failed"
  let mut mvs := ms
  let mut bis := bs
  let mut out : Expr := tp
  while !(← isDefEq (← inferType mvs.toList.getLast!) t) do
    let (ms, bs, tp) ← forallMetaTelescopeReducing out (some 1) kind
    unless ms.size == 1 do
      throwError m!"Failed to find {← ppExpr t} as the type of a parameter of {← ppExpr e}."
    mvs := mvs ++ ms
    bis := bis ++ bs
    out := tp
  return (mvs, bis, out)

private def applyIn (stx : Syntax) (ldecl : LocalDecl) : TacticM Expr := do
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
