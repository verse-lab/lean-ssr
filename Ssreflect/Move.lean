import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import «Ssreflect».Utils

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

elab "moveR" : tactic => newTactic do
  let mId <- mkFreshExprMVar $ <- whnfR (<- getMainTarget)
  (<- getMainGoal).assign mId
  setGoals [mId.mvarId!]

elab "move" : tactic => newTactic do
  let mId <- mkFreshExprMVar $ <- whnf (<- getMainTarget)
  (<- getMainGoal).assign mId
  setGoals [mId.mvarId!]
