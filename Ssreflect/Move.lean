import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import «Ssreflect».Utils

elab "move" : tactic => newTactic do
  let goalT <- whnfR (<- getMainTarget)
  let goal <- getMainGoal
  let mId <- mkFreshExprMVar goalT
  goal.assign mId
  setGoals [mId.mvarId!]

def foo (k : Nat) : Prop :=
  match k with
  | 0 => True
  | n + 1 => False
