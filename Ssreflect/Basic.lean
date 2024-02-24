import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils

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

declare_syntax_cat ssrBasic
syntax "{" (ppSpace colGt term:max)+ "}" : ssrBasic
syntax "/[tac " tactic "]" : ssrBasic

elab_rules : tactic
  | `(ssrBasic| { $ts:term* }%$br) =>
     withRef br do run `(tactic| clear $ts*)
  | `(ssrBasic| /[tac%$tc $t:tactic]) =>
      withRef tc do run `(tactic| $t)

-- partial def elabBasic : Tactic := fun stx => newTactic do
--   withTacticInfoContext (<- getRef) do
--   match stx with
--   | `(ssrBasic| { $ts:term* }) => newTactic do
--       run `(tactic| clear $ts*)
--   | `(ssrBasic| /[tac $t:tactic]) => newTactic do
--       run `(tactic| $t)
--   | _ => throwErrorAt stx "Unknown action"
