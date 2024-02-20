import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.IntroPats

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

elab "shave" is:ssr_intros ":" t:term : tactic => do
  let h <- fresh "H"
  run `(tactic| have $h : $t := ?_)
  let goal <- getMainGoal
  let goals <-getUnsolvedGoals
  setGoals [goal]
  run `(tactic| revert $h)
  elabSsr.many is
  let goal <- getMainGoal
  setGoals [goals[1]!, goal]
