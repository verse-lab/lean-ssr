import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.IntroPats

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

elab "shave" is:ssrIntros ":" t:term : tactic => do
  let h <- fresh "H"
  run `(tactic| have $h : $t := ?_)
  let goal <- getMainGoal
  let goals <-getUnsolvedGoals
  setGoals [goal]
  run `(tactic| revert $h)
  tryGoal $ elabSsrs is
  setGoals $ goals ++ (<-getUnsolvedGoals)
