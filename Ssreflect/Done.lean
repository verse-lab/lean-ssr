import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Elim

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

syntax "ssr_triv_core" : tactic
syntax "ssr_triv" : tactic


macro_rules |
  `(tactic| ssr_triv_core) => `(tactic|
<<<<<<< HEAD
    try solve
     | (repeat (constructor <;> intros)) <;> simp_all
     | (repeat (constructor <;> intros)) <;> trivial)
=======
    try (solve
      | (repeat (constructor <;> intros)) <;> simp_all
      | (repeat (constructor <;> intros)) <;> trivial))
-- macro_rules |
--   `(tactic| ssr_triv_core) => `(tactic|
--     try (solve| (repeat (constructor <;> intros)) <;> trivial))
>>>>>>> 298955d (fix ssr_triv)

macro_rules |
  `(tactic| ssr_triv) => `(tactic| try (solve | ((intros; ssr_triv_core); try (intros; simp_all; ssr_triv_core))))

elab "sdone" : tactic => run `(tactic| solve | ssr_triv)

declare_syntax_cat ssrTriv
syntax "//" : ssrTriv
syntax "/=" : ssrTriv
syntax "/==" : ssrTriv
syntax "//=" : ssrTriv
syntax "//==" : ssrTriv
-- syntax ssrTriv := ssrTriv
declare_syntax_cat ssrTrivs
syntax (name:= ssrTrivs) (ppSpace colGt ssrTriv)* : ssrTrivs

macro_rules
  | `(ssrTriv| //=) => `(ssrTrivs| /= //)
  | `(ssrTriv| //==) => `(ssrTrivs| /== //)

elab_rules : tactic
  | `(ssrTriv|  //) =>
    tryGoal $ run `(tactic| ssr_triv)
  | `(ssrTriv|  /=) => run `(tactic| try dsimp)
  | `(ssrTriv| /==) => run `(tactic| try simp)

elab_rules : tactic
  | `(ssrTrivs| $ts:ssrTriv *) => elabTactic $ mkNullNode ts

syntax (name:= sby) "sby " tacticSeq : tactic

@[tactic sby] def elabSby : Tactic
  | `(tactic| sby%$sby $ts) => do
    evalTactic ts
    unless (<- getUnsolvedGoals).length = 0 do
      tryGoal $ allGoal $ run `(tactic| solve | ssr_triv)
    unless (<- getUnsolvedGoals).length = 0 do
      throwErrorAt sby "No applicable tactic"
  | _ => throwError "Unsupported index for sby"
