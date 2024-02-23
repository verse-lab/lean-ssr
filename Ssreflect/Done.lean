import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

syntax "ssr_triv_core" : tactic
syntax "ssr_triv" : tactic

macro_rules |
  `(tactic| ssr_triv_core) => `(tactic|
    try solve| repeat (constructor <;> intros) <;> trivial)
macro_rules |
  `(tactic| ssr_triv_core) => `(tactic|
    try solve| repeat (constructor <;> intros) <;> simp_all)

macro_rules |
  `(tactic| ssr_triv) => `(tactic| try solve | ((intros; ssr_triv_core); try (intros; simp_all; ssr_triv_core)))

declare_syntax_cat ssrTriv
syntax "//" : ssrTriv
syntax "/=" : ssrTriv
syntax "/==" : ssrTriv
syntax "//=" : ssrTriv
syntax "//==" : ssrTriv
-- syntax ssrTriv := ssrTriv
declare_syntax_cat ssrTrivs
syntax (ppSpace colGt ssrTriv)* : ssrTrivs

macro_rules
  | `(ssrTriv| //=) => `(ssrTrivs| /= //)
macro_rules
  | `(ssrTriv| //==) => `(ssrTrivs| /== //)


def elabSTriv : Tactic := fun stx => do
  withTacticInfoContext (<- getRef) do
  match stx with
  | `(ssrTriv| //)  => run `(tactic| ssr_triv)
  | `(ssrTriv| /=)  => run `(tactic| try dsimp)
  | `(ssrTriv| /==) => run `(tactic| try simp)
  | _               => throwErrorAt stx "Unsupported ssr_triv syntax"

syntax (name:= sby) "sby " tacticSeq : tactic

@[tactic sby] def elabSby : Tactic
  | `(tactic| sby%$sby $ts) => do
    evalTactic ts
    unless (<- getUnsolvedGoals).length = 0 do
      tryGoal $ allGoal $ run `(tactic| solve | ssr_triv)
    unless (<- getUnsolvedGoals).length = 0 do
      throwErrorAt sby "No applicable tactic"
  | _ => throwError "Unsupported index for sby"
