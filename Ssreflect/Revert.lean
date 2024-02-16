import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

declare_syntax_cat ssr_reverts
declare_syntax_cat ssr_revert
-- intros
syntax ident : ssr_revert
syntax "(" term ")" : ssr_revert

-- syntax ssr_reverts ppSpace ssr_revert : ssr_reverts
syntax (ppSpace colGt ssr_revert)* : ssr_reverts

def mkTacticInfoR (mctxBefore : MetavarContext) (goalsBefore : List MVarId) (stx : Syntax) : TacticM Info :=
  return Info.ofTacticInfo {
    elaborator    := (← read).elaborator
    mctxBefore    := (← getMCtx)
    goalsBefore   := (← getUnsolvedGoals)
    stx           := stx
    mctxAfter     := mctxBefore
    goalsAfter    := goalsBefore
  }

def mkInitialTacticInfoR (stx : Syntax) : TacticM (TacticM Info) := do
  let mctxBefore  ← getMCtx
  let goalsBefore ← getUnsolvedGoals
  return mkTacticInfoR mctxBefore goalsBefore stx

@[inline] def withTacticInfoContextR (stx : Syntax) (x : TacticM α) : TacticM α := do
  withInfoContext x (← mkInitialTacticInfoR stx)

def elabSsrR (stx :  TSyntax `ssr_revert) : TacticM Unit := withTacticInfoContextR stx $ newTactic do
    match stx with
    | `(ssr_revert|$i:ident) => newTactic do
        run (stx := stx) `(tactic| revert $i:ident)
    | `(ssr_revert|($t:term)) => newTactic do
        let h <- fresh "H"
        run (stx := stx) `(tactic| have $h := $t)
        run (stx := stx) `(tactic| revert $h)
        tryGoal $ run (stx := stx) `(tactic| clear $h)
    | _ => throwErrorAt stx "Unknown action"
  where
    many (stx : TSyntax `ssr_reverts) : TacticM Unit :=
    match stx with
    | `(ssr_reverts| $[$is:ssr_revert] *) => newTactic do
      for i in is.reverse do allGoal $ elabSsrR i
    | _ => throwErrorAt stx "Unknown action"


elab t:tactic ":" is:ssr_reverts : tactic => do
  elabSsrR.many is; run `(tactic|$t);

-- example (k : Int) : Int := by
--   skip: k (Eq.refl k) (Eq.refl 0)
