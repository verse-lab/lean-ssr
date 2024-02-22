import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Basic

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

declare_syntax_cat ssrRevert
-- intros
syntax ident : ssrRevert
syntax "(" term ")" : ssrRevert

syntax ssrReverts := (ppSpace colGt (ssrRevert <|> ssrBasic))*

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

def elabSsrR : Tactic := fun stx =>
  newTactic do
    match stx with
    | `(ssrRevert|$i:ident) => newTactic do
        run (stx := stx) `(tactic| revert $i:ident)
    | `(ssrRevert|($t:term)) => newTactic do
        let h <- fresh "H"
        run (stx := stx) `(tactic| have $h := $t)
        run (stx := stx) `(tactic| revert $h)
        tryGoal $ run (stx := stx) `(tactic| clear $h)
    | _ => throwErrorAt stx "Unknown action"

elab t:tactic ":" is:ssrReverts : tactic => do
  let is := mkNullNode is.raw[0].getArgs.reverse
  let is := mkNode `ssrReverts #[is]
  iterateElab (HashMap.ofList [
    (`ssrRevert, fun _ => elabSsrR),
    (`ssrBasic, fun _ => elabBasic)
  ]) is; run `(tactic|$t);


-- example (k m : Int) : Int := by
--   skip: k (Eq.refl k)
