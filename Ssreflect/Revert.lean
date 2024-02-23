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

def elabSsrR : Tactic := fun stx =>do
  withTacticInfoContextR (<- getRef) do
  newTactic do
    match stx with
    | `(ssrRevert|$i:ident) => newTactic do
        run  `(tactic| revert $i:ident)
    | `(ssrRevert|($t:term)) => newTactic do
        let h <- fresh "H"
        run  `(tactic| have $h := $t)
        run  `(tactic| revert $h)
        tryGoal $ run  `(tactic| clear $h)
    | _ => throwErrorAt stx "Unknown action"

elab t:tactic ":" is:ssrReverts : tactic => do
  let is := mkNullNode is.raw[0].getArgs.reverse
  let is := mkNode `ssrReverts #[is]
  iterateElab (HashMap.ofList [
    (`ssrRevert, fun _ => elabSsrR),
    (`ssrBasic, fun _ stx => do
      withTacticInfoContextR (<- getRef) $ elabBasic stx)
  ]) is; run `(tactic|$t);


-- example (k m : Int) (eq : k = k) : k = k := by
--   skip: {m} k (Eq.refl k)
