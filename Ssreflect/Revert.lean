import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Basic
import Std.Tactic.Replace

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

declare_syntax_cat ssrRevert
declare_syntax_cat ssrReverts
-- intros
syntax "(" term ")" : ssrRevert
syntax ident : ssrRevert
syntax (name:= ssrReverts) (ppSpace colGt (ssrRevert <|> ssrBasic))* : ssrReverts

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

elab_rules : tactic
  | `(ssrRevert|$i:ident) => do
      run  `(tactic| revert $i:term)
  | `(ssrRevert|($t:term)) => do
      let h <- fresh "H"
      let goal <- getMainGoal
      let goalTag <- goal.getTag
      let (trm, []) <- Tactic.elabTermWithHoles (allowNaturalHoles := true) t none goalTag
        | throwErrorAt t "Cannont infer implicit parameters of {t}"
      let goal <- goal.assert h.getId (<- inferType trm) trm
      setGoals $ goal :: (<- getUnsolvedGoals)

elab_rules : tactic
  | `(ssrReverts| $[$ts]*) => elabTactic (annotate := withTacticInfoContextR) $ mkNullNode ts

elab t:tactic ":" is:ssrReverts : tactic => do
  let is := is.raw[0].getArgs.reverse
  elabTactic (annotate := withTacticInfoContextR) $ mkNullNode is
  elabTactic t

-- example (x y : Nat) : True := by
--   skip: {y} x (@Eq.refl Nat x);
