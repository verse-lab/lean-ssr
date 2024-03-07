import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Basic
import Ssreflect.Elim
import Std.Tactic.Replace

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

declare_syntax_cat ssrRevert (behavior := symbol)
declare_syntax_cat ssrReverts
-- intros
syntax "(" term ")" : ssrRevert
-- syntax term : ssrRevert
syntax "[" term "]" : ssrRevert
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

namespace Revert
protected def kpatternType (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  if p.isFVar && occs == Occurrences.all then
    return e.abstract #[p] -- Easy case
  else
    let pHeadIdx := p.toHeadIndex
    let pNumArgs := p.headNumArgs
    let rec visit (e : Expr) (offset : Nat) : StateRefT stateVisit MetaM Unit := do
      -- dbg_trace s! "visit({e})"
      let visitChildren : Unit → StateRefT stateVisit MetaM Unit := fun _ => do
        match e with
        | .app f a         => visit f offset; visit a offset
        | .mdata _ b       => visit b offset
        | .proj _ _ b      => visit b offset
        | .letE _ t v b _  => visit t offset; visit v offset; visit b (offset+1)
        | .lam _ d b _     => visit d offset; visit b (offset+1)
        | .forallE _ d b _ => visit d offset; visit b (offset+1)
        | _                => return ()
      if e.hasLooseBVars then
        visitChildren ()
      else
        let eTy <- inferType e
        if eTy.toHeadIndex != pHeadIdx || eTy.headNumArgs != pNumArgs then
          visitChildren ()
        else
          -- We save the metavariable context here,
          -- so that it can be rolled back unless `occs.contains i`.
          let mctx ← getMCtx
          -- dbg_trace s! "AA: {<-inferType e}"
          if (← isDefEq eTy p) then
            let i := (← get).idx
            modify $ fun st => { st with idx := i+1 }
            if occs.contains i then
              modify $ fun st => { st with exps := st.exps.push e }
            else
              -- Revert the metavariable context,
              -- so that other matches are still possible.
              setMCtx mctx
              visitChildren ()
          else
            visitChildren ()
    let (_, e) <- visit e 0 |>.run {}
    if e.exps.size = 0 then
      throwError "Pattern was not found"
    else return e.exps[0]!
end Revert

elab t:tactic ":" is:ssrReverts : tactic => do
  let is' := is.raw[0].getArgs.reverse
  elabTactic $ mkNullNode is'
  elabTactic  t


elab_rules : tactic
  | `(ssrRevert|$i:ident) => do
      run  `(tactic| revert $i:term)
  | `(ssrRevert|($ts:term)) => do
      let t <- Term.elabTerm ts none
      try
        let t <- Revert.kpattern (<- getMainTarget) t
        if t.hasExprMVar then
          throwErrorAt ts "Term is not generalized enough"
        let x <- fresh "x"
        let h <- fresh "H"
        run `(tactic| generalize $h : $ts = $x)
        run `(tactic| clear $h; revert $x)
      catch | ex => do
        let t <- Term.elabTermAndSynthesize ts none
        let ty <- inferType t
        let id <- fresh "H"
        let goal <- (<-getMainGoal).assert id.getId ty t
        setGoals [goal]
      -- let t <- instantiateMVars t
  | `(ssrRevert| [ $t:term ]) => do
      let x <- fresh "x"
      let h <- fresh "H"
      let goalType <- getMainTarget
      let prop <- Term.elabTerm (<- `(term| Prop)) none
      let t <- Term.elabTerm t prop
      try
        let t <- Revert.kpattern goalType t
        let dt <- mkAppM `Decidable #[t]
        let t <- Revert.kpatternType goalType dt
        let ts <- PrettyPrinter.delab t
        run `(tactic| generalize $h : $ts = $x)
        run `(tactic| clear $h; revert $x)
        run `(tactic| try rewrite [iteIsTrue, iteIsFalse])
      catch
      | ex => do
        -- dbg_trace "revert failed: {<- ex.toMessageData.toString}"
        let dt <- mkAppM `Decidable #[t]
        let ts <- PrettyPrinter.delab dt
        run `(tactic| have $h : $ts := by infer_instance)
        run `(tactic| revert $h:ident)


elab_rules : tactic
  | `(ssrReverts| $[$ts]*) => elabTactic (annotate := fun _ => withTacticInfoContextR default) $ mkNullNode ts
-- set_option pp.all true

@[simp↓ high] theorem decIsTrue (h : p) : @decide _ (Decidable.isTrue h) = true := by rfl
@[simp↓ high] theorem decIsFalse (h : ¬ p) : @decide _ (Decidable.isFalse h) = false := by rfl
@[simp↓ high] theorem iteIsTrue [Decidable p] (t e : α) (h : p) : (@ite _ _ (Decidable.isTrue h) t e) = t := by rfl
@[simp↓ high] theorem iteIsFalse [Decidable p] (t e : α) (h : ¬ p) : (@ite _ _ (Decidable.isFalse h) t e) = e := by rfl


-- example (x y : List Nat) : if [] = y then True else false := by
--    skip: [x = y]
