import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Qq

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic
open Qq

-- Execute `x` using the main goal local context and instances -
-- This is necessary to make sure that the context is properly updated for future tactics.
-- This way the state is affected by the tactic for reading from the local context by the next tactic.
-- Place this at the start of extra tactic's do notation block.
-- For example:
-- ```
--   local elab "mytacticname" : tactic => newTactic do
--     let goal ← getGoalProp
--     ...
-- ```
def newTactic (x : TacticM α) : TacticM α :=
  withMainContext x

-- Check if the expression is a Prop and if so return it as a Q(Prop) that can be used in a pattern match.
private def castToProp (e: Lean.Expr) : TacticM (Option Q(Prop)) := do
  Qq.checkTypeQ (u := Lean.levelOne) e q(Prop)


-- getHypotheses returns the hypotheses as an array of tuples of (Hypothesis name, Q(Prop))
-- This way the hypothesis Q(Prop) can be used in a pattern match and
-- the name can be used to refer to the hypothesis in other tactics
def getHypotheses : TacticM (Array (Lean.Syntax.Ident × Q(Prop))) := do
  let mut res := #[]
  for localDecl in ← Lean.MonadLCtx.getLCtx do
    if let some typ ← castToProp localDecl.type then
      let name := Lean.mkIdent localDecl.userName
      res := res.push (name, typ)
  return res

-- run is shorthand for evalTactic (← t).
-- def run (t: TacticM (Lean.TSyntax `tactic)): TacticM Unit := do
--   let t' ← t
--   evalTactic t'

def run (t: TacticM (Lean.TSyntax `tactic)) (stx : Option Syntax := none): TacticM Unit := do
    try evalTactic (<- t)
    catch ex => throwErrorAt (stx.getD ex.getRef) ex.toMessageData

-- def tryRun (t: TacticM (Lean.TSyntax `tactic)): TacticM Unit := do
--   let t' ← t
--   let _ :: _ <-  getUnsolvedGoals | return ()
--   evalTactic t'

def tryGoal (t: TacticM Unit): TacticM Unit := do
  t <|> return ()

-- Returns the main goal as a Q(Prop), such that it can be used in a pattern match.
def getGoalProp : TacticM Q(Prop) := do
  let goal ← getMainTarget
  match ← castToProp goal with
  | some qType => return qType
  | none => throwError "goal is not a proposition"


-- Creates a fresh variable with the suggested name.
def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : Lean.Name) : m Lean.Syntax.Ident := do
  let name ← Lean.Meta.getUnusedUserName suggestion
  return Lean.mkIdent name

def allGoal [Inhabited α]
  (tac : TacticM α) (comb : List α -> α := fun _ => default)  : TacticM α := newTactic do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  let mut ans := []
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      let (ans', mvarIdsNew') <- withMainContext do
        let mut ans := ans
        let mut mvarIdsNew := mvarIdsNew
        try
          let a <- tac
          ans := a :: ans
          mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
        catch ex =>
          if (← read).recover then
            logException ex
            mvarIdsNew := mvarIdsNew.push mvarId
          else
            throw ex
        return (ans, mvarIdsNew)
      (ans, mvarIdsNew) := (ans', mvarIdsNew')
  setGoals mvarIdsNew.toList
  return comb ans


def range (n : Nat) := (List.iota n).reverse.map (fun x => x - 1)

partial def idxGoal [Inhabited α] (tacs : Nat -> TacticM α)
  (comb : List α -> α := fun _ => default) : TacticM α :=
  newTactic do
  let mut newGoals := #[]
  let mut ans := []
  let goals ← getUnsolvedGoals
  for i in range goals.length do
    let goal := goals[i]!
    setGoals [goal]
    ans := (<- tacs i) :: ans
    newGoals := newGoals ++ (<- getUnsolvedGoals)
  setGoals newGoals.toList
  return comb ans
