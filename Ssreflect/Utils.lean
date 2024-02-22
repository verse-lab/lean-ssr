import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
-- import Qq

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic
-- open Qq

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


-- Creates a fresh variable with the suggested name.
def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : Lean.Name) : m Lean.Syntax.Ident := do
  let name ← Lean.Meta.getUnusedUserName suggestion
  return Lean.mkIdent name

def allGoal [Inhabited α]
  (tac : TacticM α) (comb : List α -> α := fun _ => default)  : TacticM α := do
  if (<- getUnsolvedGoals).length == 0 then
    tac
  else
    newTactic do
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

def keys [BEq α] [Hashable α] (m : HashMap α β) : List α :=
  m.fold (fun ks k _ => k :: ks) []


def _root_.Lean.Syntax.isSeqOfKinds (stx : Syntax) (ks: List SyntaxNodeKind) : Option Syntax :=
  stx[0].getArgs.find? fun s => ¬ ks.any (s.isOfKind ·)

def _root_.Lean.Syntax.isOfKinds (stx : Syntax) (ks: List SyntaxNodeKind) : Option SyntaxNodeKind :=
  ks.find? (stx.isOfKind ·)


def _root_.Lean.Syntax.isOfCategory (stx : Syntax) (cat : Name) : MetaM Bool := do
  let env <- getEnv
  let cats := (Lean.Parser.parserExtension.getState env).categories
  let some cat := Parser.getCategory cats cat | throwError s!"unknown parser category '{cat}'"
  return cat.kinds.toList.any (stx.isOfKind ·.1)

def _root_.Lean.Syntax.isOfCategories (stx : Syntax) (cats : List Name) : MetaM $ Option Name := do
  cats.findM? stx.isOfCategory

def _root_.Lean.Syntax.isSeqOfCategory (stx : Syntax) (cats: List Name) : MetaM $ Option Syntax :=
  stx[0].getArgs.findM? fun s => return not (<- cats.anyM (s.isOfCategory ·))

abbrev ElabOne := Tactic -> Tactic

partial def iterateElabCore (elabOne : HashMap SyntaxNodeKind ElabOne) (afterMacro : Bool) (stx : Syntax) : TacticM Unit := do
  -- dbg_trace s! "{afterMacro}"
    let ks := keys elabOne
    match <- stx.isSeqOfCategory ks with
    | some stx => throwErrorAt stx "Unsupported syntax1"
    | none =>
      for stx in stx[0].getArgs do
        let stx' := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
        let afterMacro := afterMacro || (stx != stx')
        match <- stx'.isSeqOfCategory ks, <- stx'.isOfCategories ks with
        | _     , some n =>
          let wR : _ -> TacticM Unit := if afterMacro then id else withRef stx'
          allGoal $ wR $ elabOne[n].get! (iterateElabCore elabOne afterMacro) stx'
        | none, none     => withRef stx do iterateElabCore elabOne afterMacro stx'
        | _     , _      => dbg_trace s! "{stx'[0].getArgs}"; throwErrorAt stx' "Unsupported syntax2"

def iterateElab (elabOne : HashMap SyntaxNodeKind ElabOne) (stx : Syntax) : TacticM Unit :=
  withRef stx do iterateElabCore elabOne false stx


-- partial def iterateElab (elabOne : HashMap SyntaxNodeKind ElabOne) (stx : Syntax) : TacticM Unit := do
--   let ks := keys elabOne
--   match <- stx.isSeqOfCategory ks with
--   | some stx => throwErrorAt stx "Unsupported syntax1"
--   | none =>
--     for stx in stx[0].getArgs do
--       let stx := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
--       match <- stx.isSeqOfCategory ks, <- stx.isOfCategories ks with
--       | _     , some n => allGoal $ withTacticInfoContext stx $ elabOne[n].get! (iterateElab elabOne) stx
--       | none, none     => iterateElab elabOne stx
--       | _     , _      => dbg_trace s! "{stx[0].getArgs}"; throwErrorAt stx "Unsupported syntax2"
