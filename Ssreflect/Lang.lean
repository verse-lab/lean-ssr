
import Mathlib
import Aesop
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
  let mvarIds ← getUnsolvedGoals
  let mut mvarIdsNew := #[]
  let mut ans := []
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        ans := (<- tac) :: ans
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList
  return (comb ans)

local elab "scase" : tactic => newTactic do
    let hyps <- getLCtx
    let name <- fresh "H"
    run `(tactic| intro $name:ident)
    run `(tactic| unhygienic cases $name:ident)
    allGoal do
      let hypsNew <- getLCtx
      for hyp in hypsNew do
        unless hyps.contains hyp.fvarId do
          run `(tactic| try revert $(mkIdent hyp.userName):ident)

partial def intro1PStep : TacticM Unit :=
  liftMetaTactic fun goal ↦ do
    let (_, goal) ← goal.intro1P
    pure [goal]
partial def introsDep : TacticM Unit := do
  let t ← getMainTarget
  match t with
  | Expr.forallE _ _ e _ =>
    if e.hasLooseBVars then
      intro1PStep
      introsDep
  | _ => pure ()

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
  return (comb ans)

declare_syntax_cat ssr_intros
declare_syntax_cat ssr_intro
syntax ident : ssr_intro
syntax "->" : ssr_intro
syntax "/[" term "]" : ssr_intro
syntax "<-" : ssr_intro
syntax "?" : ssr_intro
syntax "*" : ssr_intro
syntax ">" : ssr_intro
syntax "{}" : ssr_intro
syntax "_" : ssr_intro
syntax "//" : ssr_intro
syntax "/="  : ssr_intro
syntax "//="  : ssr_intro
syntax "\\" : ssr_intro
syntax "{" sepBy1(ssr_intros, "|") "}" : ssr_intro

-- syntax ssr_intros ppSpace ssr_intro : ssr_intros
syntax (ppSpace colGt ssr_intro)* : ssr_intros

-- macro_rules
--   | `(ssr_intros| { $[$is:ssr_intros]|* } $isr:ssr_intro ) => do
--     let isr := #[isr];
--     `(ssr_intros|{ $[$is $isr]|* })

def etaExpandBounded (e : Expr) (n : Nat) : MetaM Expr :=
  withDefault do forallBoundedTelescope (← inferType e) n fun xs _ => mkLambdaFVars xs (mkAppN e xs)

def argNum (eApp : Expr) (eArg : Expr) : MetaM Nat := do
  forallTelescopeReducing eApp fun eArgs _ => do
    let _ := etaExpand eApp
    let mut i : Nat := 0
    for e in eArgs do
      if (<- isDefEq (<- inferType e) eArg) then
        break
      i := i + 1
    return i

def applyInLD (t : Expr) (ld : LocalDecl) : TacticM Unit := do
  let n <- argNum (<- inferType t) ld.type
  dbg_trace s! "num: {n} "
  let t <- etaExpandBounded t n
  dbg_trace s! "term: {t} "
  dbg_trace s! "name: {ld.type} "
  let t <- lambdaTelescope t fun xs t =>
    mkLambdaFVars xs $ mkApp t ld.toExpr
  -- let t <- t.applyFVarSubst
  dbg_trace s! "term2: {t} "
  let mvarId <- getMainGoal
  dbg_trace s! "term3: { <- inferType t }"
  -- let t <- t.isE
  let mId <- mvarId.assert (<- getUnusedUserName "H") (<- inferType t) t
  replaceMainGoal [mId]
  -- mkForallFVars

def applyIn (stx : Syntax) (ldecl : LocalDecl) : TacticM Expr := do
  let t <- withNewMCtxDepth (allowLevelAssignments := true) do
    let f ← elabTermForApply stx
    let (mvs, bis, tp) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
    for (m, b) in mvs.zip bis do
      if b.isInstImplicit && !(← m.mvarId!.isAssigned) then
        try m.mvarId!.inferInstance
        catch _ => continue
    let t <- mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map fun e => some e)
    return (<- abstractMVars t).expr
  return t




partial def elabSsr (stx :  TSyntax `ssr_intro) : TacticM Unit := withTacticInfoContext stx $ newTactic do
    match stx with
    | `(ssr_intro|$i:ident) => newTactic do
        run (stx := stx) `(tactic| intro $i:ident)
    | `(ssr_intro|/[$t:term] ) => newTactic do
      -- let t <- Tactic.elabTerm t none
      let name <- fresh "H"
      run (stx:=stx) `(tactic| intros $name:ident)
      allGoal $ for i in (<- getLCtx)do
        if i.userName == name.getId then
          let t <- applyIn t i
          let mvarId <- getMainGoal
          let mId <- mvarId.assert (<- getUnusedUserName "H") (<- inferType t) t
          replaceMainGoal [mId]
      run (stx:=stx) `(tactic| clear $name:ident)
    | `(ssr_intro| ->) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intro $name:ident)
      run (stx:=stx) `(tactic| rw [$name:ident])
      tryGoal $ run (stx:=stx) `(tactic| clear $name:ident)
    | `(ssr_intro| <-) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intro $name:ident)
      run (stx:=stx) `(tactic| rw [<-$name:ident])
      tryGoal $ run (stx:=stx) `(tactic| clear $name:ident)
    | `(ssr_intro| ?) => newTactic do run (stx:=stx) `(tactic| intro _)
    | `(ssr_intro| *) => newTactic do run (stx:=stx) `(tactic| intros)
    | `(ssr_intro| >) => newTactic do introsDep
    | `(ssr_intro| _) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intro $name:ident)
      run (stx:=stx) `(tactic| clear $name:ident)
    | `(ssr_intro| {}) => newTactic do run (stx:=stx) `(tactic| scase)
    | `(ssr_intro| //) => newTactic do run (stx:=stx) `(tactic| try (intros; aesop) )
    | `(ssr_intro| /=) => newTactic do run (stx:=stx) `(tactic| try simp )
    | `(ssr_intro| //=) => newTactic do run (stx:=stx) `(tactic| try simp; try aesop )
    | `(ssr_intro| \) => newTactic do run (stx:=stx) `(tactic| fail "Goal at this point is:" )
    | `(ssr_intro| { $[$is:ssr_intros]|* } ) => do
      if (← getUnsolvedGoals).length == 1 then
        run (stx:=stx) `(tactic|scase)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        throwErrorAt stx s!"Given { is.size } tactics, but excpected { goals.length }"
      else
        idxGoal fun i => many is[i]!
    | _ => throwErrorAt stx "Unknown action"
  where
    many (stx : TSyntax `ssr_intros) : TacticM Unit :=
    match stx with
    | `(ssr_intros| $[$is:ssr_intro] *) => newTactic do
      for i in is do allGoal $ elabSsr i
    | _ => throwErrorAt stx "Unknown action"


elab t:tactic "=>" i:ssr_intro is:ssr_intros : tactic => do
  run `(tactic|$t); elabSsr i; elabSsr.many is

inductive foo : Int -> Type where
  | a (b : Bool) (eq : b = b) (x : Int) (eqq : if b then x > 0 else x < 0)
    (i : Int) : foo i
  | b (b : Bool) : foo 5

axiom bar : forall n : Nat, n = 0 -> n = n -> n = 6

theorem bazz : Int -> 5 = 5 -> ∀ f : foo 5, ∀ g : foo 5, f = g -> g = f := by
  skip=> _ /[bar]
  -- specialize
  -- skip=> _ /[bar] --{ { > | * } // | ?? -> }
