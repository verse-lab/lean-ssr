import Lean
import Lean.Elab.Tactic
import Batteries.Lean.Meta.UnusedNames
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

def run (t: TacticM Syntax): TacticM Unit := newTactic do
    evalTactic (<- t)

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
      let mvarIds ← getUnsolvedGoals
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

-- abbrev ElabOne := Tactic -> Tactic

-- partial def iterateElabCore (elabOne : HashMap SyntaxNodeKind ElabOne) (afterMacro : Bool) (stx : Syntax) : TacticM Unit := do
--     let cats := keys elabOne
--     match <- stx.isSeqOfCategory cats with
--     | some stx => throwErrorAt stx "Unsupported syntax : {stx}"
--     | none =>
--       for stx in stx[0].getArgs do
--         let stx' := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
--         let afterMacro := afterMacro || (stx != stx')
--         match <- stx'.isSeqOfCategory cats, <- stx'.isOfCategories cats with
--         | _     , some n =>
--           let wR : _ -> TacticM Unit := if afterMacro then id else withRef stx'
--           allGoal $ wR $ elabOne[n].get! (iterateElabCore elabOne afterMacro) stx'
--         | none, none     => withRef stx do iterateElabCore elabOne afterMacro stx'
--         | _     , _      => dbg_trace s! "{stx'[0].getArgs}"; throwErrorAt stx' "Unsupported syntax2"

-- def iterateElab (elabOne : HashMap SyntaxNodeKind ElabOne) (stx : Syntax) : TacticM Unit :=
--   withRef stx do iterateElabCore elabOne false stx


partial def elabTactic (stx : Syntax)
  (annotate : Syntax ->TacticM Unit -> TacticM Unit := withTacticInfoContext)
  (toGoal : TacticM Unit -> TacticM Unit := allGoal) : TacticM Unit := do
  profileitM Exception "tactic execution" (decl := stx.getKind) (← getOptions) <|
  withRef stx <| withIncRecDepth <| withFreshMacroScope <| match stx with
    | .node _ k _    =>
      if k == nullKind then
        -- Macro writers create a sequence of tactics `t₁ ... tₙ` using `mkNullNode #[t₁, ..., tₙ]`
        stx.getArgs.forM (toGoal $ elabTactic · annotate)
      else withTraceNode `Elab.step (fun _ => return stx) do
        let evalFns := tacticElabAttribute.getEntries (← getEnv) stx.getKind
        let macros  := macroAttribute.getEntries (← getEnv) stx.getKind
        if evalFns.isEmpty && macros.isEmpty then
          throwErrorAt stx "tactic '{stx.getKind}' has not been implemented"
        let s ← Tactic.saveState
        expandEval s macros evalFns #[]
    | .missing => pure ()
    | _ => throwError m!"unexpected tactic{indentD stx}"
where
    throwExs (failures : Array EvalTacticFailure) : TacticM Unit := do
     if let some fail := failures[0]? then
       -- Recall that `failures[0]` is the highest priority evalFn/macro
       fail.state.restore (restoreInfo := true)
       throw fail.exception -- (*)
     else
       throwErrorAt stx "unexpected syntax {indentD stx}"

    @[inline] handleEx (s : Tactic.SavedState) (failures : Array EvalTacticFailure) (ex : Exception) (k : Array EvalTacticFailure → TacticM Unit) := do
      match ex with
      | .error .. =>
        trace[Elab.tactic.backtrack] ex.toMessageData
        let failures := failures.push ⟨ex, ← Tactic.saveState⟩
        s.restore (restoreInfo := true); k failures
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then
          -- We do not store `unsupportedSyntaxExceptionId`, see throwExs
          s.restore (restoreInfo := true); k failures
        else if id == abortTacticExceptionId then
          for msg in (← Core.getMessageLog).toList do
            trace[Elab.tactic.backtrack] msg.data
          let failures := failures.push ⟨ex, ← Tactic.saveState⟩
          s.restore (restoreInfo := true); k failures
        else
          throw ex -- (*)

    expandEval (s : Tactic.SavedState) (macros : List _) (evalFns : List _) (failures : Array EvalTacticFailure) : TacticM Unit :=
      match macros with
      | [] => eval s evalFns failures
      | m :: ms =>
        try
          withReader ({ · with elaborator := m.declName }) do
            annotate stx do
              let stx' ← adaptMacro m.value stx
              (elabTactic stx' annotate)
        catch ex => handleEx s failures ex (expandEval s ms evalFns)

    eval (s : Tactic.SavedState) (evalFns : List _) (failures : Array EvalTacticFailure) : TacticM Unit := do
      match evalFns with
      | []              => throwExs failures
      | evalFn::evalFns => do
        try
          withReader ({ · with elaborator := evalFn.declName }) <| annotate stx <| evalFn.value stx
        catch ex => handleEx s failures ex (eval s evalFns)

def _root_.Lean.EnvExtension.set [Inhabited σ] (ext : EnvExtension σ) (s : σ) : MetaM Unit := do
  Lean.setEnv $ ext.setState (<- getEnv) s

def _root_.Lean.EnvExtension.modify [Inhabited σ] (ext : EnvExtension σ) (s : σ -> σ) : MetaM Unit := do
  Lean.modifyEnv (ext.modifyState · s)

def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ) : MetaM σ := do
  return ext.getState (<- getEnv)

initialize
  registerTraceClass `reflect

initialize
  registerTraceClass `reflect_names

-- structure stateVisit where
--   idx : Nat := 1
--   exps : Array Expr := #[]

-- #check kabstract

-- def kreplace (e : Expr) (p : Expr -> MetaM Bool) (pr : Expr -> Expr) (occs : Occurrences := .all) : MetaM Expr := do
--   let e ← instantiateMVars e
--   let rec visit (e : Expr) (offset : Nat) : StateRefT Nat MetaM Expr := do
--     let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
--       match e with
--       | .app f a         => return e.updateApp! (← visit f offset) (← visit a offset)
--       | .mdata _ b       => return e.updateMData! (← visit b offset)
--       | .proj _ _ b      => return e.updateProj! (← visit b offset)
--       | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
--       | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
--       | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
--       | e                => return e
--       -- We save the metavariable context here,
--       -- so that it can be rolled back unless `occs.contains i`.
--     let mctx ← getMCtx
--     if <- p e then
--       let i ← get
--       set (i+1)
--       if occs.contains i then
--         return pr e
--       else
--         -- Revert the metavariable context,
--         -- so that other matches are still possible.
--         setMCtx mctx
--         visitChildren ()
--     else
--       visitChildren ()
--   visit e 0 |>.run' 1

-- inductive Dir where
--   | P2B
--   | B2P

-- @[inline] abbrev PB : Dir -> Type
--   | .P2B => Prop
--   | .B2P => Bool

-- @[inline] abbrev PB' : Dir -> Type
--   | .P2B => Bool
--   | .B2P => Prop

-- @[simp] def equiv : (d : Dir) -> PB d -> PB' d -> Prop
--   | .P2B, P, b => P <-> b
--   | .B2P, b, P => P <-> b

-- class ReflectD (d : Dir) (P : PB d) (B : outParam (PB' d)) where
--   eqv : equiv d P B

-- @[inline] abbrev mkPB : (d : Dir) -> (P : Prop) -> (b : Bool) -> PB d
--   | .P2B, P, _ => P
--   | .B2P, _, b => b

-- @[inline] abbrev mkPB' : (d : Dir) -> (P : Prop) -> (b : Bool) -> PB' d
--   | .B2P, P, _ => P
--   | .P2B, _, b => b


-- @[inline] abbrev Reflect d (P : Prop) (b : Bool) := ReflectD d (mkPB d P b) (mkPB' d P b)

-- @[inline] abbrev Reflect.toProp (b : Bool) {P : Prop} [ReflectD .B2P b P] : Prop := P

-- class Reflect (P : outParam Prop) (b : outParam Bool) where
--   pb : ReflectD .P2B P b
--   bp : ReflectD .B2P b P

-- instance [Reflect P b] : ReflectD .P2B P b := by sorry
-- instance [Reflect P b] : ReflectD .B2P b P := by sorry

-- theorem toPropEq (eq : b1 = b2) [inst1:ReflectD .B2P b1 P1] [inst2:ReflectD .B2P b2 P2] : Reflect.toProp b1 = Reflect.toProp b2 := by
--   simp [Reflect.toProp]
--   cases inst1 <;> cases inst2 <;> simp_all

-- def ReflectEven d (n : Nat) : Reflect d (even n) (evenb n) := by sorry

-- #check Parser.Term.byTactic

-- elab "reflect : " tp:term t:declVal : command => liftTermElabM <| do
--   let tp <- elabTerm tp none
--   let exp <- elabByTactic t tp

-- reflect : forall n,  Reflect (even n) (evenb n) := by
--   intro _


-- instance  : forall n, ReflectD .P2B (even n) (evenb n) := ReflectEven .P2B
-- instance  : forall n, ReflectD .B2P (evenb n) (even n) := ReflectEven .B2P
-- instance ReflectTrue : Reflect d True true := by sorry
-- instance ReflectFalse : Reflect d False false := by sorry
-- instance ReflectAnd : [Reflect d P1 b1] -> [Reflect d P2 b2] -> Reflect d (P1 /\ P2) (b1 && b2) := by sorry

-- #reduce Reflect.toProp (evenb 3)

-- elab "#reflect" ib:ident : command => do
--   liftTermElabM <| generatePropSimp ib.getId

-- #reflect evenb


-- @[inline_if_reduce, nospecialize] def reflect (P : Prop) {b : Bool} [Reflect P b] : Bool := b

-- @[simp] theorem reflectE (P : Prop) {b : Bool} [Reflect P b] : b = reflect P := by rfl
-- theorem reflectI (P : Prop) {b : Bool} [inst: Reflect P b] : P = b := by
--   cases inst <;> simp_all

-- instance (n : Nat) : Reflect (even n) (evenb n) := by
--   sorry

-- example : even (n + 2) := by simp

-- #print_eqs even evenb

-- #print evenb._eq_1





  -- rw (config := { occs := .pos [2] }) [<-(@decide_eq_true_eq (even ..))]






-- example P : even 0 /\ P -> False := by
--   simp [even.zero]

-- partial def iterateElab0 (elabOne : HashMap SyntaxNodeKind Tactic) (stx : Syntax) : TacticM Unit := do
--   let cats := keys elabOne
--   match <- stx.isSeqOfCategory cats with
--   | some stx => throwErrorAt stx "Unsupported syntax1"
--   | none =>
--     for stx in stx[0].getArgs do
--     match <- stx.isOfCategories cats with
--     | some n => allGoal $ elabOne[n].get! stx
--     | _ => throwErrorAt stx "Unsupported syntax2"

-- partial def iterateElab1 (elabOne : HashMap SyntaxNodeKind Tactic) (stx : Syntax) : TacticM Unit := do
--   let cats := keys elabOne
--   match <- stx.isSeqOfCategory cats with
--   | some stx => throwErrorAt stx "Unsupported syntax1"
--   | none =>
--     for stx in stx[0].getArgs do
--       let stx := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
--       match <- stx.isSeqOfCategory cats, <- stx.isOfCategories cats with
--       | _     , some n => allGoal $ elabOne[n].get! stx
--       | none, none     => iterateElab1 elabOne stx
--       | _     , _      => throwErrorAt stx "Unsupported syntax2"

-- partial def iterateElab2 (elabOne : HashMap SyntaxNodeKind ElabOne) (stx : Syntax) : TacticM Unit := do
--   let cats := keys elabOne
--   match <- stx.isSeqOfCategory cats with
--   | some stx => throwErrorAt stx "Unsupported syntax1"
--   | none =>
--     for stx in stx[0].getArgs do
--       let stx := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
--       match <- stx.isSeqOfCategory cats, <- stx.isOfCategories cats with
--       | _     , some n => allGoal $ elabOne[n].get! (iterateElab2 elabOne) stx
--       | none, none     => iterateElab2 elabOne stx
--       | _     , _      => throwErrorAt stx "Unsupported syntax2"
