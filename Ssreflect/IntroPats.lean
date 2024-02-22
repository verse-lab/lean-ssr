import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Elim
import Ssreflect.ApplyIn
import Ssreflect.Move
import Ssreflect.Done

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

private partial def intro1PStep : TacticM Unit :=
  liftMetaTactic fun goal ↦ do
    let (_, goal) ← goal.intro1P
    pure [goal]
private partial def introsDep : TacticM Unit := do
  let t ← getMainTarget
  match t with
  | Expr.forallE _ _ e _ =>
    if e.hasLooseBVars then
      intro1PStep
      introsDep
  | _ => pure ()

declare_syntax_cat ssrIntro
syntax ssrIntros := (ppSpace colGt (ssrIntro <|> ssrTriv))*
-- intros
syntax ident : ssrIntro
syntax "?" : ssrIntro
syntax "*" : ssrIntro
syntax ">" : ssrIntro
syntax "_" : ssrIntro

-- rewrites
syntax "->" : ssrIntro
syntax "<-" : ssrIntro

-- switches
syntax "/(" term ")" : ssrIntro
syntax "/" ident : ssrIntro
syntax "/(_" term ")" : ssrIntro

-- automations
-- syntax "//" : ssrIntro
-- syntax "/==" : ssrIntro
-- syntax "/=" : ssrIntro
-- syntax "//="  : ssrIntro
-- syntax "//=="  : ssrIntro

-- destructs
syntax "[ ]" : ssrIntro
syntax "[" sepBy1(ssrIntros, "|") "]" : ssrIntro

-- top hyps manipulations
syntax "/[swap]" : ssrIntro
syntax "/[apply]" : ssrIntro
syntax "/[dup]" : ssrIntro

-- clears
syntax "{" (ppSpace colGt term:max)+ "}" : ssrIntro
syntax "{}" ident : ssrIntro

-- tactics
syntax "/[tac " tactic "]" : ssrIntro




partial def elabSsr : Tactic := fun stx => newTactic do
    let stx := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
    match stx with
    -- intros
    | `(ssrIntro|$i:ident) => newTactic do
        run (stx := stx) `(tactic| intro $i:ident)
    | `(ssrIntro| ?) => newTactic do run (stx:=stx) `(tactic| intro _)
    | `(ssrIntro| *) => newTactic do run (stx:=stx) `(tactic| intros)
    | `(ssrIntro| >) => newTactic do introsDep
    | `(ssrIntro| _) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| clear $name)

    -- rewrites
    | `(ssrIntro| ->) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| rw [$name:ident])
      tryGoal $ run (stx:=stx) `(tactic| clear $name)
    | `(ssrIntro| <-) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| rw [<-$name:ident])
      tryGoal $ run (stx:=stx) `(tactic| clear $name)

    -- switches
    | `(ssrIntro|/$t:ident)
    | `(ssrIntro|/($t:term)) => newTactic do
      let name <- fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=t) `(tactic| apply $t:term in $name)
    | `(ssrIntro|/(_ $t:term)) => newTactic do
      let name <- fresh "N"
      let h <- fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| have $h := $t)
      run (stx:=t) `(tactic| apply $name:term in $h)
      tryGoal $ run (stx:=stx) `(tactic| clear $name)
      tryGoal $ run (stx:=stx) `(tactic| clear $h)


    -- automations
    -- | `(ssrIntro| //) => newTactic do run (stx:=stx) `(tactic| ssr_triv )
    -- | `(ssrIntro| /=) => newTactic do run (stx:=stx) `(tactic| try dsimp)
    -- | `(ssrIntro| /==) => newTactic do run (stx:=stx) `(tactic| try simp)
    -- | `(ssrIntro| //=) => newTactic do run (stx:=stx) `(tactic| try dsimp; ssr_triv )
    -- | `(ssrIntro| //==) => newTactic do run (stx:=stx) `(tactic| try simp; ssr_triv )

    -- destructs
    | `(ssrIntro| []) => newTactic do run (stx:=stx) `(tactic| scase)
    | `(ssrIntro| [ $[$is:ssrIntros]|* ] ) => do
      if (← getUnsolvedGoals).length == 1 then
        run (stx:=stx) `(tactic|scase)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        run (stx := stx) `(tactic| fail "Given { is.size } tactics, but excpected { goals.length }")
      else
        idxGoal fun i => many is[i]!

    -- top hyps manipulations
    | `(ssrIntro|/[swap]) => newTactic do
      let forallE n1 _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      run (stx:=stx) `(tactic| intros $(mkIdent n1))
      let forallE n2 _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      run (stx:=stx) `(tactic| intros $(mkIdent n2))
      run (stx:=stx) `(tactic| revert $(mkIdent n1))
      run (stx:=stx) `(tactic| revert $(mkIdent n2))
    | `(ssrIntro|/[dup]) => newTactic do
      let forallE n _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      run (stx:=stx) `(tactic| intros $(mkIdent n))
      let n' <- fresh (n ++ "0")
      run (stx:=stx) `(tactic| have $n' := $(mkIdent n))
      run (stx:=stx) `(tactic| revert $(mkIdent n))
      run (stx:=stx) `(tactic| revert $n')
    | `(ssrIntro|/[apply]) => newTactic do
      let forallE n1 _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      let n1 := mkIdent n1
      run (stx:=stx) `(tactic| intros $n1)
      let forallE n2 _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      let n2 := mkIdent n2
      run (stx:=stx) `(tactic| intros $n2)
      run (stx:=stx) `(tactic| apply $n1 in $n2)
      run (stx:=stx) `(tactic| clear $n1)

    -- clears
    | `(ssrIntro| { $ts:term* }) => newTactic do
      run (stx:=stx) `(tactic| clear $ts*)
    | `(ssrIntro| {}$i:ident ) => newTactic do
      run (stx:=stx) `(tactic| clear $i)
      run (stx:=stx) `(tactic| intros $i)

    -- tactics
    | `(ssrIntro| /[tac $t:tactic]) => newTactic do
      run (stx:=stx) `(tactic| $t)
    | _ => throwErrorAt stx "Unknown action"
  where
    many (stx : TSyntax `ssrIntros) : TacticM Unit :=
    match stx with
    | `(ssrIntros| $[$is:ssrIntro] *) => newTactic do
      for i in is do allGoal $ elabSsr i
    | _ => throwErrorAt stx "Unknown action"

def isize : TSyntax `ssrIntros -> MetaM Nat
   | `(ssrIntros| $[$is:ssrIntro] *) => return is.size
   | _ => throwError "unsupported syntax"

elab t:tactic "=> " i:ssrIntro is:ssrIntros : tactic => do
  run `(tactic|$t);
  (match i with
  | `(ssrIntro| [] ) => allGoal $ elabSsr i
  | `(ssrIntro| [ $[$is:ssrIntros]|* ] ) => elabSsr i
  | _ => allGoal $ elabSsr i);
  if (<- getUnsolvedGoals).length = 0 && (<-  isize is) = 0 then
    return ()
  else elabSsr.many is

-- syntax (name:= sby) "sby " tacticSeq : tactic

-- @[tactic sby] def elabSby : Tactic
--   | `(tactic| sby%$sby $ts) => do
--     evalTactic ts
--     unless (<- getUnsolvedGoals).length = 0 do
--       tryGoal $ allGoal $ run `(tactic| solve | move=> // | moveR=> // | skip=> //  )
--     unless (<- getUnsolvedGoals).length = 0 do
--       throwErrorAt sby "No applicable tactic"
--   | _ => throwError "Unsupported index for sby"
