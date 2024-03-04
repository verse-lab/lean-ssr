import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Elim
import Ssreflect.ApplyIn
import Ssreflect.Done
import Ssreflect.Basic

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
declare_syntax_cat ssrIntros
syntax (name := ssrIntros) (ppSpace colGt (ssrIntro <|> ssrTriv <|> ssrBasic))* : ssrIntros
-- intros
syntax ident : ssrIntro
syntax "?" : ssrIntro
syntax "!" : ssrIntro
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

-- destructs
syntax "[ ]" : ssrIntro
syntax "[" sepBy1(ssrIntros, "|") "]" : ssrIntro

-- top hyps manipulations
syntax "/[swap]" : ssrIntro
syntax "/[apply]" : ssrIntro
syntax "/[dup]" : ssrIntro

-- clears
syntax "{}" ident : ssrIntro

elab_rules : tactic
    | `(ssrIntro|$i:ident) => run `(tactic| intro $i:ident)
    | `(ssrIntro| ?) => run `(tactic| intro _)
    | `(ssrIntro| !) => run `(tactic| apply funext)
    | `(ssrIntro| *) => run `(tactic| intros)
    | `(ssrIntro| >) => introsDep
    | `(ssrIntro| _) => do
      let name ← fresh "H"
      evalTactic $ <- `(tactic| intros $name)
      evalTactic $ <- `(tactic| clear $name)

    -- rewrites
    | `(ssrIntro| ->) => do
      let name ← fresh "H"
      run `(tactic| intros $name)
      run `(tactic| first | rw [$name:ident] | fail "rewrite failed")
      run `(tactic| try clear $name)
    | `(ssrIntro| <-) => newTactic do
      let name ← fresh "H"
      run `(tactic| intros $name)
      run `(tactic| first | rw [<-$name:ident] | fail "rewrite failed")
      run `(tactic| try clear $name)

    -- -- switches
    | `(ssrIntro|/$t:ident) => do
      let name <- fresh "H"
      run `(tactic| intros $name)
      run `(tactic| apply $t:term in $name)
    | `(ssrIntro|/($t:term)) => do
      let name <- fresh "H"
      run  `(tactic| intros $name)
      run `(tactic| apply $t:term in $name)
    | `(ssrIntro|/(_ $t:term)) => do
      let name <- fresh "N"
      let h <- fresh "H"
      run `(tactic| intros $name)
      run `(tactic| have $h := $t)
      run `(tactic| apply $name:term in $h)
      run `(tactic| try clear $name)
      run `(tactic| try clear $h)

    -- destructs
    | `(ssrIntro| []) => run `(tactic| scase)
    | `(ssrIntro| [$[$is:ssrIntros]|* ] ) => do
      if (← getUnsolvedGoals).length == 1 then run `(tactic|scase)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
        let s <- `(ssrIntro| [$[$is:ssrIntros]|* ] )
        throwErrorAt s "Given { is.size } tactics, but excpected { goals.length }\n{goalsMsg}"
      else
         idxGoal fun i => newTactic $ elabTactic $ is[i]!.raw[0]

    -- -- top hyps manipulations
    | `(ssrIntro|/[swap]) => newTactic do
      let forallE n1 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      run  `(tactic| intros $(mkIdent n1))
      let forallE n2 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      run  `(tactic| intros $(mkIdent n2))
      run  `(tactic| revert $(mkIdent n1))
      run  `(tactic| revert $(mkIdent n2))
    | `(ssrIntro|/[dup]) => newTactic do
      let forallE n _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      run  `(tactic| intros $(mkIdent n))
      let n' <- fresh (n ++ "0")
      run  `(tactic| have $n' := $(mkIdent n))
      run  `(tactic| revert $(mkIdent n))
      run  `(tactic| revert $n')
    | `(ssrIntro|/[apply]) => newTactic do
      let forallE n1 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      let n1 := mkIdent n1
      run  `(tactic| intros $n1)
      let forallE n2 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      let n2 := mkIdent n2
      run `(tactic| intros $n2)
      run `(tactic| apply $n1 in $n2)
      run `(tactic| clear $n1)

elab_rules : tactic
  | `(ssrIntros| $[$ts]*) => elabTactic $ mkNullNode ts

syntax ssrIntro' := ssrIntro <|> ssrBasic <|> ssrTriv
elab t:tactic arr:"=> " i:ssrIntro' is:ssrIntros : tactic => do
  evalTactic  t
  match i with
  | `(ssrIntro'| []) =>
    withTacticInfoContext arr do
      elabTactic $ mkNullNode $ #[i.raw[0]] ++ is.raw[0].getArgs
  | `(ssrIntro'| [ $_:ssrIntros|* ]) =>
    withTacticInfoContext arr do
      elabTactic i.raw[0]
      elabTactic is.raw[0]
  | _ =>
    withTacticInfoContext arr do
      elabTactic $ mkNullNode $ #[i.raw[0]] ++ is.raw[0].getArgs


elab_rules : tactic
   | `(ssrIntro| {}%$brs $i:ident) => do
    try run `(tactic| clear $i)
    catch | ex => throwErrorAt brs ex.toMessageData
    try run `(tactic| intros $i:ident)
    catch | ex => throwErrorAt i ex.toMessageData


-- example : True \/ True -> True -> True /\ True -> True := by
--   scase=> [ [a] [] {}a  | * ] //=
