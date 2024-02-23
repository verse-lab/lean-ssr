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
syntax ssrIntros := (ppSpace colGt (ssrIntro <|> ssrTriv <|> ssrBasic))*
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

-- destructs
syntax "[ ]" : ssrIntro
syntax "[" sepBy1(ssrIntros, "|") "]" : ssrIntro
syntax "![" sepBy1(ssrIntros, "|") "]" : ssrIntro

-- top hyps manipulations
syntax "/[swap]" : ssrIntro
syntax "/[apply]" : ssrIntro
syntax "/[dup]" : ssrIntro

-- clears
syntax "{}" ident : ssrIntro

-- tactics

macro_rules |
  `(ssrIntro| {} $i:ident) => `(ssrIntros| {$i} $i:ident)

partial def elabSsr (elabIterate : Tactic) : Tactic := fun stx => do
   withTacticInfoContext (<- getRef) do
   newTactic do
    let stx := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
    match stx with
    -- intros
    | `(ssrIntro|$i:ident) => newTactic do
        run `(tactic| intro $i:ident)
    | `(ssrIntro| ?) => newTactic do run  `(tactic| intro _)
    | `(ssrIntro| *) => newTactic do run  `(tactic| intros)
    | `(ssrIntro| >) => newTactic do introsDep
    | `(ssrIntro| _) => newTactic do
      let name ← fresh "H"
      run  `(tactic| intros $name)
      run  `(tactic| clear $name)

    -- rewrites
    | `(ssrIntro| ->) => newTactic do
      let name ← fresh "H"
      run  `(tactic| intros $name)
      run  `(tactic| rw [$name:ident])
      tryGoal $ run  `(tactic| clear $name)
    | `(ssrIntro| <-) => newTactic do
      let name ← fresh "H"
      run  `(tactic| intros $name)
      run  `(tactic| rw [<-$name:ident])
      tryGoal $ run  `(tactic| clear $name)

    -- switches
    | `(ssrIntro|/$t:ident)
    | `(ssrIntro|/($t:term)) => newTactic do
      let name <- fresh "H"
      run  `(tactic| intros $name)
      run `(tactic| apply $t:term in $name)
    | `(ssrIntro|/(_ $t:term)) => newTactic do
      let name <- fresh "N"
      let h <- fresh "H"
      run  `(tactic| intros $name)
      run  `(tactic| have $h := $t)
      run `(tactic| apply $name:term in $h)
      tryGoal $ run  `(tactic| clear $name)
      tryGoal $ run  `(tactic| clear $h)

    -- destructs
    | `(ssrIntro| []) => newTactic do run  `(tactic| scase)
    | `(ssrIntro| [ $[$is:ssrIntros]|* ] ) => do
      if (← getUnsolvedGoals).length == 1 then run `(tactic|scase)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
        throwErrorAt stx "Given { is.size } tactics, but excpected { goals.length }\n{goalsMsg}"
      else
         idxGoal fun i => withTacticInfoContext is[i]! $  elabIterate is[i]!
    | `(ssrIntro| ![ $[$is:ssrIntros]|* ] ) => do
      run  `(tactic|elim)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
        throwErrorAt stx "Given { is.size } tactics, but excpected { goals.length }\n{goalsMsg}"
      else
        withTacticInfoContext stx $ idxGoal fun i => elabIterate is[i]!

    -- top hyps manipulations
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
      run  `(tactic| intros $n2)
      run  `(tactic| apply $n1 in $n2)
      run  `(tactic| clear $n1)

    -- clears
    -- | `(ssrIntro| {}$i:ident ) => newTactic do
    --   run  `(tactic| clear $i)
    --   run  `(tactic| intros $i)

    | _ => throwErrorAt stx "Unknown action"
  -- where
  --   many (stx : TSyntax `ssrIntros) : TacticM Unit :=
  --   match stx with
  --   | `(ssrIntros| $[$is:ssrIntro] *) => newTactic do
  --     for i in is do allGoal $ elabSsr i
  --   | _ => throwErrorAt stx "Unknown action"

-- def isize : TSyntax `ssrIntros -> MetaM Nat
--    | `(ssrIntros| $[$is:ssrIntro] *) => return is.size
--    | _ => throwError "unsupported syntax"

def elabSsrs :=
  iterateElab (HashMap.ofList [
    (`ssrIntro, elabSsr),
    (`ssrTriv, fun _ => elabSTriv),
    (`ssrBasic, fun _ => elabBasic)
  ])

syntax ssrIntro' := ssrIntro <|> ssrBasic <|> ssrTriv

elab t:tactic "=> " i:ssrIntro' is:ssrIntros : tactic => do
  run `(tactic|$t);
  match i with
  | `(ssrIntro'| []) =>
    let is := mkNullNode $ #[i.raw[0]] ++ is.raw[0].getArgs
    let is := mkNode `ssIntros #[is]
    elabSsrs is
  | `(ssrIntro'| [ $_:ssrIntros|* ]) =>
    withRef i do elabSsr elabSsrs i.raw[0]
    elabSsrs is
  | _ =>
    let is := mkNullNode $ #[i.raw[0]] ++ is.raw[0].getArgs
    let is := mkNode `ssIntros #[is]
    elabSsrs is

-- theorem foo (n : List Nat) : (m : List Nat) -> n = m -> [] = m := by
--   skip=> [|?] // ?


-- inductive True3 where
--   | a1 (x : Nat) (y : True3) : True3
--   | b2 (x : Nat) : True3
--   | c3 (x : Nat) : True3

-- example (k : Nat) : (True ∨ True) -> (True = (True \/ True)) \/ False -> False = True := by
--   scase: k=> ? [] //= ->
