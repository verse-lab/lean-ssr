import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Elim
import Ssreflect.ApplyIn
import Ssreflect.Move

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

declare_syntax_cat ssr_intros
declare_syntax_cat ssr_intro
-- intros
syntax ident : ssr_intro
syntax "?" : ssr_intro
syntax "*" : ssr_intro
syntax ">" : ssr_intro
syntax "_" : ssr_intro

-- rewrites
syntax "->" : ssr_intro
syntax "<-" : ssr_intro

-- switches
syntax "/(" term ")" : ssr_intro
syntax "/" ident : ssr_intro
syntax "/(_" term ")" : ssr_intro

-- automations
syntax "//" : ssr_intro
syntax "/==" : ssr_intro
syntax "/=" : ssr_intro
syntax "//="  : ssr_intro
syntax "//=="  : ssr_intro

-- destructs
syntax "[ ]" : ssr_intro
syntax "[" sepBy1(ssr_intros, "|") "]" : ssr_intro

-- top hyps manipulations
syntax "/[swap]" : ssr_intro
syntax "/[apply]" : ssr_intro
syntax "/[dup]" : ssr_intro

-- clears
syntax "{" (ppSpace colGt term:max)+ "}" : ssr_intro
syntax "{}" ident : ssr_intro

-- tactics
syntax "/[tac " tactic "]" : ssr_intro

-- syntax ssr_intros ppSpace ssr_intro : ssr_intros
syntax (ppSpace colGt ssr_intro)* : ssr_intros

syntax "ssr_triv" : tactic

macro_rules |
  `(tactic| ssr_triv) => `(tactic|
    try solve| repeat (constructor <;> intros) <;> trivial)
macro_rules |
  `(tactic| ssr_triv) => `(tactic|
    try solve| repeat (constructor <;> intros) <;> simp_all)


partial def elabSsr (stx :  TSyntax `ssr_intro) : TacticM Unit := withTacticInfoContext stx $ newTactic do
    let stx := (<- liftMacroM (Macro.expandMacro? stx)).getD stx
    match stx with
    -- intros
    | `(ssr_intro|$i:ident) => newTactic do
        run (stx := stx) `(tactic| intro $i:ident)
    | `(ssr_intro| ?) => newTactic do run (stx:=stx) `(tactic| intro _)
    | `(ssr_intro| *) => newTactic do run (stx:=stx) `(tactic| intros)
    | `(ssr_intro| >) => newTactic do introsDep
    | `(ssr_intro| _) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| clear $name)

    -- rewrites
    | `(ssr_intro| ->) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| rw [$name:ident])
      tryGoal $ run (stx:=stx) `(tactic| clear $name)
    | `(ssr_intro| <-) => newTactic do
      let name ← fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| rw [<-$name:ident])
      tryGoal $ run (stx:=stx) `(tactic| clear $name)

    -- switches
    | `(ssr_intro|/$t:ident)
    | `(ssr_intro|/($t:term)) => newTactic do
      let name <- fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=t) `(tactic| apply $t:term in $name)
    | `(ssr_intro|/(_ $t:term)) => newTactic do
      let name <- fresh "N"
      let h <- fresh "H"
      run (stx:=stx) `(tactic| intros $name)
      run (stx:=stx) `(tactic| have $h := $t)
      run (stx:=t) `(tactic| apply $name:term in $h)
      tryGoal $ run (stx:=stx) `(tactic| clear $name)
      tryGoal $ run (stx:=stx) `(tactic| clear $h)


    -- automations
    | `(ssr_intro| //) => newTactic do run (stx:=stx) `(tactic| try solve | ((intros; ssr_triv); try (intros; simp_all; ssr_triv)) )
    | `(ssr_intro| /=) => newTactic do run (stx:=stx) `(tactic| dsimp)
    | `(ssr_intro| /==) => newTactic do run (stx:=stx) `(tactic| simp)
    | `(ssr_intro| //=) => newTactic do run (stx:=stx) `(tactic| try dsimp; try solve | ((intros; ssr_triv); try (intros; simp_all; ssr_triv)) )
    | `(ssr_intro| //==) => newTactic do run (stx:=stx) `(tactic| try simp; try solve | ((intros; ssr_triv); try (intros; simp_all; ssr_triv)) )

    -- destructs
    | `(ssr_intro| []) => newTactic do run (stx:=stx) `(tactic| scase)
    | `(ssr_intro| [ $[$is:ssr_intros]|* ] ) => do
      if (← getUnsolvedGoals).length == 1 then
        run (stx:=stx) `(tactic|scase)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        run (stx := stx) `(tactic| fail "Given { is.size } tactics, but excpected { goals.length }")
      else
        idxGoal fun i => many is[i]!

    -- top hyps manipulations
    | `(ssr_intro|/[swap]) => newTactic do
      let forallE n1 _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      run (stx:=stx) `(tactic| intros $(mkIdent n1))
      let forallE n2 _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      run (stx:=stx) `(tactic| intros $(mkIdent n2))
      run (stx:=stx) `(tactic| revert $(mkIdent n1))
      run (stx:=stx) `(tactic| revert $(mkIdent n2))
    | `(ssr_intro|/[dup]) => newTactic do
      let forallE n _ _ _ := (<- getMainTarget).consumeMData
        | run (stx := stx) `(tactic| fail "Goal is not an arrow type")
      run (stx:=stx) `(tactic| intros $(mkIdent n))
      let n' <- fresh (n ++ "0")
      run (stx:=stx) `(tactic| have $n' := $(mkIdent n))
      run (stx:=stx) `(tactic| revert $(mkIdent n))
      run (stx:=stx) `(tactic| revert $n')
    | `(ssr_intro|/[apply]) => newTactic do
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
    | `(ssr_intro| { $ts:term* }) => newTactic do
      run (stx:=stx) `(tactic| clear $ts*)
    | `(ssr_intro| {}$i:ident ) => newTactic do
      run (stx:=stx) `(tactic| clear $i)
      run (stx:=stx) `(tactic| intros $i)

    -- tactics
    | `(ssr_intro| /[tac $t:tactic]) => newTactic do
      run (stx:=stx) `(tactic| $t)
    | _ => throwErrorAt stx "Unknown action"
  where
    many (stx : TSyntax `ssr_intros) : TacticM Unit :=
    match stx with
    | `(ssr_intros| $[$is:ssr_intro] *) => newTactic do
      for i in is do allGoal $ elabSsr i
    | _ => throwErrorAt stx "Unknown action"


elab t:tactic "=> " i:ssr_intro is:ssr_intros : tactic => do
  run `(tactic|$t);
  (match i with
  | `(ssr_intro| [] ) => allGoal $ elabSsr i
  | `(ssr_intro| [ $[$is:ssr_intros]|* ] ) => elabSsr i
  | _ => allGoal $ elabSsr i);
  tryGoal $ elabSsr.many is

elab "sby " t:tacticSeq : tactic => do
   evalTactic t.raw
   tryGoal $ allGoal $
      run `(tactic| solve | move=> // | moveR=> // | skip=> //)

-- inductive foo : Int -> Type where
--   | a (b : Bool) (eq : b = b) (x : Int) (eqq : if b then x > 0 else x < 0)
--     (i : Int) : foo i
--   | b (b : Bool) : foo 5

-- macro "///" : ssr_intro => `(ssr_intro| /[tac skip])

-- axiom bar : forall n : Nat, Bool -> n = n -> n = 6
