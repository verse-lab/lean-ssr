import Lean
import Lean.Elab.Tactic
import Batteries.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Elim
import Ssreflect.ApplyIn
import Ssreflect.Done
import Ssreflect.Basic


open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

elab "fconstructr" : tactic => withMainContext do
  let mvarIds' ← (← getMainGoal).constructor {newGoals := .all}
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'

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
syntax ssrTriv : ssrIntro
syntax ssrBasic : ssrIntro
syntax (name := ssrIntros) (ppSpace colGt ssrIntro)* ppSpace : ssrIntros
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
-- syntax "[]" : ssrIntro
syntax "?[]" : ssrIntro
syntax "[" sepBy(ssrIntros, "|") "]" : ssrIntro
syntax "![" ssrIntros "]" : ssrIntro
syntax "⟨" sepBy1(ssrIntros, "|") "⟩" : ssrIntro

-- top hyps manipulations
syntax "/[swap]" : ssrIntro
syntax "/[apply]" : ssrIntro
syntax "/[dup]" : ssrIntro

-- clears
syntax "{}" ident : ssrIntro

/--
  Rewrite with top-of-stack hypothesis, either left-to-right (default) or right-to-left,
  annotating errors at the syntax `arr`.
-/
private def rw (arr : Syntax) (rtl : Bool := false) : TacticM Unit := do
    let name ← fresh `H
    let s ← saveState
    try
      run `(tactic| intros $name);
      if rtl then
        run `(tactic| rw [<-$name:ident])
      else
        run `(tactic| rw [$name:ident])
    catch | ex => do restoreState s; throwErrorAt arr ex.toMessageData
    tryGoal $ run `(tactic| clear $name)

private def view (t : TSyntax `term) : TacticM Unit := do
  let name <- fresh `H
  run `(tactic| intros $name)
  run `(tactic| first
    | apply $t:term in $name:ident
    | rw [$t:term] at $name:ident; revert $name
    | rw [<-$t:term] at $name:ident; revert $name)

elab_rules : tactic
    | `(ssrIntro|$i:ident) => run `(tactic| intro $i:ident)
    | `(ssrIntro| ?) => run `(tactic| intro _)
    | `(ssrIntro| !) => run `(tactic| apply_ext_theorem)
    | `(ssrIntro| *) => run `(tactic| intros)
    | `(ssrIntro| >) => introsDep
    | `(ssrIntro| _) => do
      let name ← fresh `H
      run `(tactic| intros $name)
      run `(tactic| clear $name)
    -- rewrites
    | `(ssrIntro| ->%$arr) => newTactic do rw arr
    | `(ssrIntro| <-%$arr) => newTactic do rw arr (rtl := true)
    -- -- switches
    | `(ssrIntro|/$t:ident) => do view t
    | `(ssrIntro|/($t:term)) => do view t
    | `(ssrIntro|/(_ $t:ident)) => do
      let name <- fresh `N
      let h <- fresh `H
      run `(tactic| intros $name)
      run `(tactic| apply $name:term in $t)
      run `(tactic| try clear $name)
      run `(tactic| try clear $h)
    | `(ssrIntro|/(_ $t:term)) => do
      let name <- fresh `N
      let h <- fresh `H
      run `(tactic| intros $name)
      run `(tactic| let $h := $t)
      run `(tactic| apply $name:term in $h)
      run `(tactic| try dsimp only [$h:term])
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
    | `(ssrIntro| ![$is:ssrIntros] ) => do run `(tactic|scase!); elabTactic $ is.raw[0]
    | `(ssrIntro| ⟨$[$is:ssrIntros]|* ⟩ ) => do
      run `(tactic| fconstructr)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
        let s <- `(ssrIntro| [$[$is:ssrIntros]|* ] )
        throwErrorAt s "Given { is.size } tactics, but excpected { goals.length }\n{goalsMsg}"
      else
         idxGoal fun i => newTactic $ elabTactic $ is[i]!.raw[0]

    -- -- top hyps manipulations
    | `(ssrIntro|/[swap]) => newTactic do
      run `(tactic| move)
      let forallE n1 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      run  `(tactic| intros $(mkIdent n1))
      run `(tactic| move)
      let forallE n2 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      run  `(tactic| intros $(mkIdent n2))
      run  `(tactic| revert $(mkIdent n1))
      run  `(tactic| revert $(mkIdent n2))
    | `(ssrIntro|/[dup]) => newTactic do
      let forallE n _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      run  `(tactic| intros $(mkIdent n))
      let n' <- fresh (n ++ "0".toName)
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
    | `(ssrIntro| $t:ssrTriv) => evalTactic t
    | `(ssrIntro| $t:ssrBasic) => evalTactic t

def mkNAryDestruct : Nat -> MacroM (TSyntax `ssrIntro)
  | 0 => `(ssrIntro| [])
  | n+1 => do
    let ndest <- mkNAryDestruct n
    match ndest with
    | `(ssrIntro| [$[$is:ssrIntros]|*]) => do
      let i <- `(ssrIntros| )
      let is := is.push i
      `(ssrIntro| [$[$is:ssrIntros ]|*] )
    | _ => panic! "??"

elab_rules : tactic
  | `(ssrIntro | ?[]) => do
    if (← getUnsolvedGoals).length == 1 then run `(tactic|scase)
    let n := (← getUnsolvedGoals).length
    let stx <- `(ssrIntro | ?[])
    let nbr <- liftMacroM $ mkNAryDestruct (n-1)
    TryThis.addSuggestion stx nbr (origSpan? := ← getRef)

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
  | `(ssrIntro'| ?[]) =>
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

-- inductive foo where
--  | foo
--  | foo'
--  | foo''

-- example : foo -> True -> True ∨ True -> True := by
--   move=> [ | | ] //
