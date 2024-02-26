import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Elim
import Lean.Parser.Tactic

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic
open Lean.Parser.Tactic

/-
Plan:

  1. Simple automation
    a. syntax
    b. elab_rules (evalTactic)
    c. macro
  2. Simple intro patterns
    a. syntax
    b. elab_rules
    c. elab many
  3. Simple revert patterns
    a. syntax
    b. elab_rules
    c. reverse annotation problem
  4. Simple rewrite patterns
    a. syntax
    b. elab_rules
    c. syntax transformation
    d. goal annotation
  5. introdusing elabTactic

-/

/-- ***Automation*** -/

syntax "ssr_triv_core" : tactic
syntax "ssr_triv" : tactic


macro_rules |
  `(tactic| ssr_triv_core) => `(tactic|
    try solve
     | (repeat (constructor <;> intros)) <;> simp_all
     | (repeat (constructor <;> intros)) <;> trivial)

macro_rules |
  `(tactic| ssr_triv) => `(tactic| try solve | ((intros; ssr_triv_core); try (intros; simp_all; ssr_triv_core)))

declare_syntax_cat ssrTriv
syntax "//" : ssrTriv
syntax "/=" : ssrTriv
syntax "/==" : ssrTriv
syntax "//=" : ssrTriv
syntax "//==" : ssrTriv
declare_syntax_cat ssrTrivs
syntax (name:= ssrTrivs) (ppSpace colGt ssrTriv)* : ssrTrivs

macro_rules
  | `(ssrTriv| //=) => `(ssrTrivs| /= //)
  | `(ssrTriv| //==) => `(ssrTrivs| /== //)

elab_rules : tactic
  | `(ssrTriv|  //) => run `(tactic| try ssr_triv)
  | `(ssrTriv|  /=) => run `(tactic| try dsimp)
  | `(ssrTriv| /==) => run `(tactic| try simp)

/-
def evalTriv : Tactic

-/

elab_rules : tactic
  | `(ssrTrivs| $ts:ssrTriv *) => for t in ts do allGoal <| evalTactic t

/-- *** Intro patterns *** -/


declare_syntax_cat ssrIntro
declare_syntax_cat ssrIntros
syntax (name := ssrIntros) (ppSpace colGt (ssrIntro <|> ssrTriv))* : ssrIntros
-- intros
syntax ident : ssrIntro
syntax "?" : ssrIntro
syntax "*" : ssrIntro
syntax "_" : ssrIntro

-- rewrites
syntax "->" : ssrIntro

-- destructs
syntax "[" sepBy1(ssrIntros, "|") "]" : ssrIntro

-- stack manipulations
syntax "/[swap]" : ssrIntro


elab_rules : tactic
    | `(ssrIntro|$i:ident) => run `(tactic| intro $i:ident)
    | `(ssrIntro| ?) => run `(tactic| intro _)
    | `(ssrIntro| *) => run `(tactic| intros)
    | `(ssrIntro| _) => do
      let name ← fresh "H"
      run `(tactic| intros $name)
      run `(tactic| clear $name)

    -- rewrites
    | `(ssrIntro| ->) => do
      let name ← fresh "H"
      run `(tactic| intros $name)
      run `(tactic| rw [$name:ident])
      run `(tactic| try clear $name)

    -- destructs
    | `(ssrIntro| []) => run `(tactic| scase)
    | `(ssrIntro| [$[$is:ssrIntros]|* ] ) => do
      if (← getUnsolvedGoals).length == 1 then run `(tactic|scase)
      let goals ← getUnsolvedGoals
      if goals.length != is.size then
        let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
        let s <- `(ssrIntro| [$[$is]|* ])
        throwErrorAt s "Given { is.size } tactics, but excpected { goals.length }\n{goalsMsg}"
      else
         idxGoal fun i => newTactic <| evalTactic is[i]!

    -- stack manipulations
    | `(ssrIntro|/[swap]) => newTactic do
      let forallE n1 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      let n1 := mkIdent n1
      run  `(tactic| intros $n1)
      let forallE n2 _ _ _ := (<- getMainTarget).consumeMData
        | run  `(tactic| fail "Goal is not an arrow type")
      let n2 := mkIdent n2
      run  `(tactic| intros $n2; revert $n1 $n2)


elab_rules : tactic
  | `(ssrIntros| $[$is]*) => for i in is do allGoal $ evalTactic i

/-- *** Revert patterns *** -/


declare_syntax_cat ssrRevert
declare_syntax_cat ssrReverts

syntax ident : ssrRevert
syntax "(" term ")" : ssrRevert
syntax (name:= ssrReverts) (ppSpace colGt (ssrRevert))* : ssrReverts

elab_rules : tactic
  | `(ssrRevert|$i:ident) => do
      run  `(tactic| revert $i:term)
  | `(ssrRevert|($t:term)) => do
      let h <- fresh "H"
      let goal <- getMainGoal
      let trm <- Term.elabTerm t none
      let goal <- goal.assert h.getId (<- inferType trm) trm
      setGoals [goal]
  | `(ssrReverts| $[$rs]*) => for r in rs do allGoal $ evalTactic r

elab t:tactic ":" is:ssrReverts : tactic => do
  evalTactic is; evalTactic t

-- example (n m : α) : m = n := by
--   skip: (Eq.refl n)


-- example (n m : α) : m = n := by
--   skip: n (Eq.refl n)

elab t:tactic ":" is:ssrReverts : tactic => do
  let is := is.raw[0].getArgs.reverse
  evalTactic $ mkNullNode is
  evalTactic t

-- example (n m : α) : m = n := by
--   skip: n (Eq.refl n)
--   rw

-- /-- *** Rewrite patterns *** -/


declare_syntax_cat srwRule
declare_syntax_cat srwRules
declare_syntax_cat srwRuleLoc
declare_syntax_cat srwRulesLoc
syntax (name:= srwRule) term:max : srwRule
syntax srwRule  (location)? : srwRuleLoc
syntax (ppSpace colGt (srwRule))* : srwRules
syntax (name:= srwRulesLoc) (ppSpace colGt (srwRuleLoc))* : srwRulesLoc
syntax (name := srw) "srw" srwRules (location)? : tactic


elab_rules : tactic
  | `(srwRuleLoc| $t:term $l:location ?) =>
      try do
        evalTactic $ <- `(tactic| rw [$t:term] $(l)?)
      catch | ex => throwErrorAt t ex.toMessageData

def insertLocation (l : Option (TSyntax `Lean.Parser.Tactic.location)) (x : TSyntax `srwRule) : MacroM Syntax := do
  if x.raw.isOfKind `srwRule then
        let y <- `(srwRuleLoc| $(⟨x.raw.setKind `srwRule⟩):srwRule $l:location ?)
        return y.raw
      else return x.raw

elab "srw" rs:srwRules l:(location)? : tactic =>
  match rs with
  | `(srwRules| $[$ts] *) => do
    let ts <- ts.mapM (liftMacroM $ insertLocation l ·)
    evalTactic $ mkNullNode ts
  | _ => throwError ""

example (H : (True /\ False) /\ (True /\ False) = False) : True -> (True /\ False) /\ (True /\ True) = False := by
  intro a
  srw true_and true_and
