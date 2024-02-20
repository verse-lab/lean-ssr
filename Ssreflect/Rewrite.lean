import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

declare_syntax_cat srwIter
declare_syntax_cat srwTerm
syntax ("?" <|> "!") : srwIter
syntax srwPos := "[" (num)* "]"
syntax (ident <|> ("(" term ")")) : srwTerm
syntax srwRule := (srwIter)? srwTerm
syntax (name := srw) "srw" (ppSpace colGt srwRule)* : tactic

syntax "repeat! " tacticSeq : tactic
macro_rules
  | `(tactic| repeat! $seq) => `(tactic| ($seq); repeat $seq)

syntax (name := withAnnotateState)
  "with_annotate_state " rawStx ppSpace tactic : tactic

@[tactic withAnnotateState] def evalWithAnnotateState : Tactic
  | `(tactic| with_annotate_state $stx $t) =>
    withTacticInfoContext stx (evalTactic t)
  | _ => throwUnsupportedSyntax

@[tactic srw] partial def evalSrw : Tactic
  | `(tactic| srw $i:srwIter ? ($t:term) $rw:srwRule*) => do
      withTacticInfoContext t $ match i with
      | some i =>
          match i with
          | `(srwIter| ?) => run (stx := t) `(tactic| (repeat  rw [$t:term]))
          | `(srwIter| !) => run (stx := t) `(tactic| (repeat! rw [$t:term]))
          | _ => throwErrorAt i "sould be either ? or !"
      | none => run (stx := t) `(tactic| rw [$t:term])
      allGoal $ run `(tactic| srw $rw*)
  | `(tactic| srw) => run `(tactic| skip)
  | _ => throwError "unsupported syntax for srw tactic"

-- macro_rules
--   |  => do
--      let r <- match i with
--       | some i =>
--           match i with
--           | `(srwIter| ?) => `(tactic| (repeat  rw [$t:term]))
--           | `(srwIter| !) => `(tactic| (repeat! rw [$t:term]))
--           | _ => Lean.Macro.throwErrorAt i "sould be either ? or !"
--       | none => `(tactic| rw [$t:term])
--       `(tactic| (with_annotate_state $t $r) <;> srw $rw*)
--   | `(tactic| srw) => `(tactic| skip)
