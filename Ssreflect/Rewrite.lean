import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.IntroPats

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

declare_syntax_cat srwIter
declare_syntax_cat srwTerm
declare_syntax_cat srwDir
declare_syntax_cat srwPos (behavior := both)
syntax ("?" <|> "!") : srwIter
syntax "-" : srwDir
syntax "[" (num)* "]" : srwPos
syntax atomic("[" noWs "-") (num)* "]" : srwPos
syntax (ident <|> ("(" term ")")) : srwTerm
syntax srwRule := (srwDir)? (srwIter)? (srwPos)? srwTerm
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


partial def macroCfgPos (stx : TSyntax `srwPos) : MacroM $ TSyntax `term :=
  match stx with
  | `(srwPos| [ $n:num $ns:num * ]) => do
    let pos <- macroCfgPos (<- `(srwPos| [ $ns:num* ]))
    `(term| $n :: $pos)
  | `(srwPos| []) => `(term| [])
  | _ => Macro.throwUnsupported

partial def macroCfgNeg (stx : TSyntax `srwPos) : MacroM $ TSyntax `term :=
  match stx with
  | `(srwPos| [- $n:num $ns:num * ]) => do
    let pos <- macroCfgPos (<- `(srwPos| [ $ns:num* ]))
    `(term| $n :: $pos)
  | `(srwPos| []) => `(term| [])
  | _ => Macro.throwUnsupported

partial def macroCfg (stx : TSyntax `srwPos) : MacroM $ TSyntax `term :=
  match stx with
  | `(srwPos| [- $_:num * ]) => do
      let m <- macroCfgNeg stx
      `(term| Occurrences.neg $m)
  | `(srwPos| [ $_:num * ]) => do
      let m <- macroCfgPos stx
      `(term| Occurrences.pos $m)
  | _ => Macro.throwErrorAt stx "Unsupported syntax for 'srw' positions"


@[tactic srw] partial def evalSrw : Tactic
  | `(tactic| srw $d:srwDir ? $i:srwIter ? $cfg:srwPos ? $t:srwTerm $rw:srwRule*) => do
      withTacticInfoContext t $ do
      let t' := match t with
        | `(srwTerm| ($t:term)) => some t
        | `(srwTerm| $t:ident) => some t
        | _ => none
      let some t := t' | throwErrorAt t "Unsupported Syntax"
      let cfg <- match cfg with
      | some cfg =>
        let cfg <- liftMacroM <| macroCfg cfg
        `(term| {occs := $cfg})
      | _ => `(term| {occs := .all})
      let r <- match d with
        | some _ => `(tactic| rw (config := $cfg) [<-$t:term])
        | none   => `(tactic| rw (config := $cfg) [$t:term])
      match i with
      | some i =>
          match i with
          | `(srwIter| ?) => run (stx := t) `(tactic| (repeat ($r:tactic)))
          | `(srwIter| !) => run (stx := t) `(tactic| (repeat! ($r:tactic)))
          | _ => throwErrorAt i "sould be either ? or !"
      | none => run (stx := t) (return r)
      allGoal $ run `(tactic| srw $rw*)
  | `(tactic| srw) => tryGoal $ run `(tactic| skip)
  | _ => throwError "unsupported syntax for srw tactic"


-- example : (True /\ False) /\ (True /\ False) = False := by
--   srw [-1]true_and
