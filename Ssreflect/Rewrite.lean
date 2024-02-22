import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Done
import Lean.Parser.Tactic

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic
open Lean.Parser.Tactic

declare_syntax_cat srwIter
declare_syntax_cat srwTerm
declare_syntax_cat srwRule
declare_syntax_cat srwDir
declare_syntax_cat srwPos (behavior := both)
syntax ("?" <|> "!") : srwIter
syntax "-" : srwDir
syntax "[" (num)* "]" : srwPos
syntax atomic("[" noWs "-") (num)* "]" : srwPos
syntax (ident <|> ("(" term ")")) : srwTerm
syntax  ((srwDir)? (srwIter)? (srwPos)? srwTerm) : srwRule
syntax srwRules := (ppSpace colGt (srwRule <|> ssrTriv))*
syntax (name := srw) "srw" srwRules (location)? : tactic

syntax "repeat! " tacticSeq : tactic
macro_rules
  | `(tactic| repeat! $seq) => `(tactic| ($seq); repeat $seq)


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


def elabSrwRule (l : Option (TSyntax `Lean.Parser.Tactic.location)) : Tactic
  | `(srwRule| $d:srwDir ? $i:srwIter ? $cfg:srwPos ? $t:srwTerm) => do
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
        | some _ => `(tactic| rw (config := $cfg) [<-$t:term] $(l)?)
        | none   => `(tactic| rw (config := $cfg) [$t:term] $(l)?)
      match i with
      | some i =>
          match i with
          | `(srwIter| ?) => run (stx := t) `(tactic| (repeat ($r:tactic)))
          | `(srwIter| !) => run (stx := t) `(tactic| (repeat! ($r:tactic)))
          | _ => throwErrorAt i "sould be either ? or !"
      | none => run (stx := t) (return r)
  | _ => throwError "unsupported syntax for srw tactic"


@[tactic srw]
def elabSrw : Tactic
  | `(tactic| srw $rs:srwRules $l:location ?) =>
      iterateElab
        (HashMap.ofList [(`srwRule, elabSrwRule l), (`ssrTriv, elabSTriv)])
        rs
  | _ => throwError "unsupported syntax for srw tactic"


-- example : (True /\ False) /\ (True /\ False) = False := by
--   srw [-1]true_and true_and //==
