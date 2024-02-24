import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Ssreflect.Done
import Ssreflect.Basic
import Lean.Parser.Tactic

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic
open Lean.Parser.Tactic

declare_syntax_cat srwIter
declare_syntax_cat srwTerm
declare_syntax_cat srwRule
declare_syntax_cat srwRules
declare_syntax_cat srwRuleLoc
declare_syntax_cat srwRulesLoc
declare_syntax_cat srwDir
declare_syntax_cat srwPos (behavior := both)
syntax ("?" <|> "!") : srwIter
syntax "-" : srwDir
syntax "[" (num)* "]" : srwPos
syntax atomic("[" noWs "-") (num)* "]" : srwPos
syntax (ident <|> ("(" term ")")) : srwTerm
syntax (name:= srwRule) ((srwDir)? (srwIter)? (srwPos)? srwTerm) : srwRule
syntax srwRule  (location)? : srwRuleLoc
syntax (ppSpace colGt (srwRule <|> ssrTriv <|> ssrBasic))* : srwRules
syntax (name:= srwRulesLoc) (ppSpace colGt (srwRuleLoc <|> ssrTriv <|> ssrBasic))* : srwRulesLoc
syntax (name := srw) "srw" srwRules (location)? : tactic

syntax "repeat! " tacticSeq : tactic
macro_rules
  | `(tactic| repeat! $seq) => `(tactic| ($seq); repeat' $seq)


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


elab_rules : tactic
  | `(srwRuleLoc| $d:srwDir ? $i:srwIter ? $cfg:srwPos ? $t:srwTerm $l:location ?) =>
      try do
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
            | `(srwIter| ?) => run `(tactic| (repeat' ($r:tactic)))
            | `(srwIter| !) => run `(tactic| (repeat! ($r:tactic)))
            | _ => throwErrorAt i "sould be either ? or !"
        | none => evalTactic r
      catch | ex => throwErrorAt t ex.toMessageData

elab "srw" rs:srwRules l:(location)? : tactic =>
  match rs with
  | `(srwRules| $[$ts] *) => do
    let ts <- ts.mapM fun x => do
      if x.raw.isOfKind `srwRule then
        let y <- `(srwRuleLoc| $(⟨x.raw.setKind `srwRule⟩):srwRule $l:location ?)
        return y.raw
      else return x.raw
    elabTactic (annotate := (withTacticInfoContext ·[0])) $ mkNullNode ts
  | _ => throwError ""

elab_rules : tactic
  | `(srwRulesLoc| $[$ts]*) => elabTactic (annotate := (withTacticInfoContext ·[0])) $ mkNullNode ts

-- example : True -> (True /\ False) /\ (True /\ False) = False := by
--   intro a
--   -- rw [true_and] at a
--   srw ?[-1]true_and true_and
