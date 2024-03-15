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

declare_syntax_cat ssrRw
syntax ssrTriv : ssrRw
syntax term:max : ssrRw
declare_syntax_cat ssrRws
syntax (ppSpace colGt (ssrRw))* : ssrRws

abbrev LocationExtState := Option
  (TSyntax `Lean.Parser.Tactic.location)

initialize locExt :
  EnvExtension LocationExtState ←
  registerEnvExtension (pure none)

elab_rules : tactic
  | `(ssrRw| $t:ssrTriv) => evalTactic t
  | `(ssrRw|$i:term) => do
    run `(tactic| rw [$i:term] $(<- locExt.get)?)

elab_rules : tactic
  | `(ssrRws| $rs:ssrRw*) =>
    for r in rs do allGoal $ evalTactic r


elab "srw" rs:ssrRws l:(location)? : tactic => do
  locExt.set l
  evalTactic rs

-- example (x y : Nat) (H : x = y) (H' : y = y) : x = 0 := by
--   srw H H' //
