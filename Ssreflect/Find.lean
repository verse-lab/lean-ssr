import Lean
import Std.Data.String.Basic
import Std.Util.Pickle
import Std.Lean.Delaborator

import Loogle.Cache
import Loogle.NameRel
import Loogle.RBTree
import Loogle.BlackListed
import Loogle.Trie
import Loogle.Find

open Lean Meta Elab
open Parser
open Loogle.Find
open Command

register_option find.showTypes : Bool := {
  defValue := true
  descr := "showing types in #f"
}

def MessageData.bulletList' (xs : Array (MessageData × Expr)) (showTypes : Bool := false) : MessageData :=
  MessageData.joinSep (xs.toList.map (fun x =>
  let type? : MessageData := if showTypes then " : " ++ x.2 else ""
  m!"• " ++ x.1 ++ type?)) Format.line


def MessageData.bulletListOfConstsAndTypes {m} [Monad m] [MonadEnv m] [MonadError m]
    (names : Array (Name × Expr)) (showTypes : Bool := false) : m MessageData := do
  let es ← names.mapM $ fun x =>do return (<- mkConstWithLevelParams x.1, x.2)
  pure (MessageData.bulletList' (es.map (fun x => (ppConst x.1, x.2))) showTypes)

def elabFind (args : TSyntax `Loogle.Find.find_filters) : TermElabM Unit := do
  profileitM Exception "find" (← getOptions) do
      match ← find cachedIndex args with
      | .error ⟨s, warn, suggestions⟩ => do
        Lean.logErrorAt s warn
        unless suggestions.isEmpty do
          Std.Tactic.TryThis.addSuggestions args <| suggestions.map fun sugg =>
            { suggestion := .tsyntax sugg }
      | .ok result =>
        let showTypes := (<- getOptions).get find.showTypes.name find.showTypes.defValue
        let names := result.hits.map $ fun x=> (x.1.name, x.1.type)
        Lean.logInfo $ result.header ++ (← MessageData.bulletListOfConstsAndTypes names showTypes)

elab(name := findSyntax) "#f " args:find_filters : command =>
  liftTermElabM $ elabFind args

elab(name := findSyntaxTac) "#f " args:find_filters : tactic =>
  elabFind args
