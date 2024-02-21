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

#check Format

def MessageData.bulletListTypes (xs : Array (MessageData × Format)) : MessageData :=
  MessageData.joinSep (xs.toList.map (fun x => m!"• " ++ x.1 ++ " : " ++ x.2)) Format.line

def MessageData.bulletListOfConstsTypes {m} [Monad m] [MonadEnv m] [MonadError m]
    (names : Array (Name × Format)) : m MessageData := do
  let es ← names.mapM $ fun x =>do return (<- mkConstWithLevelParams x.1, x.2)
  pure (MessageData.bulletListTypes (es.map (fun x => (ppConst x.1, x.2))))

elab(name := findSyntax) "#f " args:find_filters : command => liftTermElabM do
  profileitM Exception "find" (← getOptions) do
    match ← find cachedIndex args with
    | .error ⟨s, warn, suggestions⟩ => do
      Lean.logErrorAt s warn
      unless suggestions.isEmpty do
        Std.Tactic.TryThis.addSuggestions args <| suggestions.map fun sugg =>
          { suggestion := .tsyntax sugg }
    | .ok result =>
      let names <- result.hits.mapM $ fun x=> do let ty <- ppExpr x.1.type; return (x.1.name, ty)
      Lean.logInfo $ result.header ++ (← MessageData.bulletListOfConstsTypes names)

elab(name := findSyntaxTac) "#f " args:find_filters : tactic => do
  profileitM Exception "find" (← getOptions) do
    match ← find cachedIndex args with
    | .error ⟨s, warn, suggestions⟩ => do
      Lean.logErrorAt s warn
      unless suggestions.isEmpty do
        Std.Tactic.TryThis.addSuggestions args <| suggestions.map fun sugg =>
          { suggestion := .tsyntax sugg }
    | .ok result =>
      let names <- result.hits.mapM $ fun x=> do let ty <- ppExpr x.1.type; return (x.1.name, ty)
      Lean.logInfo $ result.header ++ (← MessageData.bulletListOfConstsTypes names)
