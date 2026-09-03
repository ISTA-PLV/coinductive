/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Lean.Log
public import ITree.Effect
public import ITree.Definition
public import ITree.Exec
public import ITree.Eval

@[expose] public section
namespace ITree.Effects
open Lean

@[implicit_reducible]
def logE (α : Type u) : Effect.{u} where
  I := α
  O _ := PUnit

def LogE.log {α : Type u} {E} [logE α -< E] (a : α) : ITree.{u} E PUnit :=
  (logE α).trigger (a)
export LogE (log)

section Eval
open ITree.Eval

instance logMH {α m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] [ToMessageData α] : SMHandler (logE α) m where
  handle i := let i : α := i; logInfo m!"{i}"

end Eval
