/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree.Effect
public import ITree.Definition

@[expose] public section
namespace ITree.Effects

@[implicit_reducible]
def emptyE : Effect.{u} where
  I := PEmpty.{u+1}
  O := nofun
