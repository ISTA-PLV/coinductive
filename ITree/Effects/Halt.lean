/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree.Effect
public import ITree.Definition
public import ITree.Eval
public import ITree.Exec

@[expose] public section
namespace ITree.Effects

def haltE : Effect.{u} where
  I := PUnit
  O _ := PEmpty

def HaltE.halt {α} {E : Effect.{u}} [haltE -< E] : ITree E α :=
  haltE.trigger ⟨⟩ >>= nofun
export HaltE (halt)

def HaltE.assume {E : Effect.{u}} [haltE -< E] (P : Prop) [Decidable P] : ITree E {_x : PUnit.{u+1} // P} :=
  if h : P then return ⟨⟨⟩, h⟩ else halt
export HaltE (assume)

section exec
open ITree.Exec

def haltEH : SEHandler haltE PUnit where
  handle i s p := False
  handle_mono := by grind

theorem exec_assume {GE : Effect.{u}} {GR σ p P s}
    {k : {_x : PUnit.{u+1} // P} → ITree GE GR} h [haltE -< GE]
    [Decidable P]
    (eh : EHandler GE GE GR σ) [_hin : InEH (haltEH).toEHandler eh]
    : (exec eh (k ⟨⟨⟩, h⟩) s p) →
      exec eh (assume P >>= k) s p := by
  intro he; unfold assume halt
  split
  · simp [he]
  · grind

end exec

section eval
open ITree.Eval

-- TODO: Error message like for fail?
instance haltMH [Monad m] [MonadExceptOf String m] : SMHandler haltE m where
  handle _ := throw "halted"

end eval
