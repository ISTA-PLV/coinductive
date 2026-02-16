import ITree.Effect
import ITree.Definition
import ITree.Exec

namespace ITree.Effects
open ITree.Exec

def failE : Effect.{u} where
  I := ULift String
  O _ := PEmpty

def FailE.fail {α : Type u} {E} [failE -< E] (s : String) : ITree.{u} E α :=
  .trigger (failE) (ULift.up s) >>= nofun
export FailE (fail)

def failEH : SEHandler failE PUnit where
  handle i s p := True
  handle_mono := by grind
