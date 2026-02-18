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

theorem exec_fail {α : Type u} {GE : Effect.{u}} {GR σ p q s}
    {k : α → ITree GE GR}
    [failE -< GE] (eh : EHandler GE GE GR σ) [hin : InEH failEH.toEHandler eh]
    : exec eh (fail q >>= k) s p := by
  unfold fail
  simp only [bind_assoc]
  apply exec.trigger failEH.toEHandler
  simp [failEH]
