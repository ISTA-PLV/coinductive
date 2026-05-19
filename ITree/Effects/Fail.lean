module

public import ITree.Effect
public import ITree.Definition
public import ITree.Exec
public import ITree.Eval

@[expose] public section
namespace ITree.Effects

def failE : Effect.{u} where
  I := ULift String
  O _ := PEmpty

def FailE.fail {α : Type u} {E} [failE -< E] (s : String) : ITree.{u} E α :=
  (failE).trigger (ULift.up s) >>= nofun
export FailE (fail)

def FailE.assert {E} [failE -< E] (P : Prop) [Decidable P] : ITree.{u} E PUnit :=
  if P then return ⟨⟩ else fail s!"assertion failed"
export FailE (assert)

section Exec
open ITree.Exec

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

end Exec

section Eval
open ITree.Eval

instance failMH {m} [Monad m] [MonadExceptOf String m] : SMHandler failE m where
  handle i := throw i.down

end Eval
