/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree.Effect
public import ITree.Definition
public import ITree.Eval
public import ITree.Exec

@[expose] public section
namespace ITree.Effects

@[implicit_reducible] def stepE : Effect.{u} where
  I := PUnit
  O _ := PUnit

def StepE.step {E : Effect.{u}} [stepE -< E] : ITree E PUnit :=
  stepE.trigger ⟨⟩
export StepE (step)

section exec
open ITree.Exec

/- nl is the number of laters per step. First component of the state is
the number of steps taken so far. Second component of the state is the number of steps left. -/
def stepEH (nl : Nat → Nat) : SEHandler stepE (ULift.{v} Nat × ULift.{v} Nat) where
  handle i s p :=
    nl s.1.down ≤ s.2.down ∧ p ⟨⟩ (ULift.up (s.1.down + 1), ULift.up (s.2.down - nl s.1.down))
  handle_mono := by grind

theorem exec_step {GE : Effect.{u}} {GR σ p} {s} nl
    {k : PUnit → ITree GE GR} [stepE -< GE]
    (eh : EHandler.{u} GE GE GR σ) [hin : InEH (stepEH nl).toEHandler eh]
    : nl (hin.getState s).1.down ≤ (hin.getState s).2.down →
      (exec.{u} eh (k ⟨⟩) (hin.putState (ULift.up ((hin.getState s).1.down + 1), ULift.up ((hin.getState s).2.down - nl (hin.getState s).1.down)) s) p) →
      exec.{u} eh (step >>= k) s p := by
  intro _ he; unfold step
  apply exec.dup
  apply exec.trigger (stepEH nl).toEHandler
  constructor; assumption
  simp [he]

theorem exec_step_0 {GE : Effect.{u}} {GR σ p} {s}
    {k : PUnit → ITree GE GR} [stepE -< GE]
    (eh : EHandler.{u} GE GE GR σ) [hin : InEH (stepEH λ _ => 0).toEHandler eh]
    :
      (exec.{u} eh (k ⟨⟩) (hin.putState (ULift.up ((hin.getState s).1.down + 1), (hin.getState s).2) s) p) →
      exec.{u} eh (step >>= k) s p := by
  intro he
  apply exec_step (λ _ => 0)
  · simp
  simp [he]


end exec

section eval
open ITree.Eval

instance stepMH [Monad m] : SMHandler stepE m where
  handle _ := return ⟨⟩

end eval
