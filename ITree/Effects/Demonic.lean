import ITree.Effect
import ITree.Definition
import ITree.Exec

namespace ITree.Effects
open ITree.Exec

def demonicE (α : Type u) : Effect.{u} where
  I := α → Prop
  O p := {a // p a}

def DemonicE.choose {α : Type u} {E : Effect.{u}} [demonicE α -< E] (p : α → Prop) : ITree E {a // p a} :=
  .trigger (demonicE α) p
export DemonicE (choose)

def demonicEH (α : Type _) : SEHandler (demonicE α) PUnit where
  handle i s p := ∃ x, ∃ (h : i x), p ⟨_, h⟩ s
  handle_mono := by grind

theorem exec_choose {α : Type u} {GE : Effect.{u}} {GR σ p q s}
    {k : {x : α // q x} → ITree GE GR} x h
    [demonicE α -< GE] (eh : EHandler GE GE GR σ) [hin : InEH (demonicEH α).toEHandler eh]
    : (exec eh (k ⟨x, h⟩) s p) →
      exec eh (choose q >>= k) s p := by
  intro he; unfold choose
  apply exec.dup
  apply exec.trigger (demonicEH α).toEHandler
  simp_all [demonicEH]
  exists ?_, ?_ <;> try assumption
