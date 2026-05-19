module

public import ITree.Effect
public import ITree.Definition
public import ITree.Eval
public import ITree.Exec

@[expose] public section
namespace ITree.Effects

def demonicE (α : Type u) : Effect.{u} where
  I := ((p : α → Prop) × (DecidablePred p) × (Inhabited {x : α // p x}))
  O p := {a // p.1 a}

def DemonicE.choose {α : Type u} {E : Effect.{u}} [demonicE α -< E] (p : α → Prop) [hp : DecidablePred p] [hi : Inhabited {x : α // p x}] : ITree E {a // p a} :=
   (demonicE α).trigger ⟨p, hp, hi⟩
export DemonicE (choose)

section exec
open ITree.Exec

def demonicEH (α : Type _) : SEHandler (demonicE α) PUnit where
  handle i s p := ∃ x, ∃ (h : i.1 x), p ⟨_, h⟩ s
  handle_mono := by grind

theorem exec_choose {α : Type u} {GE : Effect.{u}} {GR σ p q s}
    {k : {x : α // q x} → ITree GE GR} x h [demonicE α -< GE]
    [DecidablePred q] [Inhabited {x : α // q x}]
    (eh : EHandler GE GE GR σ) [hin : InEH (demonicEH α).toEHandler eh]
    : (exec eh (k ⟨x, h⟩) s p) →
      exec eh (choose q >>= k) s p := by
  intro he; unfold choose
  apply exec.dup
  apply exec.trigger (demonicEH α).toEHandler
  simp_all [demonicEH]
  exists ?_, ?_ <;> try assumption

end exec

section eval
open ITree.Eval

instance demonicMH [Monad m] : SMHandler (demonicE α) m where
  handle i := return i.2.2.default

end eval
