import ITree.Effect
import ITree.Definition
import ITree.Exec

namespace ITree.Effects
open ITree.Exec

def stateE (α : Type u) : Effect.{u} where
  I := (α → α)
  O _ := α

def StateE.modify {α : Type u} {E} [stateE α -< E] (f : α → α) : ITree E α :=
  .trigger (stateE α) f

def StateE.get {α : Type u} {E} [stateE α -< E] : ITree E α :=
  modify id

def StateE.set {α : Type u} {E} [stateE α -< E] (a : α) : ITree E PUnit :=
  modify (λ _ => a) >>= λ _ => return ⟨⟩

def StateE.modifyGet {α : Type u} {β} {E} [stateE α -< E] (f : α → Prod β α) : ITree E β :=
  do let (x, s) := f (← StateE.get); StateE.set s; return x

set_option synthInstance.checkSynthOrder false in
instance [stateE α -< E] : MonadStateOf α (ITree E) where
  get := StateE.get
  set := StateE.set
  modifyGet := StateE.modifyGet

def stateEH (α : Type u) : SEHandler (stateE α) α where
  handle i s p := p s (i s)
  handle_mono := by grind

theorem exec_stateE_get {α : Type u} {GE : Effect.{u}} GR σ p s
    {k : α → ITree GE GR}
    [stateE α -< GE] (eh : EHandler GE GE GR σ) [hin : InEH (stateEH α).toEHandler eh]
    : exec eh (k (hin.getState s)) s p →
      exec eh (StateE.get >>= k) s p := by
  rintro he; simp [StateE.get]
  apply exec.dup
  apply exec.trigger (stateEH _).toEHandler
  simp_all [stateEH]

theorem exec_get {α : Type u} {GE : Effect.{u}} GR σ p s
    {k : α → ITree GE GR}
    [stateE α -< GE] (eh : EHandler GE GE GR σ) [hin : InEH (stateEH α).toEHandler eh]
    : exec eh (k (hin.getState s)) s p →
      exec eh (get >>= k) s p := exec_stateE_get GR σ p s eh

theorem exec_stateE_set {α : Type u} {GE : Effect.{u}} GR σ p s (s' : α)
    {k : PUnit → ITree GE GR}
    [stateE α -< GE] (eh : EHandler GE GE GR σ) [hin : InEH (stateEH α).toEHandler eh]
    : exec eh (k ⟨⟩) (hin.putState s' s) p →
      exec eh (StateE.set s' >>= k) s p := by
  rintro he; simp [StateE.set]
  apply exec.dup
  apply exec.trigger (stateEH _).toEHandler
  simp_all [stateEH]

theorem exec_set {α : Type u} {GE : Effect.{u}} GR σ p s (s' : α)
    {k : PUnit → ITree GE GR}
    [stateE α -< GE] (eh : EHandler GE GE GR σ) [hin : InEH (stateEH α).toEHandler eh]
    : exec eh (k ⟨⟩) (hin.putState s' s) p →
      exec eh (set s' >>= k) s p := exec_stateE_set GR σ p s s' eh
