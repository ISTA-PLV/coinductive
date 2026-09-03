/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree.Effect
public import ITree.Definition
public import ITree.Exec

@[expose] public section

namespace ITree.Effects

@[implicit_reducible]
def angelicE (α : Type u) : Effect.{u} where
  I := (α → Prop)
  O p := {a // p a}

unif_hint (α : Type _) (x : (angelicE α).I)  where
  |- (angelicE α).O x ≟ {a // x a}

def AngelicE.choose_angelic {α : Type u} {E : Effect.{u}} [angelicE α -< E] (p : α → Prop) : ITree E {a // p a} :=
  (angelicE α).trigger p
export AngelicE (choose_angelic)

section exec
open ITree.Exec

def angelicEH (α : Type _) : SEHandler (angelicE α) PUnit where
  handle i s p := ∀ x, ∀ (h : i x), p ⟨_, h⟩ s
  handle_mono := by grind

@[simp]
theorem angelicEH_handle {α : Type _} (i : α → Prop) s p :
    (angelicEH α).handle i s p = ∀ x, ∀ (h : i x), p ⟨_, h⟩ s := rfl

theorem exec_choose_angelic {α : Type u} {GE : Effect.{u}} {GR σ p q s}
    {k : {x : α // q x} → ITree GE GR} [angelicE α -< GE]
    (eh : EHandler GE GE GR σ) [hin : InEH (angelicEH α).toEHandler eh]
    : (∀ x h, exec eh (k ⟨x, h⟩) s p) →
      exec eh (choose_angelic q >>= k) s p := by
  intro he; unfold choose_angelic
  apply exec.dup
  apply exec.trigger (angelicEH α).toEHandler
  simp_all

end exec
