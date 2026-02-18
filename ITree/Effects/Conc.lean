import ITree.Effect
import ITree.Definition
import ITree.Exec

namespace ITree.Effects
open Lean.Order ITree.Exec

inductive ForkResult : Type u
| parent | child

inductive concE.I : Type u where
| fork | kill | yield

def concE : Effect.{u} where
  I := concE.I
  O
  | .fork => ForkResult
  | .kill => PEmpty
  | .yield => PUnit

def ConcE.kill {E} [concE -< E] : ITree E α :=
  .trigger concE (.kill) >>= nofun
export ConcE (kill)

def ConcE.fork {E} [concE -< E] (child : ITree E PUnit) : ITree E PUnit :=
  .trigger concE (.fork) >>= λ
    | .child => child >>= λ _ => kill
    | .parent => return ⟨⟩
export ConcE (fork)

@[partial_fixpoint_monotone]
theorem fork_mono [concE -< E] α [PartialOrder α] (f : α → ITree E PUnit) :
  monotone f →
  monotone (λ x => fork (f x)) := by
  intro hf
  apply monotone_bind
  · apply monotone_const
  · rintro x y _ (_|_) <;> simp [PartialOrder.rel_refl]
    apply monotone_bind <;> simp [*, monotone_const]

def ConcE.yield {E} [concE -< E] : ITree E PUnit :=
  .trigger concE (.yield)
export ConcE (yield)

def ConcE.yieldAfter [concE -< E] (t : ITree E R) := do
  let v ← t; yield; return v
export ConcE (yieldAfter)

@[partial_fixpoint_monotone]
theorem yieldAfter_mono [concE -< E] α [PartialOrder α] (f : α → ITree E R) :
  monotone f →
  monotone (λ x => yieldAfter (f x)) := by
  intro hf
  apply monotone_bind
  · apply hf
  · apply monotone_const

instance concEH : EHandler concE GE GR (Nat × List (Option (ITree GE GR))) where
  handle i s k p :=
    match i with
    | .fork => p (k .parent) (s.1, s.2 ++ [some (k .child)])
    | .yield =>
      let tp' := s.2.set s.1 (some (k ⟨⟩))
      ∃ i' t', tp'[i']? = some (some t') ∧ p t' (i', tp'.set i' none)
    | .kill =>
      ∃ i' t', s.2[i']? = some (some t') ∧ p t' (i', s.2.set i' none)
  handle_mono := by
    intros i s k p q himp h; cases i
    all_goals simp at *; grind
