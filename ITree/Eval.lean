/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree.Definition

@[expose] public section
namespace ITree.Eval

class MHandler (E : Effect.{u}) (T : Type u) (m : Type u → Type u) [Monad m] where
  handle : (i : E.I) → (k : E.O i → T) → m T

class SMHandler (E : Effect.{u}) (m : Type u → Type u) [Monad m] where
  handle : (i : E.I) → m (E.O i)

instance SMHandler.toMHandler {E : Effect.{u}} {T : Type u} {m : Type u → Type u} [Monad m] [SMHandler E m]
    : MHandler E T m where
  handle i k := SMHandler.handle i >>= (pure $ k ·)

/- TODO: Should we require a MonoBind instance and define this using partial fixpoint? This would allow us to prove stuff about this definition. -/
partial def eval {GE : Effect.{u}} {GR : Type u} (m : Type u → Type u) [Monad m] [MHandler GE (ITree GE GR) m] [Inhabited GR] (t : ITree GE GR) : m GR :=
  match t.unfold with
  | .ret r => return r
  | .tau t => eval m t
  | .vis i k => MHandler.handle i k >>= eval m

partial def evalNGo {GE : Effect.{u}} {GR : Type u} (m : Type u → Type u) [Monad m] [mh : MHandler GE ((n : Nat) × (ITreeN GE GR n)) m] :
  (n : Nat) → (Coinductive.CoIndN (ITreeF GE GR) n) → m (Option GR)
  | 0, _ => return none
  | _+1, .ret r => return some r
  | n+1, .tau t => evalNGo m n t
  | _+1, .vis i k => mh.handle i (λ o => ⟨_, k o⟩) >>=
    λ o => let ⟨n, t⟩ := o; evalNGo m n t

def evalN {GE : Effect.{u}} {GR : Type u} (m : Type u → Type u) [Monad m] [MHandler GE ((n : Nat) × (ITreeN GE GR n)) m] (n : Nat) (t : ITree GE GR) : m (Option GR) := evalNGo m n (t.approx n)

instance sumMH {E₁ E₂ : Effect.{u}} {m T} [Monad m] [mh₁ : MHandler E₁ T m] [mh₂ : MHandler E₂ T m]
    : MHandler (E₁ ⊕ₑ E₂) T m where
  handle i k := match i with
    | .inl i => MHandler.handle i k
    | .inr i => MHandler.handle i k

instance sumSMH {E₁ E₂ : Effect} {m} [Monad m] [mh₁ : SMHandler E₁ m] [mh₂ : SMHandler E₂ m]
    : SMHandler (E₁ ⊕ₑ E₂) m where
  handle i := match i with
    | .inl i => mh₁.handle i
    | .inr i => mh₂.handle i
