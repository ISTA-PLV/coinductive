import Coinductive
import ITree.Effect

namespace ITree
open Coinductive Lean.Order

inductive ITreeF (E : Effect.{u}) (R : Type v) (ITree : Type w) : Type (max u v w) where
  | ret (r : R)
  | tau (t : ITree)
  | vis (i : E.I) (k : E.O i → ITree)

inductive ITreeF.In (E : Effect.{u}) (R : Type u) : Type u where
  | ret (r : R)
  | tau
  | vis (i : E.I)

instance (E : Effect.{u}) (R : Type u) : QPF (ITreeF E R) where
  PF := ⟨ITreeF.In E R, fun
    | .ret _ => PEmpty
    | .tau => PUnit
    | .vis i => E.O i⟩
  unpack
    | .ret r => .obj (.ret r) nofun
    | .tau t => .obj .tau λ _ => t
    | .vis i k => .obj (.vis i) k
  pack
    | .obj (.ret r) _ => .ret r
    | .obj .tau k => .tau (k ⟨⟩)
    | .obj (.vis i) k => .vis i k
  unpack_pack := by rintro _ ⟨⟩ <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

abbrev ITree (E : Effect.{u}) (R : Type u) : Type u := CoInd (ITreeF E R)

variable {E : Effect.{u}} {R : Type u}

def ITree.fold (t : ITreeF E R (ITree E R)) : ITree E R := CoInd.fold _ t
def ITree.ret (r : R) : ITree E R := ITree.fold (.ret r)
def ITree.tau (t : ITree E R) : ITree E R := ITree.fold (.tau t)
def ITree.vis (i : E.I) (k : E.O i → ITree E R) : ITree E R := ITree.fold (.vis i k)
def ITree.unfold (t : ITree E R) : ITreeF E R (ITree E R) := CoInd.unfold _ t

/- Ideally everything above this would be automatically generated -/

variable {E : Effect.{u}}

def ITree.spin : ITree E R := cofix _ (ITreeF.tau) PUnit.unit

instance : Inhabited (ITreeF E R PUnit) where default := .tau ⟨⟩

@[partial_fixpoint_monotone]
theorem tau_mono α [PartialOrder α] (f : α → ITree E R) :
  monotone f →
  monotone (λ x => ITree.tau (f x)) := by
    intro hf t1 t2 hle
    simp [PartialOrder.rel, CoInd.le, ITree.tau, ITree.fold, QPF.unpack]
    right
    constructor <;> try rfl
    intro _
    apply hf
    apply hle

@[partial_fixpoint_monotone]
theorem vis_mono α [PartialOrder α] i (f : α → E.O i → ITree E R) :
  monotone f →
  monotone (λ x => ITree.vis i (f x)) := by
    intro hf t1 t2 hle
    simp [PartialOrder.rel, CoInd.le, QPF.unpack]
    right
    constructor <;> try rfl
    intro _
    apply hf
    apply hle

-- use Bind.bind instead
private def ITree.bind {S} (t1 : ITree E R) (t2 : R → ITree E S) :=
  match t1.unfold with
  | .ret r => t2 r
  | .tau t => .tau (ITree.bind t t2)
  | .vis i k => .vis i (λ o => ITree.bind (k o) t2)
partial_fixpoint

@[partial_fixpoint_monotone]
theorem bind_mono {α} {S} [PartialOrder α]
  (f : α → ITree E R) (g : α → R → ITree E S) :
  monotone f →
  monotone g →
  monotone (λ x => ITree.bind (f x) (g x)) := by
    intro hf hg t1 t2 hle
    simp [PartialOrder.rel]
    have hlef : (f t1) ⊑ (f t2) := by apply hf; assumption
    -- TODO: Here we want to generalize vis_mono such that we can use it
    sorry

instance : Monad (ITree.{u} E) where
  pure := ITree.ret
  bind := ITree.bind

instance : LawfulMonad (ITree E) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map := by simp [Functor.map]; sorry
  seqLeft_eq := by
    simp [Functor.map, SeqLeft.seqLeft, Seq.seq];
    unfold Function.const; sorry
  seqRight_eq := by
    simp [Functor.map, SeqRight.seqRight, Seq.seq]; sorry
  pure_seq := by simp [pure, Seq.seq, Functor.map]; sorry
  bind_pure_comp := by
    intros
    simp [Bind.bind, Functor.map, pure];
    unfold Function.comp; rfl
  bind_map := by simp [Bind.bind, Seq.seq, Functor.map]
  pure_bind := by simp [pure, Bind.bind]; unfold ITree.bind; simp [ITree.ret, ITree.fold, ITree.unfold]
  bind_assoc := by simp [Bind.bind]; sorry

instance : MonoBind (ITree E) where
  bind_mono_left := by
    intro _ _ _ _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => x) <;> grind [monotone, PartialOrder.rel_refl]
  bind_mono_right := by
    intro _ _ a _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => a) (λ x => x)
    · grind [monotone, PartialOrder.rel_refl]
    · grind [monotone, PartialOrder.rel_refl]
    · intro _; grind

@[simp]
theorem vis_bind i k (t : S → ITree E R) :
  (.vis i k) >>= t = .vis i (λ o => k o >>= t) := by
    simp [Bind.bind]
    rw [ITree.bind]
    simp [ITree.vis, ITree.fold, ITree.unfold]

@[simp]
theorem tau_bind t1 (t : S → ITree E R) :
  t1.tau >>= t = .tau (t1 >>= t) := by
    simp [Bind.bind]
    rw [ITree.bind]
    simp [ITree.tau, ITree.fold, ITree.unfold]

def ITree.trigger (E₁ : Effect.{u}) {E₂ : Effect.{u}} [E₁ -< E₂] (i : E₁.I) : ITree.{u} E₂ (E₁.O i) :=
  let ⟨i₂, f⟩ := (Subeffect.map i);
  ITree.vis i₂ (λ x => return (f x))

def ITree.iter {α β} (t : α → ITree E (α ⊕ β)) : α → ITree E β :=
  λ a => do
    match ← (t a) with
    | .inl a => .iter t a
    | .inr b => return b
partial_fixpoint

def ITree.interp {F} (f : (i : E.I) → ITree F (E.O i)) : ITree E R → ITree F R :=
  ITree.iter λ t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau t => return (.inl t)
    | .vis i k => f i >>= λ o => return (.inl (k o))

end ITree
