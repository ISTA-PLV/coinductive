import Coinductive

namespace ITree
open Coinductive Lean.Order

structure Effect : Type (u + 1) where
  I : Type u
  O : I → Type u

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

def ITree.bind {S} (t1 : ITree E R) (t2 : R → ITree E S) :=
  match t1.unfold with
  | .ret r => t2 r
  | .tau t => .tau (ITree.bind t t2)
  | .vis i k => .vis i (λ o => ITree.bind (k o) t2)
partial_fixpoint

@[partial_fixpoint_monotone]
theorem bind_mono α {S} [PartialOrder α]
  (f : α → ITree E R) (g : α → R → ITree E S) :
  monotone f →
  monotone g →
  monotone (λ x => ITree.bind (f x) (g x)) := by
    intro hf hg t1 t2 hle
    simp [PartialOrder.rel]
    have hlef : (f t1) ⊑ (f t2) := by apply hf; assumption
    -- TODO: Here we want to generalize vis_mono such that we can use it
    sorry

def ITree.iter {α β} (t : α → ITree E (α ⊕ β)) : α → ITree E β :=
  λ a => ITree.bind (t a) λ
    | .inl a => .iter t a
    | .inr b => .ret b
partial_fixpoint

def ITree.interp {F} (f : (i : E.I) → ITree F (E.O i)) : ITree E R → ITree F R :=
  ITree.iter λ t =>
    match t.unfold with
    | .ret r => .ret (.inr r)
    | .tau t => .ret (.inl t)
    | .vis i k => ITree.bind (f i) (λ o => .ret (.inl (k o)))

def f {E R} : ITree E R := f
partial_fixpoint

def spin2 {E R} : ITree E R := ITree.tau spin2
partial_fixpoint

example {E R} : @spin2 E R = spin2 := by unfold spin2; rfl

-- TODO: I did not expect this to work. I guess it works, but we cannot prove it monotone
def ITree.test (t1 : ITree E R) : ITree E R :=
  match t1.unfold with
  | .ret r => .ret r
  | .tau t => ITree.test t
  | .vis i k => .vis i (λ o => ITree.test (k o))
partial_fixpoint


end ITree
