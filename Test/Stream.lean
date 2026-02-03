import Coinductive

namespace Stream
open Coinductive Lean.Order

inductive StreamF (α : Type w) (Stream : Type w) : Type w where
  | snil
  | scons (x : α) (tl : Stream)

inductive StreamF.In (α : Type u) : Type u where
  | snil
  | scons (x : α)

instance (α : Type u) : QPF (StreamF α) where
  PF := ⟨StreamF.In α, fun
    | .snil => PEmpty
    | .scons _ => PUnit⟩
  unpack
    | .snil => .obj (.snil) nofun
    | .scons hd tl => .obj (.scons hd) λ _ => tl
  pack
    | .obj (.snil) _ => .snil
    | .obj (.scons hd) tl => .scons hd (tl ⟨⟩)
  unpack_pack := by rintro _ (_|_) <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

abbrev Stream (α : Type u) : Type u := CoInd (StreamF α)

def Stream.fold (t : StreamF α (Stream α)) : Stream α := CoInd.fold _ t
def Stream.snil {α : Type u} : Stream α := Stream.fold (.snil)
def Stream.scons {α : Type u} (hd : α) (tl : Stream α) : Stream α := Stream.fold (.scons hd tl)

instance : Inhabited (StreamF α PUnit) where default := .snil

@[partial_fixpoint_monotone]
theorem scons_mono β α [PartialOrder β] i (f : β → Stream α) :
  monotone f →
  monotone (λ x => Stream.scons i (f x)) := by
    intro hf t1 t2 hle
    simp [PartialOrder.rel, CoInd.le, QPF.unpack]
    right
    constructor <;> try rfl
    intro _
    apply hf
    apply hle

def Stream.map {α} (f : α → β) (s : Stream α) : Stream β :=
  match s.unfold with
  | .snil => .snil
  | .scons hd tl => .scons (f hd) (Stream.map f tl)
partial_fixpoint

@[partial_fixpoint_monotone]
theorem map_mono α β γ [PartialOrder γ] (f : α → β) (g : γ → Stream α) :
  monotone g →
  monotone (λ x => Stream.map f (g x)) := by
    intro hf t1 t2 hle
    simp [PartialOrder.rel, CoInd.le, QPF.unpack]
    sorry


def Stream.stail {α} (s : Stream α) : Stream α :=
  match s.unfold with
  | .snil => .snil
  | .scons _ tl => tl

@[partial_fixpoint_monotone]
theorem stail_mono β α [PartialOrder β] (f : β → Stream α) :
  monotone f →
  monotone (λ x => Stream.stail (f x)) := by
    intro hf t1 t2 hle
    simp [PartialOrder.rel, CoInd.le, QPF.unpack]
    sorry

def s3 : Stream Nat :=
  .scons 0 $ .scons 1 $ .stail s3
partial_fixpoint

def s3' : Stream Nat :=
  .stail s3'
partial_fixpoint
