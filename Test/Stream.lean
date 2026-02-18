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

@[simp]
theorem snil_approx_1 α n :
  (Stream.snil (α:=α)).approx (n + 1) = StreamF.snil := by
    simp [Stream.snil, Stream.fold, CoInd.fold, QPF.map, QPF.pack]

@[simp]
theorem scons_approx_1 α i (s : Stream α) n :
  (Stream.scons i s).approx (n + 1) = StreamF.scons i (s.approx n) := by
    simp [Stream.scons, Stream.fold, CoInd.fold, QPF.map, QPF.pack]

@[simp]
theorem unfold_snil α :
  CoInd.unfold _ Stream.snil = StreamF.snil (α:=α) := by
    simp [Stream.snil, Stream.fold]

@[simp]
theorem unfold_scons α (i : α) s:
  CoInd.unfold _ (Stream.scons i s) = StreamF.scons i s := by
    simp [Stream.scons, Stream.fold]

instance : Inhabited (StreamF α PUnit) where default := .snil

@[simp]
theorem Stream.bot_eq α :
  CoInd.bot (StreamF α) = Stream.snil := by
    rw [CoInd.bot_eq]
    simp [QPF.map, QPF.pack, Stream.snil, Stream.fold]


theorem Stream.le_unfold α (s1 s2 : Stream α) :
  (s1 ⊑ s2) = (s1 = .snil ∨
    ∃ i s1' s2', s1 = .scons i s1' ∧ s2 = .scons i s2' ∧ s1' ⊑ s2') := by
    ext
    constructor
    · intro h
      rw [CoInd.le_unfold] at h
      rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp
      rw [<-unfold_fold _ s1, <-unfold_fold _ s2]
      rw [<-QPF.unpack_pack s1.unfold, <-QPF.unpack_pack s2.unfold]
      simp only [h1, h2]
      cases i <;> simp [QPF.pack, snil, scons, fold]
      right
      exists ?_, ?_; rotate_left 1
      constructor; rfl
      apply Exists.intro
      constructor; rfl
      simp_all
    · rintro (rfl|⟨_, _, _, rfl, rfl, _⟩)
      · simp [CoInd.le_unfold]
      · simp [CoInd.le_unfold]
        right
        simp [QPF.unpack]
        constructor <;> try rfl
        grind

theorem scons_monoN α i (s1 s2 : Stream α) n :
  CoIndN.le _ (s1.approx n) (s2.approx n) →
  CoIndN.le _ ((Stream.scons i s1).approx (n + 1))
    ((Stream.scons i s2).approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, QPF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem scons_mono β α [PartialOrder β] i (f : β → Stream α) :
  monotone f →
  monotone (λ x => Stream.scons i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply scons_monoN
    grind [CoInd.leN_le, monotone]

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
    apply CoInd.le_leN
    intro n
    dsimp only
    have hs : (g t1) ⊑ (g t2) := by grind [monotone]
    generalize g t1 = s1, g t2 = s2 at hs
    induction n generalizing s1 s2; simp [CoIndN.le]
    unfold Stream.map
    rw [Stream.le_unfold] at hs
    rcases hs with ⟨_|_⟩
    · simp [CoIndN.le, CoIndN.bot]
    next h =>
    rcases h with ⟨_, _, _, _, _, _⟩
    simp [*]
    apply scons_monoN
    grind


def Stream.stail {α} (s : Stream α) : Stream α :=
  match s.unfold with
  | .snil => .snil
  | .scons _ tl => tl

@[partial_fixpoint_monotone]
theorem stail_mono β α [PartialOrder β] (f : β → Stream α) :
  monotone f →
  monotone (λ x => Stream.stail (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    cases n; simp [CoIndN.le]
    have hs : (f t1) ⊑ (f t2) := by grind [monotone]
    generalize f t1 = s1, f t2 = s2 at hs
    unfold Stream.stail
    rw [Stream.le_unfold] at hs
    rcases hs with ⟨_|_⟩
    · simp [CoIndN.le, CoIndN.bot]
    next h =>
    rcases h with ⟨_, _, _, _, _, _⟩
    simp [*]
    grind [CoInd.leN_le]

def s3 : Stream Nat :=
  .scons 0 $ .scons 1 $ .stail s3
partial_fixpoint

def s3' : Stream Nat :=
  .stail s3'
partial_fixpoint
