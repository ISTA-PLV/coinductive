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

instance : Inhabited (ITreeF E R PUnit) where default := .tau ⟨⟩

@[simp]
theorem ITree.unfold_fold (t : ITree E R) :
  ITree.fold (ITree.unfold t) = t := by simp [ITree.fold, ITree.unfold]

@[simp]
theorem ret_approx_1 (r : R) n :
  (ITree.ret (E:=E) r).approx (n + 1) = ITreeF.ret r := by
    simp [ITree.ret, ITree.fold, CoInd.fold, QPF.map, QPF.pack]

@[simp]
theorem fold_ret_approx_1 (r : R) n :
  (ITree.fold (ITreeF.ret (E:=E) r)).approx (n + 1) = ITreeF.ret r :=
    ret_approx_1 r n

@[simp]
theorem tau_approx_1 (t : ITree E R) n :
  t.tau.approx (n + 1) = ITreeF.tau (t.approx n) := by
    simp [ITree.tau, ITree.fold, CoInd.fold, QPF.map, QPF.pack]

@[simp]
theorem fold_tau_approx_1 (t : ITree E R) n :
  (ITree.fold (ITreeF.tau t)).approx (n + 1) = ITreeF.tau (t.approx n) :=
    tau_approx_1 t n

@[simp]
theorem vis_approx_1 i (t : E.O i → ITree E R) n :
  (ITree.vis i t).approx (n + 1) = ITreeF.vis i (λ o => (t o).approx n) := by
    simp [ITree.vis, ITree.fold, CoInd.fold, QPF.map, QPF.pack]
    rfl

@[simp]
theorem fold_vis_approx_1 i (t : E.O i → ITree E R) n :
  (ITree.fold (ITreeF.vis i t)).approx (n + 1) = ITreeF.vis i (λ o => (t o).approx n) := vis_approx_1 i t n

@[simp]
theorem unfold_ret (r : R) :
  ITree.unfold (ITree.ret r) = ITreeF.ret (E:=E) r := by
    simp [ITree.ret, ITree.fold, ITree.unfold]

@[simp]
theorem unfold_tau (t : ITree E R) :
  ITree.unfold (ITree.tau t) = ITreeF.tau t := by
    simp [ITree.tau, ITree.fold, ITree.unfold]

@[simp]
theorem unfold_vis i (t : E.O i → ITree E R) :
  ITree.unfold (ITree.vis i t) = ITreeF.vis i t := by
    simp [ITree.vis, ITree.fold, ITree.unfold]


theorem tau_monoN (t1 t2 : ITree E R) n :
  CoIndN.le _ (t1.approx n) (t2.approx n) →
  CoIndN.le _ (t1.tau.approx (n + 1)) (t2.tau.approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, QPF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem tau_mono α [PartialOrder α] (f : α → ITree E R) :
  monotone f →
  monotone (λ x => ITree.tau (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply tau_monoN
    grind [CoInd.leN_le, monotone]

theorem vis_monoN i (t1 t2 : E.O i → ITree E R) n :
  (∀ o, CoIndN.le _ ((t1 o).approx n) ((t2 o).approx n)) →
  CoIndN.le _ ((ITree.vis i t1).approx (n + 1)) ((ITree.vis i t2).approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, QPF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem vis_mono α [PartialOrder α] i (f : α → E.O i → ITree E R) :
  monotone f →
  monotone (λ x => ITree.vis i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply vis_monoN
    intro o
    have := hf t1 t2 hle o
    grind [CoInd.leN_le]

def ITree.spin : ITree E R := spin.tau
partial_fixpoint

@[simp]
theorem ITree.bot_eq :
  CoInd.bot (ITreeF E R) = ITree.spin := by
    ext n
    induction n; congr 0
    rw [CoInd.bot_eq, spin]
    simp [QPF.map, QPF.pack, CoInd.fold, *]

theorem ITree.le_unfold (t1 t2 : ITree E R) :
  (t1 ⊑ t2) = (t1 = .spin ∨
    (∃ r, t1 = .ret r ∧ t2 = .ret r) ∨
    (∃ t1' t2', t1 = .tau t1' ∧ t2 = .tau t2' ∧ t1' ⊑ t2') ∨
    (∃ i t1' t2', t1 = .vis i t1' ∧ t2 = .vis i t2' ∧ ∀ o, t1' o ⊑ t2' o)) := by
    ext
    constructor
    · intro h
      rw [CoInd.le_unfold] at h
      rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp
      rw [<-Coinductive.unfold_fold _ t1, <-Coinductive.unfold_fold _ t2]
      rw [<-QPF.unpack_pack (CoInd.unfold _ t1), <-QPF.unpack_pack (CoInd.unfold _ t2)]
      simp only [h1, h2]
      right
      cases i <;> simp [QPF.pack, ret, tau, vis, fold]
      · grind
      · grind
      · right
        right
        exists ?_, ?_; rotate_left 1
        constructor; rfl
        apply Exists.intro
        constructor; rfl
        simp_all
    · rintro (rfl| ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
      · simp [CoInd.le_unfold]
      · apply PartialOrder.rel_refl
      · simp [CoInd.le_unfold]
        right
        simp [QPF.unpack, ITree.tau, ITree.fold]
        constructor <;> try rfl
        grind
      · simp [CoInd.le_unfold]
        right
        simp [QPF.unpack, ITree.vis, ITree.fold]
        constructor <;> try rfl
        grind

-- use Bind.bind instead
private def ITree.bind {S} (t1 : ITree E R) (t2 : R → ITree E S) :=
  match t1.unfold with
  | .ret r => t2 r
  | .tau t => .tau (ITree.bind t t2)
  | .vis i k => .vis i (λ o => ITree.bind (k o) t2)
partial_fixpoint

@[simp]
theorem itree_ret_bind {S} r (t : S → ITree E R) :
  ITree.bind (.ret r) t = t r := by
    rw [ITree.bind]
    simp [ITree.ret, ITree.fold, ITree.unfold]

@[simp]
theorem itree_vis_bind {S} i k (t : S → ITree E R) :
  ITree.bind (.vis i k) t = .vis i (λ o => ITree.bind (k o) t) := by
    rw [ITree.bind]
    simp [ITree.vis, ITree.fold, ITree.unfold]

@[simp]
theorem itree_tau_bind {S} t1 (t : S → ITree E R) :
  ITree.bind (t1.tau) t = .tau (ITree.bind t1 t) := by
    rw [ITree.bind]
    simp [ITree.tau, ITree.fold, ITree.unfold]


@[partial_fixpoint_monotone]
theorem bind_mono {α} {S} [PartialOrder α]
  (f : α → ITree E R) (g : α → R → ITree E S) :
  monotone f →
  monotone g →
  monotone (λ x => ITree.bind (f x) (g x)) := by
    intro hf hg t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    have hlef : (f t1) ⊑ (f t2) := by apply hf; assumption
    generalize f t1 = t1, f t2 = t2 at hlef
    induction n generalizing t1 t2; simp [CoIndN.le]
    unfold ITree.bind
    rw [ITree.le_unfold] at hlef
    rcases hlef with (rfl|⟨_, rfl, rfl⟩|⟨_, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
    · unfold ITree.spin
      simp [CoIndN.le, CoIndN.bot]
      left
      unfold ITree.spin
      simp
      congr
      ext n
      induction n; congr 0
      unfold ITree.bind ITree.spin
      simp_all
    · rename_i x
      simp
      have := hg t1 t2 hle x
      grind [CoInd.leN_le, monotone]
    · simp
      apply tau_monoN
      grind [CoInd.leN_le, monotone]
    · simp
      apply vis_monoN
      grind [CoInd.leN_le, monotone]


instance : Monad (ITree.{u} E) where
  pure := ITree.ret
  bind := ITree.bind

instance : LawfulMonad (ITree E) := LawfulMonad.mk' (ITree E)
  (id_map := by
    simp [Functor.map]
    intro _ t
    ext n
    induction n generalizing t; congr 0
    unfold ITree.bind
    rw (occs := [2]) [<-ITree.unfold_fold t]
    split <;> simp [*])
  (pure_bind := by simp [pure, Bind.bind])
  (bind_assoc := by
    simp [Bind.bind]
    intro _ _ _ t1 t2 t3
    ext n
    induction n generalizing t1; congr 0
    rw [ITree.bind.eq_def t1]
    rw [ITree.bind.eq_def t1]
    split <;> simp [*])

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
theorem tau_bind t1 (t : S → ITree E R) :
  t1.tau >>= t = .tau (t1 >>= t) := by simp [Bind.bind]

@[simp]
theorem vis_bind i k (t : S → ITree E R) :
  (.vis i k) >>= t = .vis i (λ o => k o >>= t) := by simp [Bind.bind]


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
