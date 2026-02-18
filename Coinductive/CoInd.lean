namespace Coinductive

structure PFunctor : Type (u + 1) where
  In : Type u
  Out : In → Type u

-- naming follows https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf
inductive PFunctor.Obj (PF : PFunctor) (α : Type u) : Type u where
| obj (i : PF.In) (k : PF.Out i → α)
-- necessary to avoid eta expansion on this type
| obj_dummy (e : Empty)

-- This is basically the same as the Qpf in mathlib, except that we don't require F to be a functor and instead require the type to be isomorphic to a polynomial functor
class QPF (F : Type u → Type u) where
  PF : PFunctor
  unpack {α} : F α → PF.Obj α
  pack {α} : PF.Obj α → F α
  unpack_pack {α} (x : F α) : pack (unpack x) = x
  pack_unpack {α} (x : PF.Obj α) : unpack (pack x) = x

attribute [simp] QPF.unpack_pack QPF.pack_unpack

variable (F : Type u → Type u) [QPF F]

def QPF.map {α β} (f : α → β) (x : F α) : F β :=
  let .obj i k := unpack x; pack (.obj i λ x => f (k x))

@[simp]
theorem QPF.map_pack {α β} (f : α → β) i k :
  map F f (pack (.obj i k)) = pack (.obj i λ x => f (k x)) := by
    simp [map]

@[simp]
theorem QPF.unpack_map {α β} (f : α → β) x:
  unpack (map F f x) = let .obj i k := unpack x; .obj i λ x => f (k x) := by
    simp [map]
    split
    simp

@[simp]
theorem QPF.map_map {α β γ} (f : α → β) (g : β → γ) x:
  map F g (map F f x) = map F (λ x => g (f x)) x := by
    simp [map]
    rcases h : unpack x with ⟨i, k⟩ | ⟨⟨⟩⟩
    simp

def CoIndN : Nat → Type u
  | 0 => PUnit
  | n + 1 => F (CoIndN n)

inductive coherent1 {PF : PFunctor} {α1 α2 : Type u} (K : α1 → α2 → Prop) :
  PF.Obj α1 → PF.Obj α2 → Prop where
| single i i1 i2 k1 k2 :
  i1 = .obj i k1 →
  i2 = .obj i k2 →
  (∀ x, K (k1 x) (k2 x)) →
  coherent1 K i1 i2

theorem coherent1_mono {PF : PFunctor} {α1 α2 : Type u} (K1 K2 : α1 → α2 → Prop) (i1 : PF.Obj α1) i2:
  coherent1 K1 i1 i2 →
  (∀ x y, K1 x y → K2 x y) →
  coherent1 K2 i1 i2 := by
    rintro ⟨_, _, _, _⟩ himp
    constructor <;> try assumption
    grind

def coherent {n m} (c1 : CoIndN F n) (c2 : CoIndN F m) : Prop :=
  match n, m with
  | 0, _ => True
  | _, 0 => True
  | _+1, _+1 => coherent1 coherent (QPF.unpack c1) (QPF.unpack c2)

structure CoInd : Type u where
  approx : ∀ n, CoIndN F n
  is_coherent : ∀ n m, coherent F (approx n) (approx m)

@[ext]
theorem CoInd.ext (c1 c2 : CoInd F) :
  (∀ n, c1.approx n = c2.approx n) → c1 = c2 := by
    intros hn; cases c1; cases c2; congr; ext; apply hn


def CoInd.fold (x : F (CoInd F)) : CoInd F where
  approx
  | 0 => ⟨⟩
  | n + 1 => QPF.map F (λ c => c.approx n) x
  is_coherent := by
    rintro ⟨⟩ ⟨⟩ <;> simp [coherent]
    split
    constructor <;> try rfl
    simp [is_coherent]

theorem CoInd.fold_approx (x : F (CoInd F)) n:
  (CoInd.fold F x).approx (n + 1) = QPF.map F (λ c => c.approx n) x :=
    by simp [fold]

theorem coherent_eq_i (x : CoInd F) n m {i1 k1 i2 k2}:
  QPF.unpack (x.approx (n + 1)) = .obj i1 k1 →
  QPF.unpack (x.approx (m + 1)) = .obj i2 k2 →
  i1 = i2 := by
    have h := x.is_coherent (n+1) (m+1)
    simp [coherent] at h
    cases h
    grind

theorem coherent_eq_k (x : CoInd F) n m {i k1 k2 o}:
  QPF.unpack (x.approx (n + 1)) = .obj i k1 →
  QPF.unpack (x.approx (m + 1)) = .obj i k2 →
  coherent F (k1 o) (k2 o) := by
    intro h1 h2
    have h := x.is_coherent (n+1) (m+1)
    simp [coherent] at h
    cases h
    simp_all
    rcases h1 with ⟨_, _⟩
    subst_eqs
    simp [*]


def CoInd.unfold (x : CoInd F) : F (CoInd F) :=
  match h1 : QPF.unpack (x.approx 1) with
  | .obj i1 k1 =>
  QPF.pack $ .obj i1 λ o => {
    approx n :=
      match h2 : QPF.unpack (x.approx (n + 1)) with
      | .obj _ k2 => k2 (cast (congrArg _ (coherent_eq_i F x _ _ h1 h2)) o)
    is_coherent := by
      intro n m; split; split
      have := coherent_eq_i F x 0 n (by assumption) (by assumption)
      subst_eqs
      have := coherent_eq_i F x n m (by assumption) (by assumption)
      subst_eqs
      simp only [cast_eq]
      apply coherent_eq_k <;> assumption
  }

@[simp]
theorem unfold_fold x :
  CoInd.fold F (CoInd.unfold F x) = x := by
    ext n
    cases n with
    | zero => rfl
    | succ n =>
    simp [CoInd.fold, CoInd.unfold]
    split
    simp
    split
    have := coherent_eq_i F x 0 n (by assumption) (by assumption)
    subst_eqs
    simp
    rename_i h
    rw [<-h]
    simp


@[simp]
theorem fold_unfold x :
  CoInd.unfold F (CoInd.fold F x) = x := by
    simp [CoInd.unfold, CoInd.fold]
    split
    next h =>
    simp at h
    split at h
    next heq =>
    simp at h
    rcases h with ⟨_, _⟩
    subst_eqs
    rw (occs := .pos [27]) [<-(QPF.unpack_pack x)]
    rw [heq]
    congr
    funext x
    ext n
    simp
    split
    next heq2 =>
    simp [heq] at heq2
    rcases heq2 with ⟨_, _⟩
    subst_eqs
    simp


def cofix_approx {α} (f : α → F α) (a : α) : ∀ n, CoIndN F n
  | 0 => ⟨⟩
  | n+1 => QPF.map F (λ a => cofix_approx f a n) (f a)

def cofix {α} (f : α → F α) (a : α) : CoInd F where
  approx := cofix_approx F f a
  is_coherent := by
    intro n m
    induction n generalizing m a with
    | zero => simp only [coherent]
    | succ n ih =>
      cases m with
      | zero => simp only [coherent]
      | succ m =>
        simp only [cofix_approx, coherent]
        rw [QPF.unpack_map]; split
        rw [QPF.unpack_map]; split
        simp [*] at *
        rename_i h1 h2
        rcases h1 with ⟨_, _⟩; rcases h2 with ⟨_, _⟩
        subst_eqs
        constructor <;> try rfl
        grind

theorem cofix_eq {α} (f : α → F α) a :
  cofix F f a = CoInd.fold F (QPF.map F (cofix F f) (f a)) := by
    ext n
    cases n
    . rfl
    simp [cofix, CoInd.fold, cofix_approx]

section partial_order
open Lean.Order
open Classical

def CoInd.bot [Inhabited (F PUnit)] : CoInd F :=
  cofix F (λ _ : PUnit => default) ⟨⟩

theorem CoInd.bot_eq [Inhabited (F PUnit)] :
  bot F = CoInd.fold F (QPF.map F (λ _ : PUnit => bot F) default) :=
    by unfold bot; rw (occs := [1]) [cofix_eq]

def CoInd.le [Inhabited (F PUnit)] (c1 : CoInd F) (c2 : CoInd F) : Prop :=
  c1 = bot F ∨ coherent1 CoInd.le (QPF.unpack c1.unfold) (QPF.unpack c2.unfold)
coinductive_fixpoint monotonicity fun f f' himp => by
  rintro _ _ (⟨⟨⟩⟩|x)
  . simp
  . right; apply coherent1_mono <;> assumption

theorem CoInd.le.coherent_bot_eq  [Inhabited (F PUnit)] c :
  coherent1 (le F) (QPF.unpack (unfold F c))
    (QPF.unpack (unfold F (bot F))) →
  c = bot F := by
    intro h
    ext n
    induction n generalizing c h; rfl
    rw [CoInd.bot_eq]
    rw [<-unfold_fold _ c, CoInd.fold_approx]
    simp [CoInd.fold_approx]
    rw [CoInd.bot_eq] at h
    simp at h
    split at h
    rcases h
    simp_all
    rename (_ ∧ _) => h
    cases h
    subst_eqs
    grind [le, QPF.map]

instance [Inhabited (F PUnit)] : PartialOrder (CoInd F) where
  rel := CoInd.le F
  rel_refl := by
    intro c
    apply CoInd.le.coinduct _ (Eq)
    case x => grind
    intro x1 x2 h
    subst_eqs
    right
    rcases (QPF.unpack (CoInd.unfold F x1)) with ⟨_, _⟩ <;> try trivial
    constructor <;> try trivial
    simp
  rel_trans := by
    intro c1 c2 c3 _ _
    apply CoInd.le.coinduct _ (λ c1 c3 => ∃ c2, CoInd.le F c1 c2 ∧ CoInd.le F c2 c3)
    case x => grind
    rintro c1 c3 ⟨c2, h1, h2⟩
    unfold CoInd.le at h1 h2
    cases h1 with
    | inl h1 => left; subst_eqs; trivial
    | inr h1 =>
    cases h2 with
    | inl h2 =>
      grind [CoInd.le.coherent_bot_eq]
    | inr h2 =>
    right
    rcases h1 with ⟨_, _, _, _, _, _, h3⟩
    rcases h2 with ⟨⟩
    simp_all
    cases h3
    subst_eqs
    constructor <;> try rfl
    grind
  rel_antisymm := by
    intro c1 c2 h1 h2
    ext n
    induction n generalizing c1 c2 h1 h2; rfl
    unfold CoInd.le at h1 h2
    cases h1 with
    | inl h1 => grind [CoInd.le.coherent_bot_eq]
    | inr h1 =>
    cases h2 with
    | inl h2 => grind [CoInd.le.coherent_bot_eq]
    | inr h2 =>
    cases h1
    cases h2
    simp_all
    rename (_ ∧ _) => eq
    cases eq
    subst_eqs
    rw [<-unfold_fold _ c1]
    rw [<-unfold_fold _ c2]
    unfold CoInd.fold
    simp [QPF.map, *]
    grind

noncomputable def CoInd.csup [Inhabited (F PUnit)] (c : CoInd F → Prop) : CoInd F :=
  cofix F (λ c =>
    if h : ∃ t, c t ∧ t ≠ CoInd.bot F then
      let .obj i _ := QPF.unpack (choose h).unfold;
      QPF.pack $ .obj i λ o c' =>
        ∃ c0, c c0 ∧ c0 ≠ CoInd.bot F ∧
          let .obj i' k := QPF.unpack c0.unfold
          ∃ eq : i = i', c' = k (cast (congrArg _ eq) o)
    else
      QPF.map F (λ _ : PUnit => c) default
  ) c

theorem CoInd.csup_eq [Inhabited (F PUnit)] (c : CoInd F → Prop) :
  csup F c = if h : ∃ t, c t ∧ t ≠ CoInd.bot F then
      let .obj i _ := QPF.unpack (choose h).unfold
      CoInd.fold F $ QPF.pack $ .obj i λ o => csup F λ c' =>
        ∃ c0, c c0 ∧ c0 ≠ CoInd.bot F ∧
         let .obj i' k := QPF.unpack c0.unfold
         ∃ eq : i = i', c' = k (cast (congrArg _ eq) o)
    else
      CoInd.fold F $ QPF.map F (λ _ : PUnit => csup F c) default := by
  unfold csup
  rw (occs := [1]) [cofix_eq]
  repeat split <;> simp

theorem CoInd.csup_eq_bot {c} [Inhabited (F PUnit)]:
  (¬∃ t, c t ∧ t ≠ bot F) →
  CoInd.csup F c = bot F := by
    intro h
    ext n
    induction n; rfl
    next n ih =>
    rw [CoInd.bot_eq, CoInd.csup_eq]
    simp [*, fold_approx]

theorem CoInd.le_unfold [Inhabited (F PUnit)] c1 c2 :
  (c1 ⊑ c2) = (c1 = bot F ∨ coherent1 (PartialOrder.rel) (QPF.unpack c1.unfold) (QPF.unpack c2.unfold)) := by simp [PartialOrder.rel, CoInd.le]

theorem CoInd.le_chain_step [Inhabited (F PUnit)] c c1 c2 i1 k1 i2 k2:
  c c1 →
  c c2 →
  chain c →
  c1 ≠ bot F →
  c2 ≠ bot F →
  QPF.unpack (unfold F c1) = .obj i1 k1 →
  QPF.unpack (unfold F c2) = .obj i2 k2 →
  ∃ eq : i1 = i2, (∀ o, k1 o ⊑ k2 (cast (congrArg _ eq) o) ∨ k2 (cast (congrArg _ eq) o) ⊑ k1 o) := by
    intros _ _ hc _ _ _ _
    obtain h | h := hc c1 c2 (by assumption) (by assumption)
    . simp [CoInd.le_unfold, *] at h
      cases h
      simp_all
      rename (_ ∧ _) => h
      cases h
      subst_eqs
      rename (_ ∧ _) => h
      cases h
      subst_eqs
      grind
    . simp [CoInd.le_unfold, *] at h
      cases h
      simp_all
      rename (_ ∧ _) => h
      cases h
      subst_eqs
      rename (_ ∧ _) => h
      cases h
      subst_eqs
      grind

theorem CoInd.csup_step {c} [Inhabited (F PUnit)] t i k:
  c t →
  chain c →
  t ≠ bot F →
  QPF.unpack t.unfold = .obj i k →
  CoInd.csup F c = CoInd.fold F (QPF.pack $ .obj i
    λ o => CoInd.csup F λ c' => ∃ c0, c c0 ∧ c0 ≠ CoInd.bot F ∧
        let .obj i' k := QPF.unpack c0.unfold
        ∃ eq : i = i', c' = k (cast (congrArg _ eq) o)) := by
    intro ht hc _ _
    rw [CoInd.csup_eq]
    split; rotate_left 1; grind
    next h =>
    split
    next i' _ _ =>
    obtain _ : i = i' := by grind [CoInd.le_chain_step]
    subst_eqs
    congr


theorem CoInd.csup_spec [Inhabited (F PUnit)] {c : CoInd F → Prop}
    (hc : chain c) :
    is_sup c (CoInd.csup F c) := by
  intro x
  constructor
  · intro hsup t ht
    apply PartialOrder.rel_trans; rotate_left 1; assumption
    apply le.coinduct _ (λ c1 c2 => ∃ c, c c1 ∧ chain c ∧ c2 = csup F c); rotate_left 1; grind
    rintro c1 c2 ⟨c, hc1, hc, heq⟩
    subst_eqs
    by_cases (c1 = bot F)
    . grind
    right
    rcases h : (QPF.unpack (unfold F c1)); rotate_left 1; trivial
    rw [CoInd.csup_step F c1] <;> try trivial
    simp
    constructor <;> try trivial
    intro
    apply (Exists.intro _)
    and_intros; rotate_left 2; rfl
    . grind
    rintro x y ⟨c1, _, _, hm1⟩ ⟨c2, _, _, hm2⟩
    grind [CoInd.le_chain_step]
  · intro _
    apply le.coinduct _ (λ c1 c2 => ∃ c, chain c ∧ c1 = csup F c ∧ (∀ (y : CoInd F), c y → y ⊑ c2)); rotate_left 1; grind
    rintro c1 c2 ⟨c, hc, heq, hc2⟩
    subst_eqs
    by_cases h : ∃ t, c t ∧ t ≠ CoInd.bot F
    . right
      rcases h with ⟨t, _, _⟩
      cases h : (QPF.unpack (unfold F t)) <;> try trivial
      rw [CoInd.csup_step F t] <;> try trivial
      cases h2 : (QPF.unpack (unfold F c2)) <;> try trivial
      simp
      have heq := hc2 t (by assumption)
      rw [CoInd.le_unfold] at heq
      simp [*] at heq
      rcases heq
      simp_all
      rename (_ ∧ _) => h
      cases h
      subst_eqs
      rename (_ ∧ _) => h
      cases h
      subst_eqs
      constructor <;> try trivial
      intro _
      apply (Exists.intro _)
      and_intros; rotate_left 1; rfl
      . rintro _ ⟨c', _, _, hm⟩
        split at hm
        rcases hm
        subst_eqs
        simp
        have heq := hc2 c' (by assumption)
        rw [CoInd.le_unfold] at heq
        simp [*] at heq
        rcases heq
        simp_all
        rename (_ ∧ _) => h
        cases h
        subst_eqs
        grind
      rintro x y ⟨c1, _, _, hm1⟩ ⟨c2, _, _, hm2⟩
      grind [CoInd.le_chain_step]
    . grind [CoInd.csup_eq_bot]

noncomputable instance (priority := default + 100) [Inhabited (F PUnit)] : CCPO (CoInd F) where
  has_csup {c} ch := .intro (CoInd.csup F c) (CoInd.csup_spec F ch)

section CoIndN_le

theorem coherent_unfold_eq_i (x : CoInd F) n {i1 k1 i2 k2}:
  QPF.unpack (x.approx (n + 1)) = .obj i1 k1 →
  QPF.unpack (x.unfold) = .obj i2 k2 →
  i1 = i2 := by
    simp [CoInd.unfold]
    split
    simp
    grind [coherent_eq_i]

theorem coherent_unfold_eq_k (x : CoInd F) n {i k1 k2} o:
  QPF.unpack (x.approx (n + 1)) = .obj i k1 →
  QPF.unpack (x.unfold) = .obj i k2 →
  k1 o = (k2 o).approx n := by
    simp [CoInd.unfold]
    split
    simp
    rintro _ rfl rfl
    simp
    split
    simp_all
    rename (_ ∧ _) => h
    cases h
    subst_eqs
    simp

def CoIndN.bot [Inhabited (F PUnit)] (n : Nat) : CoIndN F n :=
  (CoInd.bot F).approx n

theorem CoIndN.bot.eq_plus_1 [Inhabited (F PUnit)] n:
  CoIndN.bot F (n + 1) = QPF.map F (λ _ : PUnit => CoIndN.bot F n) default := by
    unfold CoIndN.bot
    rw (occs:=[1]) [CoInd.bot_eq]
    simp [CoInd.fold]

def CoIndN.le {n} [Inhabited (F PUnit)] (c1 : CoIndN F n) (c2 : CoIndN F n) : Prop :=
  match n with
  | 0 => True
  | n+1 => c1 = bot F (n+1) ∨ coherent1 CoIndN.le (QPF.unpack c1) (QPF.unpack c2)
coinductive_fixpoint monotonicity fun f f' himp => by
  rintro ⟨_|_⟩ _ _ h <;> simp at *
  cases h
  · grind
  next h =>
  right; cases h; constructor <;> try assumption
  intro _; apply himp; grind

theorem CoInd.le_leN [Inhabited (F PUnit)] (c1 c2 : CoInd F) :
  (∀ n, CoIndN.le F (c1.approx n) (c2.approx n)) →
  c1 ⊑ c2 := by
    intro hn;  apply CoInd.le.coinduct _ (λ c1 c2 => (∀ n, CoIndN.le F (c1.approx n) (c2.approx n)))
    rotate_right 1; grind
    intro c1 c2 ih
    by_cases hbot : (c1 = CoInd.bot F); grind
    right
    by_cases hex : (∃ n, c1.approx n ≠ CoIndN.bot F n)
    · rcases hex with ⟨n, hn⟩
      cases n; contradiction
      next n =>
      have h := ih (n+1)
      simp [CoIndN.le] at h
      cases h; grind
      next h =>
      cases h
      cases h1 : (QPF.unpack (CoInd.unfold F c1))
      cases h2 : (QPF.unpack (CoInd.unfold F c2))
      have := coherent_unfold_eq_i F c1 n (by assumption) (by assumption)
      have := coherent_unfold_eq_i F c2 n (by assumption) (by assumption)
      subst_eqs
      constructor <;> try rfl
      rotate_left 1
      · rename Empty => h; cases h
      · rename Empty => h; cases h
      intro o m
      have h := ih (m + 1)
      simp [CoIndN.le] at h
      cases h
      · cases _ : (QPF.unpack $ c1.approx (m + 1))
        rotate_left 1
        · rename Empty => h; cases h
        have := coherent_unfold_eq_i F c1 m (by assumption) (by assumption)
        subst_eqs
        have hk := coherent_unfold_eq_k F c1 m o (by assumption) (by assumption)
        rw [<-hk]
        clear hk
        simp_all [CoIndN.bot.eq_plus_1]
        split at *
        simp_all
        rename (_ ∧ _) => h
        cases h
        subst_eqs
        cases m <;> simp [CoIndN.le]
      next h =>
      cases h
      have := coherent_eq_i F c1 n m (by assumption) (by assumption)
      subst_eqs
      have := coherent_unfold_eq_k F c1 m o (by assumption) (by assumption)
      have := coherent_unfold_eq_k F c2 m o (by assumption) (by assumption)
      grind
    · false_or_by_contra
      apply hbot
      ext n
      false_or_by_contra
      next h =>
      apply hex
      exists n

theorem CoInd.leN_le [Inhabited (F PUnit)] (c1 c2 : CoInd F) n :
  c1 ⊑ c2 →
  CoIndN.le F (c1.approx n) (c2.approx n) := by
    induction n generalizing c1 c2 <;> simp [CoIndN.le]
    next n ih =>
    intro hc
    rw [CoInd.le_unfold] at hc
    cases hc
    · simp_all [CoIndN.bot]
    next h =>
    cases h
    right
    cases _ : (QPF.unpack $ c1.approx (n + 1))
    rotate_left 1
    · rename Empty => h; cases h
    cases _ : (QPF.unpack $ c2.approx (n + 1))
    rotate_left 1
    · rename Empty => h; cases h
    have := coherent_unfold_eq_i F c1 n (by assumption) (by assumption)
    have := coherent_unfold_eq_i F c2 n (by assumption) (by assumption)
    subst_eqs
    constructor <;> try rfl
    intro o
    have := coherent_unfold_eq_k F c1 n o (by assumption) (by assumption)
    have := coherent_unfold_eq_k F c2 n o (by assumption) (by assumption)
    grind

end CoIndN_le
end partial_order
