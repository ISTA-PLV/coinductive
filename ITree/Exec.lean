import ITree.Definition

namespace ITree.Exec

/--
`E` is the specific (sub)effect to handle
`GE` and `GR` are the effect and return value of the global itree (they should always be universally quantified in instances)
`σ` is the type of states of the handler
-/
structure EHandler (E GE : Effect.{u}) (GR : Type u) (σ : Type v) where
  handle : (i : E.I) → σ → (E.O i → ITree.{u} GE GR) → (ITree.{u} GE GR → σ → Prop) → Prop
  handle_mono : ∀ {i s k p q},
    handle i s k p →
    (∀ o s', p o s' → q o s') →
    handle i s k q

/-- Simple version of EHandler that does not need access to the continuation -/
structure SEHandler (E : Effect.{u}) (σ : Type v) where
  handle : (i : E.I) → σ → (E.O i → σ → Prop) → Prop
  handle_mono : ∀ {i s p q},
    handle i s p →
    (∀ o s', p o s' → q o s') →
    handle i s q

attribute [simp] EHandler.handle
attribute [simp] SEHandler.handle

@[coe]
def SEHandler.toEHandler {E GE : Effect.{u}} {GR σ : Type u} (eh : SEHandler E σ)
    : EHandler E GE GR σ where
  handle i s k p := eh.handle i s (λ o s' => p (k o) s')
  handle_mono := by grind [SEHandler.handle_mono]

/- TODO: This coercion sometimes fails to trigger, unclear why -/
instance {E GE GR σ} : Coe (SEHandler E σ) (EHandler E GE GR σ) where
  coe := SEHandler.toEHandler

@[simp]
theorem seh_to_ehandler_handle_eq_seh_handle {E GE : Effect.{u}} GR (eh : SEHandler E σ) i s k p:
    eh.toEHandler.handle (GE:=GE) (GR:=GR) i s k p = eh.handle i s (λ o s' => p (k o) s') := by
  apply propext; simp [SEHandler.toEHandler]

/-- Inclusion of EHandlers -/
class InEH {E₁ E₂ GE : Effect.{u}} {GR : Type u} {σ₁ σ₂ : Type u} [sub : E₁ -< E₂]
  (eh₁ : EHandler E₁ GE GR σ₁) (eh₂ : EHandler E₂ GE GR σ₂) where
  getState : σ₂ → σ₁
  putState : σ₁ → σ₂ → σ₂
  put_get s : putState (getState s) s = s
  get_put s s' : getState (putState s s') = s
  isIn : ∀ i s₂ k p,
    eh₁.handle i (getState s₂) k (λ t s₁' => p t (putState s₁' s₂)) →
    let ⟨i₂, o⟩ := sub.map i; eh₂.handle i₂ s₂ (λ x => k (o x)) p

attribute [simp] InEH.getState InEH.putState
attribute [simp] InEH.put_get InEH.get_put

instance inEHRefl {E GE GR σ} (eh : EHandler E GE GR σ) : InEH eh eh where
  getState := id
  putState x _ := x
  put_get := by simp
  get_put := by simp
  isIn := by intros; assumption

section exec
variable {GE : Effect.{u}} {GR σ : Type u}
variable (eh : EHandler GE GE GR σ)

inductive exec.F (exec : ITree GE GR → σ → (ITree GE GR → σ → Prop) → Prop)
    : ITree GE GR → σ → (ITree GE GR → σ → Prop) → Prop where
  | stop t s p : p t s → exec.F exec t s p
  | tau t s p : exec t s p → exec.F exec (.tau t) s p
  | step i k s p :
      eh.handle i s k (λ t' s' => exec t' s' p) →
      exec.F exec (ITree.vis i k) s p

theorem exec.F.mono exec₁ exec₂ p (t : ITree GE GR) s:
    exec.F eh exec₁ t s p →
    (∀ t s, exec₁ t s p → exec₂ t s p) →
    exec.F eh exec₂ t s p := by
  intro h himp
  cases h with
  | stop => constructor; assumption
  | tau => apply exec.F.tau; grind
  | step => apply exec.F.step; apply eh.handle_mono; assumption; grind

def exec (t : ITree GE GR) (s : σ) (p : ITree GE GR → σ → Prop) : Prop :=
  exec.F eh exec t s p
coinductive_fixpoint monotonicity fun f f' himp => by
  intro _ _ _ _; apply exec.F.mono; assumption; solve_by_elim

theorem exec.coind (q : ITree GE GR → σ → Prop) p :
    (∀ t s, q t s → exec.F eh (λ t s _ => q t s) t s p) →
    ∀ t s, q t s → exec eh t s p := by
  intros h t s hq; apply coinduct _ (λ t s p' => q t s ∧ p = p')
  · intro t s p' ⟨hq, rfl⟩;
    apply exec.F.mono
    · apply h; grind
    grind
  · constructor <;> trivial

theorem exec.strong_coind (q : ITree GE GR → σ → Prop) p :
    (∀ t s, q t s → exec.F eh (λ t s p' => exec eh t s (λ t' s' => p' t' s' ∨ q t' s')) t s p)
    → ∀ t s, q t s → exec eh t s p := by
  intros h t s hq;
  apply coinduct _ (λ t s p' => p' = p ∧ exec eh t s (λ t' s' => p' t' s' ∨ q t' s'))
  · rintro t' s' p' ⟨rfl, h₁⟩; unfold exec at h₁;
    cases h₁ with
    | stop _ _ _ h₂ => cases h₂ with
      | inl h => apply exec.F.stop; exact h
      | inr _ =>
        apply exec.F.mono; apply h; assumption
        grind
    | tau => apply exec.F.tau; grind
    | step =>
      apply exec.F.step
      apply EHandler.handle_mono; assumption
      grind
  · constructor
    · rfl
    . unfold exec; apply exec.F.stop; grind

theorem exec.fold (t : ITree GE GR) (s : σ) (p : ITree GE GR → σ → Prop)
    : exec.F eh (exec eh) t s p = exec eh t s p := by
  symm; apply eq_def

theorem exec.stop (t : ITree GE GR) s p :
    p t s → exec eh t s p := by
  intros h; unfold exec; apply exec.F.stop; exact h

theorem exec.step (i : GE.I) (k : GE.O i → ITree GE GR) s p :
    eh.handle i s k (λ t' s' => exec eh t' s' p) →
    exec eh (.vis i k) s p := by
  intros h; unfold exec; apply exec.F.step; exact h

theorem exec.dup (t : ITree GE GR) (s : σ) p :
    exec eh t s (λ t' s' => exec eh t' s' p) →
    exec eh t s p := by
  intros h
  apply coind _ (λ t s => exec eh t s (λ t' s' => exec eh t' s' p))
  · intros t s h
    unfold exec at h; cases h with
    | stop _ _ _ h =>
      unfold exec at h; apply exec.F.mono; assumption
      intros; apply exec.stop; assumption
    | tau => apply exec.F.tau; grind
    | step =>
      apply exec.F.step
      apply EHandler.handle_mono; assumption
      grind
  · assumption

theorem exec.mono p q (t : ITree GE GR) s :
    exec eh t s p →
    (∀ t s, p t s → q t s) →
    exec eh t s q := by
  intros he himp;
  apply coind _ (λ t s => exec eh t s p)
  · intros t s h; unfold exec at h; cases h with
    | stop => apply exec.F.stop; solve_by_elim
    | tau => apply exec.F.tau; solve_by_elim
    | step =>
      apply exec.F.step
      apply EHandler.handle_mono; assumption
      grind
  · assumption

end exec

section exec

/- Trigger -/

theorem exec.trigger {E GE : Effect.{u}} {GR σ Gσ : Type u} {i : E.I} {k : E.O i → ITree GE GR} {s p}
  [E -< GE] (eh : EHandler E GE GR σ) (ehg : EHandler GE GE GR Gσ) [hin : InEH eh ehg] :
    eh.handle i (hin.getState s) k (λ t' s' => p t' (hin.putState s' s)) →
    exec ehg (ITree.trigger E i >>= k) s p := by
  intros h; simp [ITree.trigger]
  apply exec.step
  have hi := hin.isIn _ _ _ _ h
  dsimp only at hi
  apply EHandler.handle_mono; assumption
  grind [exec.stop]

/- Bind -/

class EHandlerBind {E GE : Effect.{u}} {GR GR' : Type u} {σ} (eh : EHandler E GE GR σ) (ehb : outParam $ EHandler E GE GR' σ) where
  bind_handle i s k₁ k₂ p :
    ehb.handle i s k₁ (λ t' s' => p (t' >>= k₂) s') →
    eh.handle i s (λ x => (k₁ x) >>= k₂) p

instance eHandlerBindSimple {E GE : Effect.{u}} GR GR' σ (eh : SEHandler E σ) :
  EHandlerBind (GE:=GE) (GR:=GR) (GR':=GR') eh eh.toEHandler where
  bind_handle := by
    intros i s k₁ k₂ p h; exact h

/-- This is the default handler that gets installed if we use the bind
rule on a hander that does not support bind. It ensures that the effects from the handler cannot be used during the bind.
But other effects can still be used. For example, this is used for concurrency.
-/
def failingEH {E GE : Effect.{u}} {GR σ : Type u} : EHandler E GE GR σ where
  handle _ _ _ _ := False
  handle_mono := by grind

instance (priority := 1) eHandlerBindFailure {E GE : Effect.{u}} GR GR' σ (eh : EHandler E GE GR σ) :
  EHandlerBind eh (@failingEH E GE GR' σ) where
  bind_handle := by intros; simp_all [failingEH]


theorem exec.bind_post {GE : Effect.{u}} GR R σ (eh : EHandler GE GE GR σ) (ehb : EHandler GE GE R σ) (t : ITree GE R) (s : σ) (k : R → ITree GE GR) p [ehBind : EHandlerBind eh ehb] :
    exec ehb t s (λ t' s' => p (t' >>= k) s') →
    exec eh (t >>= k) s p := by
  intros h;
  apply coind _ (λ t s => ∃ t', t = t' >>= k ∧ exec ehb t' s (λ t'' s' => p (t'' >>= k) s'))
  · rintro _ _ ⟨t, _, hstep⟩
    subst_eqs; unfold exec at hstep; cases hstep with
    | stop => apply exec.F.stop; assumption
    | tau => simp; apply exec.F.tau; grind
    | step i k _ h =>
      simp
      apply exec.F.step
      apply ehBind.bind_handle
      apply EHandler.handle_mono; assumption
      intros o s' h₁; exists o
  · exists t

theorem exec.bind {GE : Effect.{u}} GR R σ (eh : EHandler GE GE GR σ) (ehb : EHandler GE GE R σ) (t : ITree GE R) (s : σ) (k : R → ITree GE GR) p [ehBind : EHandlerBind eh ehb] :
    exec ehb t s (λ t' s' => exec eh (t' >>= k) s' p) →
    exec eh (t >>= k) s p := by
  intros h; apply dup; apply bind_post; assumption

/- ## Instances for sums -/

def sumEH {E₁ E₂ GE GR σ₁ σ₂} (eh₁ : EHandler E₁ GE GR σ₁) (eh₂ : EHandler E₂ GE GR σ₂)
    : EHandler (E₁ ⊕ₑ E₂) GE GR (σ₁ × σ₂) where
  handle i s k p := match i with
    | .inl i => eh₁.handle i s.1 k (λ o s' => p o ⟨s', s.2⟩)
    | .inr i => eh₂.handle i s.2 k (λ o s' => p o ⟨s.1, s'⟩)
  handle_mono := by
    intros i s k p p' _ himp
    cases i with
    | inl _ =>
      simp at *
      apply eh₁.handle_mono; assumption
      grind
    | inr _ =>
      simp at *
      apply eh₂.handle_mono; assumption
      grind

notation:59 eh₁ " ⊕ₑₕ " eh₂ => sumEH eh₁ eh₂

instance (priority:=mid) sumInEHL {E₁ E₂ E₃ GE GR σ₁ σ₂ σ₃} [E₁ -< E₂] (eh₁ : EHandler E₁ GE GR σ₁) (eh₂ : EHandler E₂ GE GR σ₂) (eh₃ : EHandler E₃ GE GR σ₃)
    [hin : InEH eh₁ eh₂] :
    InEH eh₁ (eh₂ ⊕ₑₕ eh₃)  where
  getState := hin.getState ∘ Prod.fst
  putState s₁ s := (hin.putState s₁ s.fst, s.snd)
  put_get := by rintro ⟨s₂, s₃⟩; simp
  get_put := by rintro s₁ ⟨s₂, s₃⟩; simp
  isIn := by
    intros i s₂₃ k p h
    have h' := hin.isIn i s₂₃.fst k (λ t s => p t (s, s₂₃.snd))
    simp at h; have hhandle := h' h; clear h'
    apply EHandler.handle_mono; assumption
    grind

instance (priority:=low) sumInEHR {E₁ E₂ E₃ GE GR σ₁ σ₂ σ₃} [E₁ -< E₃] (eh₁ : EHandler E₁ GE GR σ₁) (eh₂ : EHandler E₂ GE GR σ₂) (eh₃ : EHandler E₃ GE GR σ₃)
    [hin : InEH eh₁ eh₃] :
    InEH eh₁ (eh₂ ⊕ₑₕ eh₃) where
  getState := hin.getState ∘ Prod.snd
  putState s₁ s := (s.fst, hin.putState s₁ s.snd)
  put_get := by rintro ⟨s₂, s₃⟩; simp
  get_put := by rintro s₁ ⟨s₂, s₃⟩; simp
  isIn := by
    intros i s₂₃ k p h; have h' := hin.isIn i s₂₃.snd k (λ t s => p t (s₂₃.fst, s))
    simp at h; have hhandle := h' h; clear h'
    apply EHandler.handle_mono; assumption
    grind

instance sumEHBind E₁ E₂ GE GR₁ GR₂ σ₁ σ₂
  (eh₁ : EHandler E₁ GE GR₁ σ₁) (eh₂ : EHandler E₂ GE GR₁ σ₂)
  (ehb₁ : EHandler E₁ GE GR₂ σ₁) (ehb₂ : EHandler E₂ GE GR₂ σ₂)
  [ib₁ : EHandlerBind eh₁ ehb₁] [ib₂ : EHandlerBind eh₂ ehb₂]
    : EHandlerBind (eh₁ ⊕ₑₕ eh₂) (ehb₁ ⊕ₑₕ ehb₂) where
  bind_handle := by
    intros i s k₁ k₂ p h
    match i with
    | .inl i =>
      unfold EHandler.handle at h |-; simp [sumEH] at *;
      apply ib₁.bind_handle; assumption
    | .inr i =>
      unfold EHandler.handle at h |-; simp [sumEH] at *;
      apply ib₂.bind_handle; assumption

def sumSEH {E₁ E₂ σ₁ σ₂} (eh₁ : SEHandler E₁ σ₁) (eh₂ : SEHandler E₂ σ₂)
    : SEHandler (E₁ ⊕ₑ E₂) (σ₁ × σ₂)
  where
  handle i s p := match i with
    | .inl i => eh₁.handle i s.fst (λ o s' => p o ⟨s', s.2⟩)
    | .inr i => eh₂.handle i s.snd (λ o s' => p o ⟨s.1, s'⟩)
  handle_mono := by
    intros i s p p' _ himp
    match i with
    | .inl i =>
      simp at *
      apply eh₁.handle_mono; assumption
      grind
    | .inr i =>
      simp at *
      apply eh₂.handle_mono; assumption
      grind

notation:50 eh₁ " ⊕ₛₑₕ " eh₂ => sumSEH eh₁ eh₂

instance (priority:=mid) sumInSEHL {E₁ E₂ E₃ GE : Effect.{u}} {GR σ₁ σ₂ σ₃ : Type u} [E₁ -< E₂] (eh₁ : EHandler E₁ GE GR σ₁) (eh₂ : SEHandler E₂ σ₂) (eh₃ : SEHandler E₃ σ₃)
    [hin : InEH eh₁ eh₂.toEHandler] :
    InEH eh₁ (eh₂ ⊕ₛₑₕ eh₃).toEHandler where
  getState := hin.getState ∘ Prod.fst
  putState s₁ s := (hin.putState s₁ s.fst, s.snd)
  put_get := by rintro ⟨s₂, s₃⟩; simp
  get_put := by rintro s₁ ⟨s₂, s₃⟩; simp
  isIn := by
    intros i s₂₃ k p h; simp at *;
    have h' := hin.isIn i (s₂₃.fst) k (λ t s₂ => p t ⟨s₂, s₂₃.snd⟩) h
    apply SEHandler.handle_mono; assumption
    grind

instance (priority:=low) sumInSEHR {E₁ E₂ E₃ GE : Effect.{u}} {GR σ₁ σ₂ σ₃ : Type u} [E₁ -< E₃] (eh₁ : EHandler E₁ GE GR σ₁) (eh₂ : SEHandler E₂ σ₂) (eh₃ : SEHandler E₃ σ₃)
    [hin : InEH eh₁ eh₃.toEHandler] :
    InEH eh₁ (eh₂ ⊕ₛₑₕ eh₃).toEHandler where
  getState := hin.getState ∘ Prod.snd
  putState s₁ s := (s.fst, hin.putState s₁ s.snd)
  put_get := by rintro ⟨s₂, s₃⟩; simp
  get_put := by rintro s₁ ⟨s₂, s₃⟩; simp
  isIn := by
    intros i s₂₃ k p h; simp at *;
    have h' := hin.isIn i (s₂₃.snd) k (λ t s₃ => p t ⟨s₂₃.fst, s₃⟩) h
    apply SEHandler.handle_mono; assumption
    grind

/-- EHandler isomorphism -/
structure Iso (α β : Type _) where
  toFun : α → β
  invFun : β → α
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

@[simp, grind =]
theorem toFun_invFun {α β} (iso : Iso α β) s :
  iso.toFun (iso.invFun s) = s := by grind [iso.left_inv, iso.right_inv]

@[simp, grind =]
theorem invFun_toFun {α β} (iso : Iso α β) s :
  iso.invFun (iso.toFun s) = s := by grind [iso.left_inv, iso.right_inv]

def isoEH {E GE R σ₁ σ₂} (iso : Iso σ₁ σ₂) (eh : EHandler E GE R σ₁) : EHandler E GE R σ₂ where
  handle i s k p := eh.handle i (iso.invFun s) k (λ t s' => p t (iso.toFun s'))
  handle_mono := by grind [EHandler.handle_mono]

instance {E E' GE GR σ₁ σ₂ σ'} (iso : Iso σ₁ σ₂) (eh : EHandler E GE GR σ₁) (eh' : EHandler E' GE GR σ') [E' -< E]
  [hin : InEH eh' eh]:
  InEH eh' (isoEH iso eh) where
  getState s := hin.getState (iso.invFun s)
  putState s x := iso.toFun $ hin.putState s (iso.invFun x)
  put_get := by simp
  get_put := by simp
  isIn := by grind [isoEH, hin.isIn]

/- EHandler interp -/
section interp
variable {E₁ E₂ : Effect.{u}} (f : (i : E₁.I) → ITree E₂ (E₁.O i))

def interpEH {σ} (eh : SEHandler E₂ σ) : SEHandler E₁ σ where
  handle i s p := exec eh (f i) s λ r s' => ∃ v, r = pure v ∧ p v s'
  handle_mono he h := by grind [exec.mono]

theorem exec_interpEH {GE : Effect.{u}} GR σ σ₂ (ehf : SEHandler E₂ σ₂) i p s
    {k : E₁.O i → ITree GE GR}
    [E₁ -< GE] (eh : EHandler GE GE GR σ) [hin : InEH (interpEH f ehf).toEHandler eh] :
      (exec ehf (f i) (hin.getState s) λ r s' => ∃ v, r = pure v ∧ exec eh (k v) (hin.putState s' s) p) →
      exec eh (ITree.trigger E₁ i >>= k) s p := by
  rintro he
  apply exec.dup
  apply exec.trigger (interpEH f ehf).toEHandler
  simp_all [interpEH]

/- TODO: everything below here is work in progress -/

class EHandlerParametric {E GR σ₁ σ₂ GE₁ GE₂}
  (rel : ITree GE₁ GR → ITree GE₂ GR → Prop)
  (eh₁ : EHandler E GE₁ GR σ₁) (eh₂ : EHandler E GE₂ GR σ₂) where
  state_rel : σ₁ → σ₂ → Prop
  handle_rel i s₁ s₂ k₁ k₂ p :
    state_rel s₁ s₂ →
    (∀ o, rel (k₁ o) (k₂ o))  →
    eh₁.handle i s₁ k₁ p →
    eh₂.handle i s₂ k₂ λ t₂' s₂' =>
      ∃ t₁' s₁', state_rel s₁' s₂' ∧ rel t₁' t₂' ∧ p t₁' s₁'


-- class EHandlerInterp {GR σ₁ σ₂ GE₁ GE₂} [E₂ -< GE₂]
--   (f : (i : E₁.I) → ITree E₂ (E₁.O i))
--   (Gf : (i : GE₁.I) → ITree GE₂ (GE₁.O i))
--   (eh₁ : EHandler E₁ GE₁ GR σ₁) (eh₂ : EHandler E₂ GE₂ GR σ₂) where
--   state_rel : σ₁ → σ₂ → Prop
--   handle_rel₁ i s₁ s₂ k p :
--     state_rel s₁ s₂ →
--     eh₁.handle i s₁ k p →
-- -- TODO: introduce an exec! that takes an [EHandler E GE GR σ] and a contiuation from R to ITree GE GR? It can also force the ehandler to result in .ret instead of an arbitrary itree maybe?
--     exec eh₂ (ITree.interp (ITree.trigger _) (f i) >>= λ o => ITree.interp Gf (k o)) s₂ λ t' s' => True

def inl_ {E' : Effect.{u}} :
  (i : (E₁ ⊕ₑ E').I) → ITree (E₂ ⊕ₑ E') ((E₁ ⊕ₑ E').O i)
  -- The tau is necessary to ensure that we always do at least one step when interpreting
  | .inl x => ITree.tau (ITree.interp (ITree.trigger E₂) (f x))
  | .inr x => ITree.trigger E' x

theorem exec_interp_1 σ σ₁ σ₂ E' GR (t : ITree (E₁ ⊕ₑ E') GR) p s s₁ s₂
  (ehf : SEHandler E₂ σ) (eh₁ : EHandler E' (E₁ ⊕ₑ E') GR σ₁)
  (eh₂ : EHandler E' (E₂ ⊕ₑ E') GR σ₂)
  [ehp : EHandlerParametric (ITree.interp (inl_ f) · = ·) eh₁ eh₂]:
  ehp.state_rel s₁ s₂ →
  (exec (ehf.toEHandler ⊕ₑₕ eh₂) (ITree.interp (inl_ f) t) (s, s₂) p) →
  exec ((interpEH f ehf).toEHandler ⊕ₑₕ eh₁) t (s, s₁) λ t' s' => ∃ s₂', ehp.state_rel s'.2 s₂' ∧ p (ITree.interp (inl_  f) t') (s'.1, s₂') := by
  intro hrel he
  apply exec.coind _ λ t s => ∃ s₂, ehp.state_rel s.2 s₂ ∧ exec (ehf ⊕ₑₕ eh₂) (ITree.interp (inl_ f) t) (s.1, s₂) p
  rotate_left 1; grind
  rintro t s ⟨s₂, hrel, he⟩
  cases t <;> simp at he
  · sorry
  · -- apply exec.F.tau
    sorry
  · sorry

theorem exec_interp_2 σ σ₁ σ₂ E' GR (t : ITree (E₁ ⊕ₑ E') GR) p s s₁ s₂
  (ehf : SEHandler E₂ σ) (eh₁ : EHandler E' (E₁ ⊕ₑ E') GR σ₁)
  (eh₂ : EHandler E' (E₂ ⊕ₑ E') GR σ₂)
  [ehp : EHandlerParametric (ITree.interp (inl_ f) · = ·) eh₁ eh₂]:
  ehp.state_rel s₁ s₂ →
  (exec ((interpEH f ehf).toEHandler ⊕ₑₕ eh₁) t (s, s₁) p) →
  exec (ehf.toEHandler ⊕ₑₕ eh₂) (ITree.interp (inl_ f) t) (s, s₂) λ t' s' =>    ∃ s₁' t'', ehp.state_rel s₁' s'.2 ∧
    t' = ITree.interp (inl_ f) t'' ∧ p t'' (s'.1, s₁') := by
  intro hrel he
  apply exec.strong_coind _ λ t s =>
    ∃ s₁ t', ehp.state_rel s₁ s.2 ∧ t = ITree.interp (inl_ f) t' ∧
    exec ((interpEH f ehf).toEHandler ⊕ₑₕ eh₁) t' (s.1, s₁) p
  rotate_left 1; grind
  rintro _ s ⟨_, _, hrel, rfl, he⟩
  unfold exec at he
  cases he
  · apply exec.F.stop; grind
  · simp
    apply exec.F.tau
    apply exec.stop
    grind
  · rename_i i k hh
    simp
    cases i <;> simp [inl_]
    · -- the tau in inl_ is necessary here
      apply exec.F.tau
      apply exec.bind
      rw (occs:=[1]) [sumEH] at hh
      simp at hh
      rw (occs:=[1]) [interpEH] at hh
      simp at hh
      sorry
    · unfold ITree.trigger
      simp
      apply exec.F.step
      rw (occs:=[1]) [sumEH]
      simp
      apply EHandler.handle_mono
      . apply ehp.handle_rel
        . assumption
        . intro o; rfl
        . assumption
      intro _ _ _
      apply exec.stop
      grind


end interp
