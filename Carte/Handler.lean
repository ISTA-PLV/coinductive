import Iris.BI
import Iris.ProofMode
import Iris.Algebra.IProp
import Iris.Instances.IProp
import ITree.Definition

open Iris BI ITree

/-
  An [iHandler] is the user-specified recipe used to define a custom
  weakest precondition [WPi]. It specifies how to interpret an event
  logically, given weakest preconditions for continuations of the itree.
-/
structure iHandler GF (E : Effect.{u}) where
  ihandle :
      (i : E.I) →
      -- Continuation conditions [λ a, ▷ WPi k a @ H; ∅ {{ Φ }}]
      (E.O i → IProp GF) →
      -- Conditions for spawning threads [λ a, ▷ WPi k a @ H; ⊤ {{ False }}]
      (E.O i → IProp GF) →
      -- Condition [WPi (Vis i k) @ H; ∅ {{ Φ }}]
      IProp GF

  ihandle_mono :
    ∀ (i : E.I) (Φ Φ' s s' : E.O i → IProp GF),
      (∀ a, Φ a -∗ Φ' a) ⊢
      □ (∀ t, s t -∗ s' t) -∗
      ihandle i Φ s -∗ ihandle i Φ' s'

-- TODO: define pointwise_relation
-- Global Instance handler_ne Σ E n (H : iHandler Σ E) A :
--   Proper (pointwise_relation _ (pointwise_relation _ (dist n) ==> pointwise_relation _ (dist n) ==> dist n)) (ihandle _ _ H A).
-- Proof.
--   intros e Φ1 Φ2 HΦ s1 s2 Hs.
--   assert (Hmon : ∀ Φ s, (H A e Φ s ⊣⊢ ∃ Φ' s', (∀ a, Φ' a -∗ Φ a) ∗ □ (∀ a, s' a -∗ s a) ∗ H A e Φ' s')).
--   - iIntros (Φ s). iSplit.
--     * iIntros "HH". iExists Φ, s. iSplitR; first eauto. by iSplitR; first eauto.
--     * iIntros "[%Φ' [%s' [HmonΦ [Hmons HH]]]]". by iApply (ihandler_mono with "HmonΦ Hmons").
--   - rewrite !Hmon. repeat f_equiv.
-- Qed.

-- An [iHandler] for sum events [E1 +' E2] delegating to respective [iHandler]s.
def sumH {GF E₁ E₂} (H1 : iHandler GF E₁) (H2 : iHandler GF E₂) : iHandler GF (E₁ ⊕ₑ E₂) where
  ihandle := by
    intro e Φ s
    cases e with
    | inl e1 => exact H1.ihandle e1 Φ s
    | inr e2 => exact H2.ihandle e2 Φ s
  ihandle_mono := by
    iintro %e %Φ %Φ' %s %s' HΦwand #Hswand HH
    cases e with
    | inl e1 =>
      simp; iapply H1.ihandle_mono (i := e1) (Φ := Φ) (Φ' := Φ') (s := s) (s' := s') $$ [HΦwand]
      . iintro %x H'; ispecialize HΦwand $$ %x; iapply HΦwand $$ H'
      . imodintro; iintro %t H'; ispecialize Hswand $$ %t; iapply Hswand $$ H'
      . iexact HH
    | inr e2 =>
      simp; iapply H2.ihandle_mono (i := e2) (Φ := Φ) (Φ' := Φ') (s := s) (s' := s') $$ [HΦwand]
      iintro %x H'; ispecialize HΦwand $$ %x; iapply HΦwand $$ H'
      . imodintro; iintro %t H'; ispecialize Hswand $$ %t; iapply Hswand $$ H'
      . iexact HH
infixr:30 " ⊕ₕ " => sumH

/- `[inH H1 H2]` means that `H2` restricts to `H1` along the subeffect embedding. -/
class inH {GF E₁ E₂} [f : E₁ -< E₂] (H1 : iHandler GF E₁) (H2 : iHandler GF E₂) where
  is_inH : ∀ (i : E₁.I) (Φ s : E₁.O i → IProp GF),
    let ⟨j, back⟩ := f.map i
    H2.ihandle j (fun x => Φ (back x)) (fun x => s (back x)) ⊣⊢ H1.ihandle i Φ s

instance inH_reflexivity {GF E} (H : iHandler GF E) : inH H H where
  is_inH := by
    intro i Φ s; simp

instance sumH_inH_l {GF E₁ E₂ E₃} [f : E₁ -< E₂]
  (H1 : iHandler GF E₁) (H2 : iHandler GF E₂) (H3 : iHandler GF E₃) :
  inH H1 H2 → inH H1 (H2 ⊕ₕ H3) := by
    intro Hin
    refine ⟨?_⟩
    intro i Φ s
    simpa [sumH] using (inH.is_inH (H1 := H1) (H2 := H2) (f := f) i Φ s)

instance sumH_inH_r {GF E₁ E₂ E₃} [f : E₁ -< E₃]
    (H1 : iHandler GF E₁) (H2 : iHandler GF E₂) (H3 : iHandler GF E₃) :
    inH H1 H3 →
    inH H1 (H2 ⊕ₕ H3) := by
  intro Hin
  refine ⟨?_⟩
  intro i Φ s
  simpa [sumH] using (inH.is_inH (H1 := H1) (H2 := H3) (f := f) i Φ s)

/- `[wandH H1 H2]` means that `H1` implies `H2` -/
class wandH {GF E} (H1 : iHandler GF E) (H2 : iHandler GF E) where
  is_wandH : ∀ (i : E.I) (Φ s : E.O i → IProp GF),
    ⊢ H1.ihandle i Φ s -∗ H2.ihandle i Φ s

instance wandH_reflexivity {GF E} (H : iHandler GF E) : wandH H H := by
  refine ⟨?_⟩
  iintro %i %Φ %s H
  iexact H

instance sumH_wandH {GF E₁ E₂} (H1 H1' : iHandler GF E₁) (H2 H2' : iHandler GF E₂) :
  wandH H1 H1' → wandH H2 H2' → wandH (H1 ⊕ₕ H2) (H1' ⊕ₕ H2') := by
    intro Hwand1 Hwand2
    refine ⟨?_⟩
    iintro %e %Φ %s H
    cases e with
    | inl e1 =>
      simp [sumH] at *
      iapply Hwand1.is_wandH $$ H
    | inr e2 =>
      simp [sumH] at *
      iapply Hwand2.is_wandH $$ H

/- `Sequential` handlers ignore the spawning continuation and do not model concurrency. -/
class Sequential {GF : BundledGFunctors} {E : Effect} (H : iHandler GF E) where
  is_seq : ∀ (i : E.I) (Φ s : E.O i → IProp GF),
    ⊢ H.ihandle i Φ s -∗ H.ihandle i Φ (fun _ => iprop(⌜False⌝))

-- TODO: `iapply` does not work, needed to find the reason
instance sumH_Sequential {GF E₁ E₂} (H1 : iHandler GF E₁) (H2 : iHandler GF E₂)
  [Hs1 : Sequential H1] [Hs2 : Sequential H2] : Sequential (H1 ⊕ₕ H2) := by
    refine ⟨?_⟩
    iintro %e %Φ %s H
    cases e with
    | inl e1 =>
        simp [sumH] at *
        -- iapply Hs1.is_seq $$ H
        sorry
    | inr e2 =>
        simp [sumH] at *
        -- iapply Hs2.is_seq $$ H
        sorry
