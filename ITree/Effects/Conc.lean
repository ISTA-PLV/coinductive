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

structure ConcState GE GR where
  curr : Nat
  pool : List (Option (ITree GE GR))
  curr_in_pool : curr < pool.length
  curr_is_none : pool[curr] = none

attribute [grind! .] ConcState.curr_in_pool

def ConcState.add {GE GR} (s : ConcState GE GR) (t : ITree GE GR) : ConcState GE GR where
  curr := s.curr
  pool := s.pool ++ [some t]
  curr_in_pool := by grind
  curr_is_none := by grind [curr_is_none]

def ConcState.yield {GE GR} (tp : List (Option (ITree GE GR))) (i : Nat) (h : i < tp.length) : ConcState GE GR where
  curr := i
  pool := tp.set i none
  curr_in_pool := by grind
  curr_is_none := by grind

@[simp]
theorem ConcState.yield_id {GE GR} (s : ConcState GE GR) t h :
  yield (s.pool.set s.curr t) s.curr h = s := by
  simp [yield]
  congr
  grind [List.set_getElem_self, curr_is_none]

@[simp]
def ConcState.next {GE GR} (tp : List (Option (ITree GE GR))) (C : ITree GE GR → ConcState GE GR → Prop) : Prop :=
  ∃ i t, ∃ (h : i < tp.length), tp[i] = some t ∧ C t (yield tp i h)

def concEH {GE GR} : EHandler concE GE GR (ConcState GE GR) where
  handle i s k p :=
    match i with
    | .fork => p (k .parent) (s.add (k .child))
    | .yield =>
      let tp' := s.pool.set s.curr (some (k ⟨⟩))
      ConcState.next tp' p
    | .kill =>
      ConcState.next s.pool p
  handle_mono := by
    intros i s k p q himp h; cases i
    all_goals simp at *; grind

theorem exec_yield_yielded {GE : Effect.{u}} {GR σ} (next : Nat)
    {k : PUnit → ITree GE GR} [concE -< GE]
    (eh : EHandler GE GE GR σ)
    [hin : InEH concEH eh] s p t :
    let ss := hin.getState s;
    let tp' := ss.pool.set ss.curr (k ⟨⟩);
    (h : next < tp'.length) →
    tp'[next] = some t →
    exec eh t (hin.putState (ConcState.yield tp' next h) s) p →
    exec eh (yield >>= k) s p := by
  dsimp only
  rintro h htp he; simp [yield]
  apply exec.dup
  apply exec.trigger concEH
  rw (occs := [1]) [concEH.eq_def]
  simp
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  constructor <;> assumption
  grind

theorem exec_yield_same {GE : Effect.{u}} {GR σ}
    {k : PUnit → ITree GE GR} [concE -< GE]
    (eh : EHandler GE GE GR σ)
    [hin : InEH concEH eh] s p :
    exec eh (k ⟨⟩) s p →
    exec eh (yield >>= k) s p := by
  rintro he
  apply exec_yield_yielded ((InEH.getState concEH eh s).curr)
  · rw [List.getElem_set_self]; grind
  simp [he]
