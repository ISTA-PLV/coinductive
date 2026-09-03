/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree.Effect
public import ITree.Definition
public import ITree.Exec
public import ITree.Eval

@[expose] public section
namespace ITree.Effects
open Lean.Order

inductive ForkResult : Type u
| parent | child

inductive concE.I : Type u where
| fork | kill | yield

@[implicit_reducible]
def concE : Effect.{u} where
  I := concE.I
  O
  | .fork => ForkResult
  | .kill => PEmpty
  | .yield => PUnit

universe u
unif_hint where
  |- concE.{u}.O .fork ≟ ForkResult.{u}
unif_hint where
  |- concE.{u}.O .kill ≟ PEmpty
unif_hint where
  |- concE.{u}.O .yield ≟ PUnit

def ConcE.kill {E} [concE -< E] : ITree E α :=
  concE.trigger (.kill) >>= nofun
export ConcE (kill)

def ConcE.fork {E} [concE -< E] (child : ITree E PUnit) : ITree E PUnit :=
  concE.trigger (.fork) >>= λ
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
  concE.trigger (.yield)
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

structure ConcState (T : Type u) where
  curr : Nat
  pool : List (Option T)
  curr_in_pool : curr < pool.length
  curr_is_none : pool[curr] = none

attribute [grind! .] ConcState.curr_in_pool

def ConcState.new {T} : ConcState T where
  curr := 0
  pool := [none]
  curr_in_pool := by grind
  curr_is_none := by grind

def ConcState.add {T} (s : ConcState T) (t : T) : ConcState T where
  curr := s.curr
  pool := s.pool ++ [some t]
  curr_in_pool := by grind
  curr_is_none := by grind [curr_is_none]

def ConcState.yield {T} (tp : List (Option T)) (i : Nat) (h : i < tp.length) : ConcState T where
  curr := i
  pool := tp.set i none
  curr_in_pool := by grind
  curr_is_none := by grind

@[simp]
theorem ConcState.yield_id {T} (s : ConcState T) t h :
  yield (s.pool.set s.curr t) s.curr h = s := by
  simp [yield]
  congr
  grind [List.set_getElem_self, curr_is_none]

@[simp]
def ConcState.next {T} (tp : List (Option T)) (C : T → ConcState T → Prop) : Prop :=
  ∃ i t, ∃ (h : i < tp.length), tp[i] = some t ∧ C t (yield tp i h)

/- n ensures that we stop after going one round through tp -/
def ConcState.next_roundrobin {T} (n : Nat) (curr : Nat) (tp : List (Option T)) (h : n ≤ tp.length) : Option (T × ConcState T) :=
  match n with
  | 0 => none
  | n+1 =>
    let c := (curr + 1) % tp.length;
    have := @Nat.mod_lt (curr + 1) tp.length
    match tp[c] with
    | none => next_roundrobin n c tp (by grind)
    | some t => (t, yield tp c (by grind))

section Exec
open ITree.Exec

def concEH {GE GR} : EHandler concE GE GR (ConcState (ITree GE GR)) where
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
end Exec

section Eval
open ITree.Eval

instance concMH {m T} [Monad m] [MonadExceptOf String m] [MonadStateOf (ConcState T) m] : MHandler concE T m where
  handle i k :=
  match i with
  | .fork => do modifyThe (ConcState T) (λ s => s.add (k .child)); return k .parent
  | .yield => do
    let s ← get;
    let s := s.add (k ⟨⟩)
    let some s' := ConcState.next_roundrobin (s.pool.length)
      s.curr s.pool (by grind)
      | throw "no thread to schedule"
    set (s'.2)
    return s'.1
  | .kill => do
    let s ← get;
    let some s' := ConcState.next_roundrobin (s.pool.length)
      s.curr s.pool (by grind)
      | throw "no thread to schedule"
    set (s'.2)
    return s'.1


end Eval
