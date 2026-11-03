/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree.Effect
public import ITree.Definition
public import ITree.Effects.Demonic
public import ITree.Effects.Fail
public import ITree.Effects.State
public import Std.Data.ExtTreeMap

@[expose] public section
namespace ITree.Effects

/-- Heap locations with integer offsets and laws supporting fresh block allocation.
Offsets use `Int` so programs can express negative displacements. -/
class LawfulLoc (Loc : Type u) [Ord Loc] extends Zero Loc, HAdd Loc Int Loc where
  decEq : DecidableEq Loc
  add_zero (l : Loc) : l + (0 : Int) = l
  add_nat_inj (l : Loc) (i j : Int) : (l + i) + j = l + (i + j)
  add_pos_gt (l : Loc) (m : Nat) : compare (l + (1 + m : Int)) l = .gt

attribute [instance_reducible, instance] LawfulLoc.decEq

protected abbrev heapE.T (Loc : Type u) [Ord Loc] (Val : Type u) :=
  Std.ExtTreeMap Loc (Option Val)
abbrev heapE (Loc : Type u) [Ord Loc] (Val : Type u) :=
  stateE (heapE.T Loc Val)
abbrev heapEH (Loc : Type u) [Ord Loc] (Val : Type u) :=
  stateEH (heapE.T Loc Val)

variable {E : Effect.{u}} {Loc : Type u} [Ord Loc] [Std.TransOrd Loc] {Val : Type u}

def HeapE.storeOpt [heapE Loc Val -< E] (l : Loc) (v : Option Val) : ITree E (Option Val) := do
  let hmap ← get
  set (hmap.insert l v)
  return hmap[l]?.join
export HeapE (storeOpt)

def HeapE.store? [heapE Loc Val -< E] (l : Loc) (v : Val) : ITree E (Option Val) :=
  storeOpt l (some v)
export HeapE (store?)

def HeapE.store! [heapE Loc Val -< E] [failE -< E] (l : Loc) (v : Val) : ITree E Val := do
  let some v ← store? l v
    | fail "Storing in unallocated memory"
  return v
export HeapE (store!)

def HeapE.load? [heapE Loc Val -< E] (l : Loc) : ITree E (Option Val) := do
  let hmap ← get
  return hmap[l]?.join
export HeapE (load?)

def HeapE.load! [heapE Loc Val -< E] [failE -< E] (l : Loc) : ITree E Val := do
  let some v ← load? l
    | fail "Loading from unallocated memory"
  return v
export HeapE (load!)

instance inhabited_free_locs [LawfulLoc Loc]
    {n} (hmap : heapE.T Loc Val) :
    Inhabited { l : Loc // ∀ m : Nat, m < n → l + (m : Int) ∉ hmap } where
  default := by
    cases Hmax : (hmap.maxKey?)
    · simp [hmap.maxKey?_eq_none_iff] at Hmax; simp [Hmax]
      exact ⟨0, trivial⟩
    · rename_i kmax
      simp [hmap.maxKey?_eq_some_iff_getKey?_eq_self_and_forall] at Hmax
      obtain ⟨_, Hmax⟩ := Hmax; refine ⟨kmax + (1 : Int), ?_⟩
      intro m _ Hmem
      simpa [LawfulLoc.add_nat_inj, LawfulLoc.add_pos_gt] using Hmax _ Hmem

def HeapE.allocN [heapE Loc Val -< E] [demonicE Loc -< E]
    [LawfulLoc Loc] (n : Nat) (v : Val) : ITree E Loc := do
  let hmap ← get
  let ⟨l, _⟩ ← choose (fun l : Loc => ∀ m : Nat, m < n → l + (m : Int) ∉ hmap)
  set (hmap.insertMany <| (List.range n).map fun m => ⟨l + (m : Int), some v⟩)
  return l
export HeapE (allocN)

def HeapE.alloc [heapE Loc Val -< E] [demonicE Loc -< E]
    [LawfulLoc Loc] (v : Val) : ITree E Loc :=
  allocN 1 v
export HeapE (alloc)
