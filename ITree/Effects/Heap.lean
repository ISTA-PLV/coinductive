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

/- TODO: can we make this an instance? -/
@[reducible]
def inhabited_free_locs {n} (hmap : heapE.T Loc Val) [Zero Loc] [HAdd Loc Int Loc] [Std.LawfulEqOrd Loc] (hlt : ∀ (l : Loc) (m : Nat), ¬(compare (l + (1 : Int) + (m : Int)) l).isLE) : Inhabited { l // ∀ (m : Nat), m < n → (l : Loc) + (m : Int) ∉ hmap } where
  default := ⟨match hmap.maxKey? with | some n => n + (1 : Int) | none => 0, by
    intro m hm
    cases h : (hmap.maxKey?) <;>
      simp [hmap.maxKey?_eq_none_iff,
        hmap.maxKey?_eq_some_iff_mem_and_forall] at h <;> simp [h]
    next max =>
    have ⟨_, h⟩ := h;
    intros contra
    replace contra := h _ contra
    grind
  ⟩

def HeapE.allocN [heapE Loc Val -< E] [demonicE Loc -< E] [Zero Loc] [HAdd Loc Int Loc] [Std.LawfulEqOrd Loc] (n : Nat) (v : Val) (hle : ∀ (l : Loc) (m : Nat), ¬(compare (l + (1 : Int) + (m : Int)) l).isLE = true) : ITree E Loc := do
  let hmap ← get
  let ⟨l, _⟩ ← choose (hi := inhabited_free_locs hmap hle) (λ l : Loc => ∀ m : Nat, m < n → l + (m : Int) ∉ hmap)
  set (hmap.insertMany $ (List.range n).map λ m => ⟨l + (m : Int), some v⟩)
  return l
export HeapE (allocN)

def HeapE.alloc [heapE Loc Val -< E] [demonicE Loc -< E] [Zero Loc] [HAdd Loc Int Loc] [Std.LawfulEqOrd Loc]
  (v : Val) (hle : ∀ (l : Loc) (m : Nat), ¬(compare (l + (1 : Int) + (m : Int)) l).isLE = true) : ITree E Loc := allocN 1 v hle
export HeapE (alloc)
