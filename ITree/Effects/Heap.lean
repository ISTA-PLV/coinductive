import ITree.Effect
import ITree.Definition
import ITree.Effects.Demonic
import ITree.Effects.Fail
import ITree.Effects.State
import Std.Data.ExtTreeMap

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

def HeapE.alloc [heapE Loc Val -< E] [demonicE Loc -< E] (v : Val) : ITree E Loc := do
  let hmap ← get
  let ⟨l, _⟩ ← choose (λ l => l ∉ hmap)
  set (hmap.insert l v)
  return l
export HeapE (alloc)
