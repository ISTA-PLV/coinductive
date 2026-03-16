# Coinductive

A Lean 4 library for coinductive types using polynomial functors. These coinductive types are then used to define interaction trees.

**NOTE**: This library is in early development and thus incomplete and subject to change.

## Overview

This library provides:

- **`Coinductive`** — A general coinductive type construction. Any functor isomorphic to a polynomial functor (`PF`) gets a coinductive fixpoint `CoInd F`, equipped with a fold/unfold isomorphism and a chain-complete partial order (CCPO).
- **`ITree`** — Interaction trees built on `Coinductive`.

## Design

The coinductive type `CoInd F` is represented as a *coherent sequence of approximations*. An element of `CoInd F` is a sequence `approx : ∀ n, CoIndN F n` where `CoIndN F n` is the `n`-step approximation, and all pairs of approximations are mutually coherent (agree on shape at every shared depth).

This is inspired by [QPFTypes](https://github.com/alexkeizer/QpfTypes) and the corresponding [thesis](https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf), but differs in the technical implementation.

The key feature of `CoInd F` is that it allows very ergonomic recursive definitions via Lean's `partial_fixpoint` construct.

## Quick Start

### Defining a coinductive type

Implement the `PF` typeclass for your functor, then use `CoInd`:

```lean
import Coinductive

-- The functor whose fixpoint is a stream
inductive StreamF (α : Type u) (S : Type u) : Type u where
  | snil
  | scons (hd : α) (tl : S)

instance (α : Type u) : PF (StreamF α) where
  P := ⟨..., ...⟩
  unpack := ...
  pack   := ...
  unpack_pack := ...
  pack_unpack := ...

abbrev Stream (α : Type u) := CoInd (StreamF α)

def Stream.fold (t : StreamF α (Stream α)) : Stream α := CoInd.fold _ t
def Stream.snil {α : Type u} : Stream α := Stream.fold (.snil)
def Stream.scons {α : Type u} (hd : α) (tl : Stream α) : Stream α := Stream.fold (.scons hd tl)

-- This instance is used to define the bottom element of the CCPO structure used by partial_fixpoint 
instance : Inhabited (StreamF α PUnit) where default := .snil
```

See `Test/Stream.lean` for the complete stream example.

### Recursive definitions

Use `partial_fixpoint` for recursive coinductive definitions. Register monotonicity
lemmas with `@[partial_fixpoint_monotone]` for your constructors:

```lean
@[partial_fixpoint_monotone]
theorem scons_mono β α [PartialOrder β] i (f : β → Stream α) :
  monotone f →
  monotone (λ x => Stream.scons i (f x)) := by
  ...

def Stream.map (f : α → β) (s : Stream α) : Stream β :=
  match s.unfold with
  | .snil        => .snil
  | .scons hd tl => .scons (f hd) (Stream.map f tl)
partial_fixpoint
```

### Using ITrees

The `partial_fixpoint` construct also works on `ITree`. Note that it is not necessary that the definition is productive (i.e. there is no tau before the recursive occurrence):
```lean
def ITree.iter {α β} (t : α → ITree E (α ⊕ β)) : α → ITree E β :=
  λ a => do
    match ← (t a) with
    | .inl a => .iter t a
    | .inr b => return b
partial_fixpoint
```

## Building

Requires Lean 4.

```
lake build
```
