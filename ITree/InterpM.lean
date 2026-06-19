module

public import ITree.Definition

/-!
# Monadic Interpretation of ITrees (`interpM`)

`ITree.interpM` interprets an `ITree E R` into any monad `m` equipped with a loop/iteration
operator (`MonadIter`).

This generalises `ITree.interp` (which targets only another ITree) to arbitrary monads,
matching the `interp` function from the Rocq library.

## Main declarations

* `MonadIter`: typeclass for monads with a loop/iteration combinator
* `LawfulMonadIter`: a lawful iter combinator can be unfolded
* `ITree.interpM`: interpret an `ITree E R` into any `MonadIter`-monad

Additionally, instances of (`Lawful`)`MonadIter` are provided for:
* `ITree E`, and
* `StateT σ m`, assuming that `m` has a (`Lawful`)`MonadIter` instance,

## References

* Rocq InteractionTrees library:
  <https://deepspec.github.io/InteractionTrees/master/ITree.Basics.Basics.html#MonadIter>
-/

@[expose] public section
namespace ITree

/-! ## MonadIter Classes -/

/--
`MonadIter m` indicates that `m` is a monad with a loop/iteration combinator.
-/
class MonadIter (m : Type u → Type u) where
  /--
  `iter f init` is a loop/iteration combinator.

  The precise meaning is defined by the `MonadIter` instance on the monad `m`,
  but the intention is that this runs the function `f` repeatedly, starting from
  initial state `init`, where:

  - if `f` returns `inl a`, the loop continues from the new state `a`, and
  - if `f` returns `inr b`, the loop terminates and returns the result `b`.
  -/
  iter : {α β : Type u} → (f : α → m (α ⊕ β)) → (init : α) → m β
open MonadIter (iter)

/--
A `MonadIter` satisfying the unfolding equation: one step of `iter` peels off
one call to `f`, then either loops (`.inl`) or returns (`.inr`).
-/
class LawfulMonadIter (m : Type u → Type u) [Monad m] [MonadIter m] : Prop where
  iter_eq : ∀ {α β : Type u} (f : α → m (α ⊕ β)) (init : α),
    MonadIter.iter f init =
      f init >>= fun
        | .inl a => MonadIter.iter f a
        | .inr b => return b

variable {E : Effect.{u}} {R : Type u}
variable {m : Type u → Type u} [Monad m] [MonadIter m]

section Instances

/-! ### ITree -/

/-- `ITree` is a (lawful) `MonadIter`. -/
instance : MonadIter (ITree E) where iter := ITree.iter

@[simp] theorem ITree.iter_eq : @MonadIter.iter (ITree E) _ α β = ITree.iter := by rfl

instance : LawfulMonadIter (ITree E) where
  iter_eq f a := by simp; grind [ITree.iter]

/-! ### StateT -/
section State
variable {σ : Type u} {m : Type u → Type u} [Monad m] [Functor m] [MonadIter m]

/-- `StateT σ m` is a (lawful) `MonadIter` when `m` is, threading the state through each step. -/
instance : MonadIter (StateT σ m) where
  iter f a s :=
    MonadIter.iter (init := (a, s)) <| fun (a, s) =>
      (fun (ba, s) => ba.map (·, s) (·, s)) <$> (f a).run s

omit [Monad m] in
@[simp, grind =] theorem StateT.run_iter {f : α → StateT σ m (α ⊕ β)}  :
    StateT.run (iter (m := StateT σ m) f a) s
    = iter (fun (a, s) => (fun (ba, s) => ba.map (·, s) (·, s)) <$> (f a).run s) (a, s) := by
  rfl

instance {σ : Type u} {m : Type u → Type u} [Monad m] [LawfulMonad m]
    [MonadIter m] [LawfulMonadIter m] : LawfulMonadIter (StateT σ m) where
  iter_eq f a := by
    grind [LawfulMonadIter.iter_eq, bind_assoc, =_ bind_pure_comp]

end State
end Instances

/-! ## Monadic ITree Interpretation -/
namespace ITree

/--
Map an `ITree E R` into a generic monad `m` equiped with a `MonadIter` instance,
using handler `h` to interpret effects.
-/
def interpM (h : (i : E.I) → m (E.O i)) : ITree E R → m R :=
  MonadIter.iter fun t =>
    match t.unfold with
    | .ret r   => return (.inr r)
    | .tau t'  => return (.inl t')
    | .vis i k => h i >>= fun o => return (.inl (k o))

section Lemmas
variable [LawfulMonad m] [LawfulMonadIter m] (h : (i : E.I) → m (E.O i))

@[simp, grind =] theorem interpM_ret (r : R) :
    interpM h (ret r) = return r := by
  rw [interpM, LawfulMonadIter.iter_eq]; simp

@[simp, grind =] theorem interpM_tau (t : ITree E R) :
    interpM h (tau t) = interpM h t := by
  rw [interpM, LawfulMonadIter.iter_eq]; simp

@[simp, grind =] theorem interpM_vis (i : E.I) (k : E.O i → ITree E R) :
    interpM h (vis i k) = h i >>= fun o => interpM h (k o) := by
  rw [interpM, LawfulMonadIter.iter_eq]; simp

end Lemmas
end ITree
end ITree
