/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ITree
public import HeapLang.Lang

@[expose] public section
namespace HeapLang

open ITree ITree.Effects ITree.Exec

def Val.int! [failE -< E] : Val → ITree E Int
  | .lit (.int i) => return i
  | x => fail s!"{reprStr x} is not Int"

def Val.bool! [failE -< E] : Val → ITree E Bool
  | .lit (.bool b) => return b
  | x => fail s!"{reprStr x} is not Bool"

def Val.loc! [failE -< E] : Val → ITree E Loc
  | .lit (.loc l) => return l
  | x => fail s!"{reprStr x} is not Loc"

def Val.pair! [failE -< E] : Val → ITree E (Val × Val)
  | .pair v1 v2 => return (v1, v2)
  | x => fail s!"{reprStr x} is not Pair"

def Val.rec! [failE -< E] : Val → ITree E (Binder × Binder × Exp)
  | .rec_ f x e => return (f, x, e)
  | x => fail s!"{reprStr x} is not Rec"

def Val.injL! [failE -< E] : Val → ITree E Val
  | .injL v => return v
  | x => fail s!"{reprStr x} is not InjL"

def Val.injR! [failE -< E] : Val → ITree E Val
  | .injR v => return v
  | x => fail s!"{reprStr x} is not InjR"

abbrev heaplangE := concE ⊕ₑ heapE Loc Val ⊕ₑ failE ⊕ₑ demonicE Loc ⊕ₑ stepE

structure HeaplangState (T : Type) : Type where
  tp : ConcState T
  heap : heapE.T Loc Val
  steps : Nat
  steps_left : Nat

@[simp]
def HeaplangStateIso T : Iso (ConcState T × heapE.T Loc Val × PUnit × PUnit × (ULift Nat × ULift Nat)) (HeaplangState T) where
  toFun x := ⟨x.1, x.2.fst, ULift.down x.2.2.2.2.1, ULift.down x.2.2.2.2.2⟩
  invFun x := ⟨x.tp, x.heap, ⟨⟩, ⟨⟩, ⟨ULift.up x.steps, ULift.up x.steps_left⟩⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

abbrev heaplangEH {GE GR} (nl : Nat → Nat) : EHandler heaplangE GE GR (HeaplangState (ITree GE GR)) :=
  isoEH (HeaplangStateIso (ITree GE GR)) (concEH ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH Loc ⊕ₛₑₕ stepEH nl).toEHandler)

/- TODO: define EHandlerBind -/
-- instance {GE GR GR'} : EHandlerBind (GE:=GE) (GR:=GR) (GR':=GR')
  -- heaplangEH (failingEH ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH (List Loc)).toEHandler) := inferInstanceAs (EHandlerBind (concEH ⊕ₑₕ _) _)

abbrev heaplangM := StateT (ConcState ((n : Nat) × ITreeN heaplangE Val n)) (StateT (heapE.T Loc Val) (ExceptT String IO))

instance : MonadEval heaplangM IO where
  monadEval x := do
    let r ← x |>.run (ConcState.new) |>.run ∅
    match r with
    | .ok v => return v.1.1
    | .error msg => IO.ofExcept $ .error (s!"Evaluation failed: {msg}")


def UnOp.denote (op : UnOp) (v : Val) : ITree heaplangE Val :=
  match op, v with
  | .neg, .lit (.bool b) => return .lit (.bool !b)
  | .neg, .lit (.int n) => return .lit (.int (~~~n))
  | .minus, .lit (.int n) => return .lit (.int (-n))
  | _, _ => fail "UnOp: type mismatch"

def BinOp.evalInt (op : BinOp) (n₁ n₂ : Int) : Option BaseLit :=
  match op with
  | .plus => some $ .int (n₁ + n₂)
  | .minus => some $ .int (n₁ - n₂)
  | .mult => some $ .int (n₁ * n₂)
  | .tdiv => some $ .int (Int.tdiv n₁ n₂)
  | .tmod => some $ .int (Int.tmod n₁ n₂)
/- TODO: get rid of the toNat and define the operations directly on Int -/
  | .and => some $ .int (Nat.land n₁.toNat n₂.toNat : Nat)
  | .or => some $ .int (Nat.lor n₁.toNat n₂.toNat : Nat)
  | .xor => some $ .int (Nat.xor n₁.toNat n₂.toNat : Nat)
  | .shiftl => some $ .int (n₁ <<< n₂.toNat)
  | .shiftr => some $ .int (n₁ >>> n₂.toNat)
  | .le => some $ .bool (decide (n₁ ≤ n₂))
  | .lt => some $ .bool (decide (n₁ < n₂))
  | .eq => some $ .bool (decide (n₁ = n₂))
  | .offset => none

def BinOp.evalBool (op : BinOp) (b₁ b₂ : Bool) : Option BaseLit :=
  match op with
  | .and => some $ .bool (b₁ && b₂)
  | .or => some $ .bool (b₁ || b₂)
  | .xor => some $ .bool (Bool.xor b₁ b₂)
  | .eq => some $ .bool (decide (b₁ = b₂))
  | _ => none

def BinOp.evalLoc (op : BinOp) (l₁ : Loc) (v₂ : BaseLit) : Option BaseLit :=
  match op, v₂ with
  | .offset, .int off => some $ .loc (l₁ + off)
  | .le, .loc l₂ => some $ .bool (decide (l₁.n ≤ l₂.n))
  | .lt, .loc l₂ => some $ .bool (decide (l₁.n < l₂.n))
  | _, _ => none

def BinOp.denote (op : BinOp) (v₁ v₂ : Val) : ITree heaplangE Val :=
  if op == .eq then
    if Val.compareSafe v₁ v₂ then
      return .lit (.bool (decide (v₁ = v₂)))
    else
      fail "EqOp: comparing boxed values"
  else
    match v₁, v₂ with
    | .lit (.int n₁), .lit (.int n₂) => do
      let .some l := BinOp.evalInt op n₁ n₂
        | fail "BinOp: invalid int operation"
      return .lit l
    | .lit (.bool b₁), .lit (.bool b₂) => do
      let some l := BinOp.evalBool op b₁ b₂
        | fail "BinOp: invalid bool operation"
      return .lit l
    | .lit (.loc l₁), .lit v₂ => do
      let some l := BinOp.evalLoc op l₁ v₂
        | fail "BinOp: invalid loc operation"
      return .lit l
    | _, _ => fail "BinOp: type mismatch"

def Exp.yieldIfNotVal : Exp → ITree heaplangE Unit
  | .val _ => return ()
  | _ => yield

/- TODO: check all the yields and add step -/
def Exp.denote (e : Exp) : ITree heaplangE Val :=
  let denoteYield e :=
    if e.isVal then denote e else yieldAfter (denote e)
  match e with
  | .val v => return v
  | .var x => fail s!"Unbound variable {reprStr x}"
  | .rec_ f x e => do step; return .rec_ f x e
  | .app e₁ e₂ => do
    let v ← denoteYield e₂
    let f ← denoteYield e₁
    let ⟨f', x', e⟩ ← f.rec!
    let body := e.subst f' f |>.subst x' v
    step
    body.yieldIfNotVal
    denote body
  | .unop op e => do
    let v ← denoteYield e
    let r ← op.denote v
    step
    return r
  | .binop op e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let r ← op.denote v₁ v₂
    step
    return r
  | .if e₀ e₁ e₂ => do
    let c ← denoteYield e₀
    if ← c.bool! then
      step
      denoteYield e₁
    else
      step
      denoteYield e₂
  | .pair e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    step
    return .pair v₁ v₂
  | .fst e => do
    let v ← denoteYield e
    let p ← v.pair!
    step
    return p.1
  | .snd e => do
    let v ← denoteYield e
    let p ← v.pair!
    step
    return p.2
  | .injL e => do
    let v ← denoteYield e
    step
    return .injL v
  | .injR e => do
    let v ← denoteYield e
    step
    return .injR v
  | .case e₀ e₁ e₂ => do
    let v ← denoteYield e₀
    match v with
    | .injL w => step; yield; denote (.app e₁ (.val w))
    | .injR w => step; yield; denote (.app e₂ (.val w))
    | _ => fail "Case: not a sum value"
  | .allocN e₁ e₂ => do
    let v ← denoteYield e₂
    let vn ← denoteYield e₁
    let n ← vn.int!
    if n ≤ 0 then fail "AllocN: count must be positive"
    let l ← HeapE.allocN n.toNat v (by
      -- TODO: move this proof somewhere else?
      intro l m
      simp [compare, compareOfLessAndEq, Ordering.isLE]
      grind)
    step
    return .lit (.loc l)
  | .free e => do
    let v ← denoteYield e
    let l ← v.loc!
    let .some _ ← storeOpt (Val:=Val) l none
      | fail "free: location not allocated"
    step
    return .lit .unit
  | .load e => do
    let v ← denoteYield e
    let r ← load! (← v.loc!)
    step
    return r
  | .store e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let _ ← store! (← v₁.loc!) v₂
    step
    return .lit .unit
  | .cmpXchg e₀ e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let v₀ ← denoteYield e₀
    let l ← v₀.loc!
    let vl ← load! l
    if !Val.compareSafe vl v₁ then
      fail "CmpXchg: comparing boxed values"
    if vl = v₁ then
      let _ ← store! l v₂
      step
      return .pair vl (.lit (.bool true))
    else
      step
      return .pair vl (.lit (.bool false))
  | .xchg e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let r ← store! (← v₁.loc!) v₂
    step
    return r
  | .faa e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let l ← v₁.loc!
    let i₂ ← v₂.int!
    let old ← load! l
    let i₁ ← old.int!
    let _ ← store! l (.lit (.int (i₁ + i₂)) : Val)
    step
    return old
  | .fork e => do
    let _ ← ConcE.fork (denoteYield e >>= λ _ => return ⟨⟩)
    step
    return .lit .unit
  | .newProph => do
    fail "prophecy is not implemented"
  | .resolve _ _ _ => do
    fail "prophecy is not implemented"
partial_fixpoint
