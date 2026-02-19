import Lean.PrettyPrinter.Delaborator
import ITree

open ITree
open ITree.Effects
open ITree.Exec

namespace HeapLang

@[ext]
structure Loc where
  private mk ::
  private n : Int
deriving Inhabited, Repr, DecidableEq

instance : Ord Loc where
  compare l₁ l₂ := compare l₁.n l₂.n

instance : Std.TransOrd Loc where
  eq_swap := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    apply Int.instTransOrd.eq_swap
  isLE_trans := by
    intros l₁ l₂ l₃; unfold compare; unfold instOrdLoc; simp;
    apply Int.instTransOrd.isLE_trans

instance : Std.LawfulEqOrd Loc where
  eq_of_compare := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    intros h; ext; assumption

def Loc.offset (l : Loc) (i : Int) : Loc := ⟨l.n + i⟩

@[ext]
structure ProphId where
  private mk ::
  private n : Nat
deriving Inhabited, Repr, DecidableEq

inductive Binder where
  | anon
  | named (name : String)
deriving Inhabited, Repr, DecidableEq

inductive BaseLit where
  | int (n : Int)
  | bool (b : Bool)
  | unit
  | poison
  | loc (l : Loc)
  | prophecy (p : ProphId)
deriving Inhabited, Repr, DecidableEq

inductive UnOp where
  | neg
  | minus
deriving Inhabited, Repr, DecidableEq

inductive BinOp where
  /- We use "tdiv" and "tmod" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30 / -4 == 7. ("div" would return 8.) -/
  | plus | minus | mult | tdiv | tmod /- arithmetic -/
  | and | or | xor /- bitwise -/
  | shiftl | shiftr /- shifts -/
  | le | lt | eq /- relations -/
  | offset /- pointer offset -/
deriving Inhabited, Repr, DecidableEq

mutual
  inductive Exp : Type where
    /- values -/
    | val (v : Val)
    /- Base lambda calculus -/
    | var (x : String)
    | rec_ (f x : Binder) (e : Exp)
    | app (e₁ e₂ : Exp)
    /- Base types and their operations -/
    | unop (op : UnOp) (e : Exp)
    | binop (op : BinOp) (e₁ e₂ : Exp)
    | if (e₀ e₁ e₂ : Exp)
    /- Products -/
    | pair (e₁ e₂ : Exp)
    | fst (e : Exp)
    | snd (e : Exp)
    /- Sums -/
    | injL (e : Exp)
    | injR (e : Exp)
    | case (e₀ e₁ e₂ : Exp)
    /- Heap -/
    | allocN (e₁ e₂ : Exp) /- array length, initial value -/
    | free (e : Exp)
    | load (e : Exp)
    | store (e₁ e₂ : Exp)
    | cmpXchg (e₀ e₁ e₂ : Exp) /- compare exchange -/
    | xchg (e₁ e₂ : Exp) /- exchange -/
    | faa (e₁ e₂ : Exp) /- fetch and add -/
    /- Concurrency -/
    | fork (e : Exp)
    /- Prophecy -/
    | newProph
    | resolve (e₀ e₁ e₂ : Exp)
  deriving Inhabited, Repr, DecidableEq
  inductive Val : Type where
    | lit (l : BaseLit)
    | rec_ (f x : Binder) (e : Exp)
    | pair (v₁ v₂ : Val)
    | injL (v : Val)
    | injR (v : Val)
  deriving Inhabited, Repr, DecidableEq
end

def Exp.isVal : Exp → Bool
  | .val _ => true
  | _ => false

instance : Coe Nat BaseLit where
  coe n := .int n

instance : Coe Int BaseLit where
  coe n := .int n

instance : Coe Bool BaseLit where
  coe b := .bool b

instance : Coe Unit BaseLit where
  coe _ := .unit

/- TODO: this instance is sometimes not reduced away. What can we do about this? -/
@[reducible]
instance {n} : OfNat BaseLit n where
  ofNat := .int n

def Exp.substStr (x : String) (v : Val) (e : Exp) : Exp :=
  match e with
  | .val _ => e
  | .var x' => if x == x' then .val v else e
  | .rec_ f x' e => .rec_ f x' $ if .named x != f && .named x != x' then e.substStr x v else e
  | .app e₁ e₂ => .app (e₁.substStr x v) (e₂.substStr x v)
  | .unop op e' => .unop op (e'.substStr x v)
  | .binop op e₁ e₂ => .binop op (e₁.substStr x v) (e₂.substStr x v)
  | .if e₀ e₁ e₂ => .if (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .pair e₁ e₂ => .pair (e₁.substStr x v) (e₂.substStr x v)
  | .fst e' => .fst (e'.substStr x v)
  | .snd e' => .snd (e'.substStr x v)
  | .injL e' => .injL (e'.substStr x v)
  | .injR e' => .injR (e'.substStr x v)
  | .case e₀ e₁ e₂ => .case (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .allocN e₁ e₂ => .allocN (e₁.substStr x v) (e₂.substStr x v)
  | .free e' => .free (e'.substStr x v)
  | .load e' => .load (e'.substStr x v)
  | .store e₁ e₂ => .store (e₁.substStr x v) (e₂.substStr x v)
  | .cmpXchg e₀ e₁ e₂ => .cmpXchg (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .xchg e₁ e₂ => .xchg (e₁.substStr x v) (e₂.substStr x v)
  | .faa e₁ e₂ => .faa (e₁.substStr x v) (e₂.substStr x v)
  | .fork e' => .fork (e'.substStr x v)
  | .newProph => .newProph
  | .resolve e₀ e₁ e₂ => .resolve (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)

def Exp.subst (x : Binder) (v : Val) (e : Exp) : Exp :=
  if let .named x := x then Exp.substStr x v e else e

def BaseLit.isUnboxed : BaseLit → Bool
  | .prophecy _ | .poison => false
  | _ => true

def Val.isUnboxed : Val → Bool
  | .lit l => l.isUnboxed
  | .injL (.lit l) => l.isUnboxed
  | .injR (.lit l) => l.isUnboxed
  | _ => false

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

abbrev heaplangE := concE ⊕ₑ heapE Loc Val ⊕ₑ failE ⊕ₑ demonicE (List Loc)

structure HeaplangState (GE GR) where
  tp : ConcState GE GR
  heap : heapE.T Loc Val

@[simp]
def HeaplangStateIso GE GR : Iso (ConcState GE GR × heapE.T Loc Val × PUnit × PUnit) (HeaplangState GE GR) where
  toFun x := ⟨x.1, x.2.fst⟩
  invFun x := ⟨x.tp, x.heap, ⟨⟩, ⟨⟩⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

abbrev heaplangEH {GE GR} : EHandler heaplangE GE GR (HeaplangState GE GR) :=
  isoEH (HeaplangStateIso GE GR) (concEH (GE:=GE) (GR:=GR) ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH (List Loc)).toEHandler)

/- TODO: define EHandlerBind -/
-- instance {GE GR GR'} : EHandlerBind (GE:=GE) (GR:=GR) (GR':=GR')
  -- heaplangEH (failingEH ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH (List Loc)).toEHandler) := inferInstanceAs (EHandlerBind (concEH ⊕ₑₕ _) _)

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
  | .offset, .int off => some $ .loc (l₁.offset off)
  | .le, .loc l₂ => some $ .bool (decide (l₁.n ≤ l₂.n))
  | .lt, .loc l₂ => some $ .bool (decide (l₁.n < l₂.n))
  | _, _ => none

def BinOp.denote (op : BinOp) (v₁ v₂ : Val) : ITree heaplangE Val :=
  if op == .eq then
    if v₁.isUnboxed || v₂.isUnboxed then
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
  | .rec_ f x e => return .rec_ f x e
  | .app e₁ e₂ => do
    let v ← denoteYield e₂
    let f ← denoteYield e₁
    let ⟨f', x', e⟩ ← f.rec!
    let body := e.subst f' f |>.subst x' v
    body.yieldIfNotVal
    denote body
  | .unop op e => do
    let v ← denoteYield e
    op.denote v
  | .binop op e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    op.denote v₁ v₂
  | .if e₀ e₁ e₂ => do
    let c ← denoteYield e₀
    if ← c.bool! then
      denoteYield e₁
    else
      denoteYield e₂
  | .pair e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    return .pair v₁ v₂
  | .fst e => do
    let v ← denoteYield e
    return (← v.pair!).1
  | .snd e => do
    let v ← denoteYield e
    return (← v.pair!).2
  | .injL e => do
    let v ← denoteYield e
    return .injL v
  | .injR e => do
    let v ← denoteYield e
    return .injR v
  | .case e₀ e₁ e₂ => do
    let v ← denoteYield e₀
    match v with
    | .injL w => yield; denote (.app e₁ (.val w))
    | .injR w => yield; denote (.app e₂ (.val w))
    | _ => fail "Case: not a sum value"
  | .allocN e₁ e₂ => do
    let v ← denoteYield e₂
    let vn ← denoteYield e₁
    let n ← vn.int!
    if n ≤ 0 then fail "AllocN: count must be positive"
    let ⟨ls, _⟩ ← HeapE.allocN (λ ls => ∃ l : Loc, ls = (List.range n.toNat).map λ n => l.offset (Int.ofNat n)) v
    return .lit (.loc ls.head!)
  | .free e => do
    let v ← denoteYield e
    let l ← v.loc!
    let .some _ ← storeOpt (Val:=Val) l none
      | fail "free: location not allocated"
    return .lit .unit
  | .load e => do
    let v ← denoteYield e
    load! (← v.loc!)
  | .store e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let _ ← store! (← v₁.loc!) v₂
    return .lit .unit
  | .cmpXchg e₀ e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let v₀ ← denoteYield e₀
    let l ← v₀.loc!
    let vl ← load! l
    if !(vl.isUnboxed || v₁.isUnboxed) then
      fail "CmpXchg: comparing boxed values"
    if vl = v₁ then
      let _ ← store! l v₂
      return .pair vl (.lit (.bool true))
    else
      return .pair vl (.lit (.bool false))
  | .xchg e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    store! (← v₁.loc!) v₂
  | .faa e₁ e₂ => do
    let v₂ ← denoteYield e₂
    let v₁ ← denoteYield e₁
    let l ← v₁.loc!
    let i₂ ← v₂.int!
    let old ← load! l
    let i₁ ← old.int!
    let _ ← store! l (.lit (.int (i₁ + i₂)) : Val)
    return old
  | .fork e => do
    let _ ← ConcE.fork (denoteYield e >>= λ _ => return ⟨⟩)
    return .lit .unit
  | .newProph => do
    fail "prophecy is not implemented"
  | .resolve _ _ _ => do
    fail "prophecy is not implemented"
partial_fixpoint


section Derived
def Exp.stuck : Exp := Exp.app (.val $ .lit $ .int 0) (.val $ .lit $ .int 0)

@[simp]
theorem Exp.stuck_subst x v:
  Exp.substStr x v Exp.stuck = Exp.stuck := by
  simp [Exp.stuck, Exp.substStr]

def Exp.assert (e : Exp) := Exp.if e (.val $ .lit .unit) Exp.stuck

@[simp]
theorem Exp.assert_subst x v e:
  Exp.substStr x v (Exp.assert e) = Exp.assert (Exp.substStr x v e) := by
  simp [Exp.assert, Exp.substStr]
end Derived

section Notation
open Lean Lean.PrettyPrinter Elab Parser

declare_syntax_cat hl_exp
declare_syntax_cat hl_val

/-- embedding heaplang expressions into terms -/
syntax:max "hl(" hl_exp ")" : term
/-- embedding heaplang binders into terms -/
syntax:max "hl_binder(" binderIdent ")" : term
/-- embedding heaplang values into terms -/
syntax:max "hl_val(" hl_val ")" : term

/-- escaping -/
syntax:max "{" term "}" : hl_val
/-- escaping identifiers -/
syntax:max ident : hl_val
/-- embedding literals -/
syntax:max "#" term:max : hl_val
/-- pairs -/
syntax:max "(" hl_val ", " hl_val,+ ")" : hl_val
/-- injL -/
syntax:100 "injl(" hl_val ")" : hl_val
/-- injR -/
syntax:100 "injr(" hl_val ")" : hl_val

/-- parenthesis -/
syntax:max "(" hl_exp ")" : hl_exp
/-- embedding values -/
syntax:max "v(" hl_val ")" : hl_exp
/-- escaping -/
syntax:max "{" term "}" : hl_exp
/-- embedding literals -/
syntax:max "#" term:max : hl_exp
/-- variables -/
syntax:max ident : hl_exp
-- levels are taken from https://github.com/leanprover/lean4/blob/985f350dcd18fc7814dfa677cac09933f44f3215/src/Init/Notation.lean#L280
/-- addition -/
syntax:65 hl_exp:66 " + " hl_exp:65 : hl_exp
/-- offset -/
syntax:65 hl_exp:66 " +ₗ " hl_exp:65 : hl_exp
/-- subtraction -/
syntax:65 hl_exp:66 " - " hl_exp:65 : hl_exp
/-- multiplication -/
syntax:70 hl_exp:71 " * " hl_exp:70 : hl_exp
/-- division -/
syntax:70 hl_exp:71 " / " hl_exp:70 : hl_exp
/-- modulo -/
syntax:70 hl_exp:71 " % " hl_exp:70 : hl_exp
/-- and -/
syntax:60 hl_exp:61 " & " hl_exp:60 : hl_exp
/-- or -/
syntax:55 hl_exp:56 " | " hl_exp:55 : hl_exp
/-- xor -/
syntax:58 hl_exp:59 " ^ " hl_exp:58 : hl_exp
/-- shiftl -/
syntax:75 hl_exp:76 " <<< " hl_exp:75 : hl_exp
/-- shiftr -/
syntax:75 hl_exp:76 " >>> " hl_exp:75 : hl_exp
/-- le -/
syntax:50 hl_exp:50 " <= " hl_exp:50 : hl_exp
syntax:50 hl_exp:50 " ≤ " hl_exp:50 : hl_exp
/-- lt -/
syntax:50 hl_exp:50 " < " hl_exp:50 : hl_exp
/-- equality -/
syntax:50 hl_exp:50 " = " hl_exp:50 : hl_exp

/-- neg -/
syntax:100 "~" hl_exp:100 : hl_exp
/-- minus -/
syntax:75 "-" hl_exp:75 : hl_exp

/-- if -/
syntax:10 "if " hl_exp:10 " then " hl_exp:10 " else " hl_exp:10 : hl_exp

/-- application -/
syntax:100 hl_exp:100 ppSpace hl_exp:101 : hl_exp
/-- let -/
syntax:10 "let " binderIdent " := " hl_exp:10 "; " hl_exp:1 : hl_exp
/-- sequencing -/
syntax:5 hl_exp:6 "; " hl_exp:5 : hl_exp
/-- lambda -/
syntax:10 "λ " binderIdent+ ", " hl_exp:10 : hl_exp
/-- lambda -/
syntax:10 "λ " binderIdent+ ", " hl_exp:10 : hl_val
/-- recursive function -/
syntax:10 "rec " binderIdent ppSpace binderIdent+ " := " hl_exp:10 : hl_exp
/-- recursive function -/
syntax:10 "rec " binderIdent ppSpace binderIdent+ " := " hl_exp:10 : hl_val

/-- pairs -/
syntax:max "(" hl_exp ", " hl_exp,+ ")" : hl_exp
/-- fst -/
syntax:100 "fst(" hl_exp ")" : hl_exp
/-- snd -/
syntax:100 "snd(" hl_exp ")" : hl_exp

/-- case -/
syntax:100 "case: " hl_exp:80 " | " binderIdent " => " hl_exp:80 " | " binderIdent " => " hl_exp:80 : hl_exp
/-- injL -/
syntax:100 "injl(" hl_exp ")" : hl_exp
/-- injR -/
syntax:100 "injr(" hl_exp ")" : hl_exp

/-- heap operations -/
syntax:100 "allocn(" hl_exp ", " hl_exp ")" : hl_exp
syntax:100 "ref(" hl_exp ")" : hl_exp
syntax:100 "free(" hl_exp ")" : hl_exp
syntax:80 "!" hl_exp:80 : hl_exp
syntax:80 hl_exp:80 " ← " hl_exp:80 : hl_exp
syntax:100 "cmpXchg(" hl_exp ", " hl_exp ", " hl_exp ")" : hl_exp
syntax:100 "xchg(" hl_exp ", " hl_exp ")" : hl_exp
syntax:100 "faa(" hl_exp ", " hl_exp ")" : hl_exp

/-- fork -/
syntax:100 "fork(" hl_exp  ")" : hl_exp

/-- assert -/
syntax:100 "assert(" hl_exp  ")" : hl_exp

partial def unpackHLExp [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `hl_exp)
  | `(hl($e)) => `(hl_exp|$e)
  | `($t) => `(hl_exp|{$t})

partial def unpackHLVal [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `hl_val)
  | `(hl_val($e)) => `(hl_val|$e)
  | `($t) => `(hl_val|{$t})

partial def unpackHLBinder [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `Lean.binderIdent)
  | `(hl_binder($e)) => `(binderIdent|$e)
-- TODO
  | `($_) => panic! "unknown binder"

/-- elaborating binders -/
macro_rules
  | `(hl_binder(_)) => `(Binder.anon)
  | `(hl_binder($i:ident)) => `(Binder.named $(Syntax.mkStrLit i.getId.toString))

/-- elaborating values -/
macro_rules
  | `(hl_val($i:ident)) => pure i
  | `(hl_val({$t})) => pure t
  | `(hl_val(# $e)) => `(Val.lit $e)
  | `(hl_val(rec $f $x := $e)) => do `(Val.rec_ hl_binder($f) hl_binder($x) hl($e))
  | `(hl_val(rec $f $x $xs* := $e)) => do `(hl_val(rec $f $x := λ $xs*, $e))
  | `(hl_val(λ $xs*, $e)) => do `(hl_val(rec _ $xs* := $e))
  | `(hl_val(($e1, $e2))) => `(Val.pair hl_val($e1) hl_val($e2))
  | `(hl_val(($e1, $e2, $e3,*))) => `(hl_val(($e1, ($e2, $e3,*))))
  | `(hl_val(injl($e1))) => `(Val.injL hl_val($e1))
  | `(hl_val(injr($e1))) => `(Val.injR hl_val($e1))

/-- elaborating expressions -/
macro_rules
  | `(hl(($e))) => `(hl($e))
  | `(hl({$t})) => pure t
  | `(hl(v($e))) => `(Exp.val hl_val($e))
  | `(hl(# $e)) => `(hl(v(# $e)))
  | `(hl($i:ident)) => `(Exp.var $(Syntax.mkStrLit i.getId.toString))
  | `(hl($e1 + $e2)) => `(Exp.binop BinOp.plus hl($e1) hl($e2))
  | `(hl($e1 +ₗ $e2)) => `(Exp.binop BinOp.offset hl($e1) hl($e2))
  | `(hl($e1 - $e2)) => `(Exp.binop BinOp.minus hl($e1) hl($e2))
  | `(hl($e1 * $e2)) => `(Exp.binop BinOp.mult hl($e1) hl($e2))
  | `(hl($e1 / $e2)) => `(Exp.binop BinOp.tdiv hl($e1) hl($e2))
  | `(hl($e1 % $e2)) => `(Exp.binop BinOp.tmod hl($e1) hl($e2))
  | `(hl($e1 & $e2)) => `(Exp.binop BinOp.and hl($e1) hl($e2))
  | `(hl($e1 | $e2)) => `(Exp.binop BinOp.or hl($e1) hl($e2))
  | `(hl($e1 ^ $e2)) => `(Exp.binop BinOp.xor hl($e1) hl($e2))
  | `(hl($e1 <<< $e2)) => `(Exp.binop BinOp.shiftl hl($e1) hl($e2))
  | `(hl($e1 >>> $e2)) => `(Exp.binop BinOp.shiftr hl($e1) hl($e2))
  | `(hl($e1 <= $e2)) => `(hl($e1 ≤ $e2))
  | `(hl($e1 ≤ $e2)) => `(Exp.binop BinOp.le hl($e1) hl($e2))
  | `(hl($e1 < $e2)) => `(Exp.binop BinOp.lt hl($e1) hl($e2))
  | `(hl($e1 = $e2)) => `(Exp.binop BinOp.eq hl($e1) hl($e2))
  | `(hl(~$e1)) => `(Exp.unop UnOp.neg hl($e1))
  | `(hl(-$e1)) => `(Exp.unop UnOp.minus hl($e1))
  | `(hl(if $e1 then $e2 else $e3)) => `(Exp.if hl($e1) hl($e2) hl($e3))
  | `(hl($e1 $e2)) => `(Exp.app hl($e1) hl($e2))
  | `(hl(rec $f $x := $e)) => do `(Exp.rec_ hl_binder($f) hl_binder($x) hl($e))
  | `(hl(rec $f $x $xs* := $e)) => do `(hl(rec $f $x := λ $xs*, $e))
  | `(hl(λ $xs*, $e)) => do `(hl(rec _ $xs* := $e))
  | `(hl($e1; $e2)) => `(hl(let _ := $e1; $e2))
  | `(hl(let $i := $e1; $e2)) => `(hl((λ $i, $e2) $e1))
  | `(hl(($e1, $e2))) => `(Exp.pair hl($e1) hl($e2))
  | `(hl(($e1, $e2, $e3,*))) => `(hl(($e1, ($e2, $e3,*))))
  | `(hl(fst($e1))) => `(Exp.fst hl($e1))
  | `(hl(snd($e1))) => `(Exp.snd hl($e1))
  | `(hl(case: $e1 | $i2 => $e2 | $i3 => $e3)) => `(Exp.case hl($e1) hl(λ $i2, $e2) hl(λ $i3, $e3))
  | `(hl(injl($e1))) => `(Exp.injL hl($e1))
  | `(hl(injr($e1))) => `(Exp.injR hl($e1))
  | `(hl(allocn($e1, $e2))) => `(Exp.allocN hl($e1) hl($e2))
  | `(hl(ref($e1))) => `(hl(allocn(#1, $e1)))
  | `(hl(free($e1))) => `(Exp.free hl($e1))
  | `(hl(! $e1)) => `(Exp.load hl($e1))
  | `(hl($e1 ← $e2)) => `(Exp.store hl($e1) hl($e2))
  | `(hl(cmpXchg($e1, $e2, $e3))) => `(Exp.cmpXchg hl($e1) hl($e2) hl($e3))
  | `(hl(xchg($e1, $e2))) => `(Exp.xchg hl($e1) hl($e2))
  | `(hl(faa($e1, $e2))) => `(Exp.faa hl($e1) hl($e2))
  | `(hl(fork($e1))) => `(Exp.fork hl($e1))
  | `(hl(assert($e1))) => `(Exp.assert hl($e1))

/-- delaborating Binders -/
@[app_unexpander Binder.anon]
def unexpAnon : Unexpander
  | `($_) => `(hl_binder(_))

@[app_unexpander Binder.named]
def unexpNamed : Unexpander
  | `($_ $s:str) => `(hl_binder($(Lean.mkIdent $ Name.mkSimple s.getString):ident))
  | _ => throw ()

/-- delaborating values -/
@[app_unexpander Val.lit]
def unexpLit : Unexpander
  | `($_ $arg) => `(hl_val(# $arg))
  | _ => throw ()

partial def unexpLamVal : Term → UnexpandM Term
  | `(hl_val(rec _ $x := $e)) => do
    unexpLamVal $ ← `(hl_val(λ $x, $e))
  | `(hl_val(λ $x, (λ $ys*, $e))) => do
    unexpLamVal $ ← `(hl_val(λ $x $ys*, $e))
  | x => return x

@[app_unexpander Val.rec_]
def unexpRecVal : Unexpander
  | `($_ $f $x $e) => do
    unexpLamVal $ ← `(hl_val(rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e)))
  | _ => throw ()

partial def unexpPairVal' : Term → UnexpandM Term
  | `(hl_val(($e1, ($e2, $e3,*)))) => do
    unexpPairVal' $ ← `(hl_val(($e1, $e2, $e3,*)))
  | x => return x

@[app_unexpander Val.pair]
def unexpPairVal : Unexpander
  | `($_ $e1 $e2) => do
    unexpPairVal' $ ← `(hl_val(($(← unpackHLVal e1), $(← unpackHLVal e2))))
  | _ => throw ()

@[app_unexpander Val.injL]
def unexpInjlVal : Unexpander
  | `($_ $e1) => do `(hl_val(injl($(← unpackHLVal e1))))
  | _ => throw ()

@[app_unexpander Val.injR]
def unexpInjrVal : Unexpander
  | `($_ $e1) => do `(hl_val(injr($(← unpackHLVal e1))))
  | _ => throw ()

/-- delaborating expressions -/
partial def unexpValLit : Term → UnexpandM Term
  | `(hl(v(# $l))) => do
    unexpValLit $ ← `(hl(# $l))
  | `(hl(v({$i:ident}))) => do
    unexpValLit $ ← `(hl(v($i:ident)))
  | x => return x

@[app_unexpander Exp.val]
def unexpVal : Unexpander
  | `($_ $arg) => do unexpValLit $ ← `(hl(v($(← unpackHLVal arg))))
  | _ => throw ()


@[app_unexpander Exp.var]
def unexpVar : Unexpander
  | `($_ $e:str) => do `(hl($(Lean.mkIdent $ Name.mkSimple e.getString):ident))
  | _ => throw ()

@[app_unexpander Exp.binop]
def unexpBinop : Unexpander
  | `($_ BinOp.plus $e1 $e2) => do `(hl(($(← unpackHLExp e1) + $(← unpackHLExp e2))))
  | `($_ BinOp.offset $e1 $e2) => do `(hl(($(← unpackHLExp e1) +ₗ $(← unpackHLExp e2))))
  | `($_ BinOp.minus $e1 $e2) => do `(hl(($(← unpackHLExp e1) - $(← unpackHLExp e2))))
  | `($_ BinOp.mult $e1 $e2) => do `(hl(($(← unpackHLExp e1) * $(← unpackHLExp e2))))
  | `($_ BinOp.tdiv $e1 $e2) => do `(hl(($(← unpackHLExp e1) / $(← unpackHLExp e2))))
  | `($_ BinOp.tmod $e1 $e2) => do `(hl(($(← unpackHLExp e1) % $(← unpackHLExp e2))))
  | `($_ BinOp.and $e1 $e2) => do `(hl(($(← unpackHLExp e1) & $(← unpackHLExp e2))))
  | `($_ BinOp.or $e1 $e2) => do `(hl(($(← unpackHLExp e1) | $(← unpackHLExp e2))))
  | `($_ BinOp.xor $e1 $e2) => do `(hl(($(← unpackHLExp e1) ^ $(← unpackHLExp e2))))
  | `($_ BinOp.shiftl $e1 $e2) => do `(hl(($(← unpackHLExp e1) <<< $(← unpackHLExp e2))))
  | `($_ BinOp.shiftr $e1 $e2) => do `(hl(($(← unpackHLExp e1) >>> $(← unpackHLExp e2))))
  | `($_ BinOp.le $e1 $e2) => do `(hl(($(← unpackHLExp e1) ≤ $(← unpackHLExp e2))))
  | `($_ BinOp.lt $e1 $e2) => do `(hl(($(← unpackHLExp e1) < $(← unpackHLExp e2))))
  | `($_ BinOp.eq $e1 $e2) => do `(hl(($(← unpackHLExp e1) = $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.unop]
def unexpUnop : Unexpander
  | `($_ UnOp.neg $e1) => do `(hl((~$(← unpackHLExp e1))))
  | `($_ UnOp.minus $e1) => do `(hl((-$(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.if]
def unexpIf : Unexpander
  | `($_ $e1 $e2 $e3) => do `(hl(if $(← unpackHLExp e1) then $(← unpackHLExp e2) else $(← unpackHLExp e3) ))
  | _ => throw ()

partial def unexpLam : Term → UnexpandM Term
  | `(hl((rec _ $x := $e))) => do
    unexpLam $ ← `(hl((λ $x, $e)))
  | `(hl((λ $x, (λ $ys*, $e)))) => do
    unexpLam $ ← `(hl((λ $x $ys*, $e)))
  | x => return x

@[app_unexpander Exp.rec_]
def unexpRec : Unexpander
  | `($_ $f $x $e) => do
    unexpLam $ ← `(hl((rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e))))
  | _ => throw ()

partial def unexpLet : Term → UnexpandM Term
  | `(hl((λ $f, $e2) $e1)) => do
    unexpLet $ ← `(hl(let $f := $e1; $e2))
  | `(hl(let _ := $e1; $e2)) => do `(hl($e1; $e2))
  | x => return x

@[app_unexpander Exp.app]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    unexpLet $ ← `(hl($(← unpackHLExp e1) $(← unpackHLExp e2)))
  | _ => throw ()

partial def unexpPair' : Term → UnexpandM Term
  | `(hl(($e1, ($e2, $e3,*)))) => do
    unexpPair' $ ← `(hl(($e1, $e2, $e3,*)))
  | x => return x

@[app_unexpander Exp.pair]
def unexpPair : Unexpander
  | `($_ $e1 $e2) => do
    unexpPair' $ ← `(hl(($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.fst]
def unexpFst : Unexpander
  | `($_ $e1) => do `(hl(fst($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.snd]
def unexpSnd : Unexpander
  | `($_ $e1) => do `(hl(snd($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.injL]
def unexpInjl : Unexpander
  | `($_ $e1) => do `(hl(injl($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.injR]
def unexpInjr : Unexpander
  | `($_ $e1) => do `(hl(injr($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.case]
def unexpCase : Unexpander
  | `($_ $e1 hl((λ $i2, $e2)) hl((λ $i3, $e3))) => do `(hl(case: $(← unpackHLExp e1) | $i2 => $e2 | $i3 => $e3))
  | _ => throw ()

partial def unexpRef : Term → UnexpandM Term
  | `(hl(allocn(#1, $e2))) => do `(hl(ref($e2)))
  | x => return x

@[app_unexpander Exp.allocN]
def unexpAllocN : Unexpander
  | `($_ $e1 $e2) => do unexpRef $ ← `(hl(allocn($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.free]
def unexpFree : Unexpander
  | `($_ $e1) => do `(hl(free($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.load]
def unexpLoad : Unexpander
  | `($_ $e1) => do `(hl(!$(← unpackHLExp e1)))
  | _ => throw ()

@[app_unexpander Exp.store]
def unexpStore : Unexpander
  | `($_ $e1 $e2) => do `(hl($(← unpackHLExp e1) ← $(← unpackHLExp e2)))
  | _ => throw ()

@[app_unexpander Exp.cmpXchg]
def unexpCmpXChg : Unexpander
  | `($_ $e1 $e2 $e3) => do `(hl(cmpXchg($(← unpackHLExp e1), $(← unpackHLExp e2), $(← unpackHLExp e3))))
  | _ => throw ()

@[app_unexpander Exp.xchg]
def unexpXChg : Unexpander
  | `($_ $e1 $e2) => do `(hl(xchg($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.faa]
def unexpFAA : Unexpander
  | `($_ $e1 $e2) => do `(hl(faa($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.fork]
def unexpFork : Unexpander
  | `($_ $e1) => do `(hl(fork($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.assert]
def unexpAssert : Unexpander
  | `($_ $e1) => do `(hl(assert($(← unpackHLExp e1))))
  | _ => throw ()

section test
variable (v : Val)
/-- info: hl((#1 + (#1 + v(v)))) : Exp -/
#guard_msgs in
#check hl(#1 + #1 + {.val v})
/--
info: Exp.binop BinOp.plus (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
  (Exp.binop BinOp.plus (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
    (Exp.val v)) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(#1 + #1 + {.val v})
/-- info: hl((#1 + (#1 + v(v)))) : Exp -/
#guard_msgs in
#check hl(#1 + (#1 + v(v)))

/-- info: hl(((#1 + #1) + v(v))) : Exp -/
#guard_msgs in
#check hl((#1 + #1) + v(v))

/-- info: hl((#1 = (v + v(v)))) : Exp -/
#guard_msgs in
#check hl(#1 = v + v(v))
/--
info: Exp.binop BinOp.eq (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
  (Exp.binop BinOp.plus (Exp.var "v") (Exp.val v)) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(#1 = v + v(v))

/-- info: hl((λ x y z, #1)) : Exp -/
#guard_msgs in
#check hl(λ x y z, #1)

/-- info: hl_val(λ x y z, #1) : Val -/
#guard_msgs in
#check hl_val(λ x y z, #1)

/--
info: Exp.rec_ Binder.anon (Binder.named "x")
  (Exp.rec_ Binder.anon (Binder.named "y")
    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(λ x y, #1)

/-- info: hl((rec f x := x) #1) : Exp -/
#guard_msgs in
#check hl((rec f x := x) #1)

/--
info: (Exp.rec_ (Binder.named "f") (Binder.named "x") (Exp.var "x")).app
  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl((rec f x := x) #1)

/-- info: hl((λ x y, let z := #1; #2; (x + (y + z)))) : Exp -/
#guard_msgs in
#check hl(λ x y, let z := #1; #2; x + y + z)

/--
info: Exp.rec_ Binder.anon (Binder.named "x")
  (Exp.rec_ Binder.anon (Binder.named "y")
    ((Exp.rec_ Binder.anon (Binder.named "z")
          ((Exp.rec_ Binder.anon Binder.anon
                (Exp.binop BinOp.plus (Exp.var "x") (Exp.binop BinOp.plus (Exp.var "y") (Exp.var "z")))).app
            (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2))))))).app
      (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(λ x y, let z := #1; #2; x + y + z)

/--
info: hl((λ x y,
      ((((#1 + (#2 +ₗ (#3 - (#4 * (#5 / (#6 % #7)))))) & #8) | (#9 ^ (#10 <<< (#11 >>> #12)))) ≤
          (#13 ≤ (#14 < (#15 = (#16 + ((-#17) + (~#18))))))))) : Exp
-/
#guard_msgs in
#check hl(λ x y, #1 + #2 +ₗ #3 - #4 * #5 / #6 % #7 & #8 | #9 ^ #10 <<< #11 >>> #12 <= #13 ≤ #14 < #15 = #16 + (-#17) + (~#18))

/--
info: Exp.rec_ Binder.anon (Binder.named "x")
  (Exp.rec_ Binder.anon (Binder.named "y")
    (Exp.binop BinOp.le
      (Exp.binop BinOp.or
        (Exp.binop BinOp.and
          (Exp.binop BinOp.plus (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
            (Exp.binop BinOp.offset
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2)))))
              (Exp.binop BinOp.minus
                (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 3) (@instOfNatBaseLit (nat_lit 3)))))
                (Exp.binop BinOp.mult
                  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 4) (@instOfNatBaseLit (nat_lit 4)))))
                  (Exp.binop BinOp.tdiv
                    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 5) (@instOfNatBaseLit (nat_lit 5)))))
                    (Exp.binop BinOp.tmod
                      (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 6) (@instOfNatBaseLit (nat_lit 6)))))
                      (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 7) (@instOfNatBaseLit (nat_lit 7)))))))))))
          (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 8) (@instOfNatBaseLit (nat_lit 8))))))
        (Exp.binop BinOp.xor (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 9) (@instOfNatBaseLit (nat_lit 9)))))
          (Exp.binop BinOp.shiftl
            (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 10) (@instOfNatBaseLit (nat_lit 10)))))
            (Exp.binop BinOp.shiftr
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 11) (@instOfNatBaseLit (nat_lit 11)))))
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 12) (@instOfNatBaseLit (nat_lit 12)))))))))
      (Exp.binop BinOp.le (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 13) (@instOfNatBaseLit (nat_lit 13)))))
        (Exp.binop BinOp.lt (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 14) (@instOfNatBaseLit (nat_lit 14)))))
          (Exp.binop BinOp.eq (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 15) (@instOfNatBaseLit (nat_lit 15)))))
            (Exp.binop BinOp.plus
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 16) (@instOfNatBaseLit (nat_lit 16)))))
              (Exp.binop BinOp.plus
                (Exp.unop UnOp.minus
                  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 17) (@instOfNatBaseLit (nat_lit 17))))))
                (Exp.unop UnOp.neg
                  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 18) (@instOfNatBaseLit (nat_lit 18))))))))))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(λ x y, #1 + #2 +ₗ #3 - #4 * #5 / #6 % #7 & #8 | #9 ^ #10 <<< #11 >>> #12 <= #13 ≤ #14 < #15 = #16 + (-#17) + (~#18))

/-- info: hl(if #1 then #2 else #3) : Exp -/
#guard_msgs in
#check hl(if #1 then #2 else #3)

/-- info: hl((#1, #2, #3)) : Exp -/
#guard_msgs in
#check hl((#1, #2, #3))

/--
info: (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))).pair
  ((Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2))))).pair
    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 3) (@instOfNatBaseLit (nat_lit 3)))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl((#1, #2, #3))

/-- info: hl_val((#1, #BaseLit.unit, #(BaseLit.bool true), #(BaseLit.int (-1)))) : Val -/
#guard_msgs in
#check hl_val((#1, #(), #true, #(.int (-1))))

/--
info: (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))).pair
  ((Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2)))).pair
    (Val.lit (@OfNat.ofNat BaseLit (nat_lit 3) (@instOfNatBaseLit (nat_lit 3))))) : Val
-/
#guard_msgs in
set_option pp.explicit true in
#check hl_val((#1, #2, #3))

/-- info: hl(fst(snd((#1, #2, #3)))) : Exp -/
#guard_msgs in
#check hl(fst(snd((#1, #2, #3))))

/-- info: hl(case: injl(injr(#1)) | _ => #1 | y => #2) : Exp -/
#guard_msgs in
#check hl(case: injl(injr(#1)) | _ => #1 | y => #2)

/-- info: hl_val(injl(injr(#1))) : Val -/
#guard_msgs in
#check hl_val(injl(injr(#1)))


/--
info: hl(let x := ref(#0);
    let y := allocn(!x, #0);
      (x ← !x + #1); fork(cmpXchg(x, #1, #2); xchg(x, #2); faa(x, #4)); assert((!x = #0)); free(x)) : Exp
-/
#guard_msgs in
#check hl(let x := ref(#0); let y := allocn(!x, #0); x ← !x + #1; fork(cmpXchg(x, #1, #2); xchg(x, #2); faa(x, #4)); assert(!x = #0); free(x))

/--
info: (Exp.rec_ Binder.anon (Binder.named "x")
      ((Exp.rec_ Binder.anon (Binder.named "y")
            ((Exp.rec_ Binder.anon Binder.anon
                  ((Exp.rec_ Binder.anon Binder.anon
                        ((Exp.rec_ Binder.anon Binder.anon (Exp.var "x").free).app
                          (Exp.binop BinOp.eq (Exp.var "x").load
                              (Exp.val
                                (Val.lit
                                  (@OfNat.ofNat BaseLit (nat_lit 0) (@instOfNatBaseLit (nat_lit 0)))))).assert)).app
                    ((Exp.rec_ Binder.anon Binder.anon
                            ((Exp.rec_ Binder.anon Binder.anon
                                  ((Exp.var "x").faa
                                    (Exp.val
                                      (Val.lit
                                        (@OfNat.ofNat BaseLit (nat_lit 4) (@instOfNatBaseLit (nat_lit 4))))))).app
                              ((Exp.var "x").xchg
                                (Exp.val
                                  (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2)))))))).app
                        ((Exp.var "x").cmpXchg
                          (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
                          (Exp.val
                            (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2))))))).fork)).app
              (Exp.binop BinOp.plus ((Exp.var "x").store (Exp.var "x").load)
                (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))))).app
        ((Exp.var "x").load.allocN
          (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 0) (@instOfNatBaseLit (nat_lit 0)))))))).app
  ((Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))).allocN
    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 0) (@instOfNatBaseLit (nat_lit 0)))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(let x := ref(#0); let y := allocn(!x, #0); x ← !x + #1; fork(cmpXchg(x, #1, #2); xchg(x, #2); faa(x, #4)); assert(!x = #0); free(x))

end test
end Notation
