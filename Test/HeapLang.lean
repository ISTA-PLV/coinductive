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

instance : Coe Unit BaseLit where
  coe _ := .unit

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
  tid : Nat
  tpool : List (Option (ITree GE GR))
  heap : heapE.T Loc Val

@[simp]
def HeaplangStateIso GE GR : Iso ((Nat × List (Option (ITree GE GR))) × heapE.T Loc Val × PUnit × PUnit) (HeaplangState GE GR) where
  toFun x := ⟨x.1.1, x.1.2, x.2.fst⟩
  invFun x := ⟨⟨x.tid, x.tpool⟩, x.heap, ⟨⟩, ⟨⟩⟩
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

section Notation
open Lean Lean.PrettyPrinter Elab Parser

declare_syntax_cat hl_exp
declare_syntax_cat hl_val

syntax:max "hl(" hl_exp ")" : term
syntax:max "hl_binder(" binderIdent ")" : term
syntax:max "hl_val(" hl_val ")" : term
syntax:max "(" hl_exp ")" : hl_exp
syntax:max "v(" hl_val ")" : hl_exp
syntax:max "{" term "}" : hl_exp
syntax:max "{" term "}" : hl_val
syntax:max ident : hl_val
syntax:max "#" term:max : hl_exp
syntax:max "#" term:max : hl_val
syntax:max ident : hl_exp
syntax:65 hl_exp:66 " + " hl_exp:65 : hl_exp
syntax:60 hl_exp:61 " = " hl_exp:60 : hl_exp

syntax:100 hl_exp:100 ppSpace hl_exp:101 : hl_exp -- app
syntax:10 "let " binderIdent " := " hl_exp:10 "; " hl_exp:1 : hl_exp
syntax:5 hl_exp:6 "; " hl_exp:5 : hl_exp
syntax:10 "λ " binderIdent+ ", " hl_exp:10 : hl_exp
syntax:10 "λ " binderIdent+ ", " hl_exp:10 : hl_val
syntax:10 "rec " binderIdent ppSpace binderIdent+ " := " hl_exp:10 : hl_exp
syntax:10 "rec " binderIdent ppSpace binderIdent+ " := " hl_exp:10 : hl_val

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

macro_rules
  | `(hl_binder(_)) => `(Binder.anon)
  | `(hl_binder($i:ident)) => `(Binder.named $(Syntax.mkStrLit i.getId.toString))

macro_rules
  | `(hl_val($i:ident)) => pure i
  | `(hl_val({$t})) => pure t
  | `(hl_val(# $e)) => `(Val.lit $e)
  | `(hl_val(rec $f $x := $e)) => do `(Val.rec_ hl_binder($f) hl_binder($x) hl($e))
  | `(hl_val(rec $f $x $xs* := $e)) => do `(hl_val(rec $f $x := λ $xs*, $e))
  | `(hl_val(λ $xs*, $e)) => do `(hl_val(rec _ $xs* := $e))

macro_rules
  | `(hl(($e))) => `(hl($e))
  | `(hl({$t})) => pure t
  | `(hl(v($e))) => `(Exp.val hl_val($e))
  | `(hl(# $e)) => `(hl(v(# $e)))
  | `(hl($i:ident)) => `(Exp.var $(Syntax.mkStrLit i.getId.toString))
  | `(hl($e1 + $e2)) => `(Exp.binop .plus hl($e1) hl($e2))
  | `(hl($e1 = $e2)) => `(Exp.binop .eq hl($e1) hl($e2))
  | `(hl($e1 $e2)) => `(Exp.app hl($e1) hl($e2))
  | `(hl(rec $f $x := $e)) => do `(Exp.rec_ hl_binder($f) hl_binder($x) hl($e))
  | `(hl(rec $f $x $xs* := $e)) => do `(hl(rec $f $x := λ $xs*, $e))
  | `(hl(λ $xs*, $e)) => do `(hl(rec _ $xs* := $e))
  | `(hl($e1; $e2)) => `(hl(let _ := $e1; $e2))
  | `(hl(let $i := $e1; $e2)) => `(hl((λ $i, $e2) $e1))

@[app_unexpander Binder.anon]
def unexpAnon : Unexpander
  | `($_) => `(hl_binder(_))

@[app_unexpander Binder.named]
def unexpNamed : Unexpander
  | `($_ $s:str) => `(hl_binder($(Lean.mkIdent $ Name.mkSimple s.getString):ident))
  | _ => throw ()

@[app_unexpander Val.lit]
def unexpLit : Unexpander
  | `($_ $arg) => `(hl_val(# $arg))
  | _ => throw ()

partial def unexpValLit : TSyntax `hl_exp → UnexpandM (TSyntax `hl_exp)
  | `(hl_exp | v(# $l)) => do
    unexpValLit $ ← `(hl_exp | # $l)
  | `(hl_exp | v({$i:ident})) => do
    unexpValLit $ ← `(hl_exp | v($i:ident))
  | x => return x

@[app_unexpander Exp.val]
def unexpVal : Unexpander
  | `($_ $arg) => do
    let r ← unexpValLit $ ← `(hl_exp|v($(← unpackHLVal arg)))
    `(hl($r))
  | _ => throw ()


@[app_unexpander Exp.var]
def unexpVar : Unexpander
  | `($_ $e:str) => do `(hl($(Lean.mkIdent $ Name.mkSimple e.getString):ident))
  | _ => throw ()

@[app_unexpander Exp.binop]
def unexpBinop : Unexpander
  | `($_ BinOp.plus $e1 $e2) => do `(hl(($(← unpackHLExp e1) + $(← unpackHLExp e2))))
  | `($_ BinOp.eq $e1 $e2) => do `(hl(($(← unpackHLExp e1) = $(← unpackHLExp e2))))
  | _ => throw ()

partial def unexpLam : TSyntax `hl_exp → UnexpandM (TSyntax `hl_exp)
  | `(hl_exp | (rec _ $x := $e)) => do
    unexpLam $ ← `(hl_exp | (λ $x, $e))
  | `(hl_exp | (λ $x, (λ $ys, $e))) => do
    unexpLam $ ← `(hl_exp | (λ $x $ys, $e))
  | x => return x

@[app_unexpander Exp.rec_]
def unexpRec : Unexpander
  | `($_ $f $x $e) => do
    let r ← unexpLam $ ← `(hl_exp|(rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e)))
    `(hl($r))
  | _ => throw ()

partial def unexpLamVal : TSyntax `hl_val → UnexpandM (TSyntax `hl_val)
  | `(hl_val | rec _ $x := $e) => do
    unexpLamVal $ ← `(hl_val | λ $x, $e)
  | `(hl_val | λ $x, (λ $ys, $e)) => do
    unexpLamVal $ ← `(hl_val | λ $x $ys, $e)
  | x => return x

@[app_unexpander Val.rec_]
def unexpRecVal : Unexpander
  | `($_ $f $x $e) => do
    let r ← unexpLamVal $ ← `(hl_val|rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e))
    `(hl_val($r))
  | _ => throw ()

partial def unexpLet : TSyntax `hl_exp → UnexpandM (TSyntax `hl_exp)
  | `(hl_exp | (λ $f, $e2) $e1) => do
    unexpLet $ ← `(hl_exp | let $f := $e1; $e2)
  | `(hl_exp | let _ := $e1; $e2) => do
    `(hl_exp | $e1; $e2)
  | x => return x

@[app_unexpander Exp.app]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    let r ← unexpLet $ ← `(hl_exp|$(← unpackHLExp e1) $(← unpackHLExp e2))
    `(hl($r))
  | _ => throw ()


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

/-- info: hl((λ x y, #1)) : Exp -/
#guard_msgs in
#check hl(λ x y, #1)

/-- info: hl_val(λ x y, #1) : Val -/
#guard_msgs in
#check hl_val(λ x y, #1)

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
