import ITree

open ITree
open ITree.Effects
open ITree.Exec

namespace SimpLang

@[ext]
structure Loc where
  private mk ::
  private n : Nat
deriving Inhabited, Repr, DecidableEq

instance : Ord Loc where
  compare l₁ l₂ := compare l₁.n l₂.n

instance : Std.TransOrd Loc where
  eq_swap := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    apply Nat.instTransOrd.eq_swap
  isLE_trans := by
    intros l₁ l₂ l₃; unfold compare; unfold instOrdLoc; simp;
    apply Nat.instTransOrd.isLE_trans

instance : Std.LawfulEqOrd Loc where
  eq_of_compare := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    intros h; ext; assumption

inductive Binder where
  | anon
  | named (name : String)
deriving Inhabited, Repr, DecidableEq

inductive BaseLit where
  | int (n : Int)
  | loc (l : Loc)
  | unit
deriving Inhabited, Repr, DecidableEq

inductive BinOp where
  | plus
  | eq
  | pair
deriving Inhabited, Repr, DecidableEq

inductive UnOp where
  | fst
  | snd
deriving Inhabited, Repr, DecidableEq

inductive HeapOp where
  | alloc
  | load
  | store
  | faa
deriving Inhabited, Repr, DecidableEq

mutual
  inductive Exp : Type where
    | val (v : Val)
    | var (x : String)
    | rec_ (f x : Binder) (e : Exp)
    | app (e₁ e₂ : Exp)
    | binOp (op : BinOp) (e₁ e₂ : Exp)
    | unOp (op : UnOp) (e : Exp)
    | if (e₀ e₁ e₂ : Exp)
    | fork (e : Exp)
    | heapOp (op : HeapOp) (e₁ : Exp) (e₂ : Exp)
    | assert (e : Exp)
  deriving Inhabited, Repr, DecidableEq
  inductive Val : Type where
    | lit (l : BaseLit)
    | rec_ (f x : Binder) (e : Exp)
    | pair (v₁ v₂ : Val)
  deriving Inhabited, Repr, DecidableEq
end

def Exp.isVal : Exp → Bool
  | .val _ => true
  | _ => false

instance : Coe Nat Val where
  coe n := .lit $ .int n

instance : Coe Int Val where
  coe n := .lit $ .int n

instance : Coe Unit Val where
  coe _ := .lit $ .unit

instance {n} : OfNat Val n where
  ofNat := .lit $ .int n

def Exp.substStr (x : String) (v : Val) (e : Exp) : Exp :=
  match e with
  | .val _ => e
  | .var x' => if x == x' then .val v else e
  | .rec_ f x' e => .rec_ f x' $ if .named x != f && .named x != x' then e.substStr x v else e
  | .app e₁ e₂ => .app (e₁.substStr x v) (e₂.substStr x v)
  | .binOp op e₁ e₂ => .binOp op (e₁.substStr x v) (e₂.substStr x v)
  | .unOp op e' => .unOp op (e'.substStr x v)
  | .if e₀ e₁ e₂ => .if (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .fork e => .fork (e.substStr x v)
  | .heapOp op e₁ e₂ => .heapOp op (e₁.substStr x v) (e₂.substStr x v)
  | .assert e => .assert (e.substStr x v)

def Exp.subst (x : Binder) (v : Val) (e : Exp) : Exp :=
  if let .named x := x then Exp.substStr x v e else e

def BaseLit.bool (b : Bool) : BaseLit :=
  if b then .int 1 else .int 0

def Val.int! [failE -< E] : Val → ITree E Int
  | lit (.int i) => return i
  | x => fail s!"{reprStr x} is not Int"

def Val.bool! [failE -< E] (v : Val) : ITree E Bool :=
  do return (← v.int!) != 0

def Val.loc! [failE -< E] : Val → ITree E Loc
  | lit (.loc l) => return l
  | x => fail s!"{reprStr x} is not Loc"

def Val.pair! [failE -< E] : Val → ITree E (Val × Val)
  | .pair v1 v2 => return (v1, v2)
  | x => fail s!"{reprStr x} is not Pair"

def Val.rec! [failE -< E] : Val → ITree E (Binder × Binder × Exp)
  | rec_ f x e => return (f, x, e)
  | x => fail s!"{reprStr x} is not Rec"

abbrev simpE := concE ⊕ₑ heapE Loc Val ⊕ₑ failE ⊕ₑ demonicE Loc
def simpEH {GE GR} := concEH (GE:=GE) (GR:=GR) ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH Loc).toEHandler

instance {GE GR GR'} : EHandlerBind (GE:=GE) (GR:=GR) (GR':=GR')
  simpEH (failingEH ⊕ₑₕ (heapEH Loc Val ⊕ₛₑₕ failEH ⊕ₛₑₕ demonicEH Loc).toEHandler) := inferInstanceAs (EHandlerBind (concEH ⊕ₑₕ _) _)

def UnOp.denote (op : UnOp) (v : Val) : ITree simpE Val :=
  match op with
  | .fst => return (← v.pair!).1
  | .snd => return (← v.pair!).2

def BinOp.denote (op : BinOp) (v₁ v₂ : Val) : ITree simpE Val :=
  match op with
  | .plus => return (← v₁.int!) + (← v₂.int!)
  | .eq => return .lit (.bool (decide $ v₁ == v₂))
  | .pair => return .pair v₁ v₂

def HeapOp.denote (op : HeapOp) (v₁ v₂ : Val) : ITree simpE Val :=
  match op with
  | .alloc => do
    let l ← HeapE.alloc v₂
    return .lit (.loc l)
  | .load => do load! (← v₁.loc!)
  | .store => do
    _ ← store! (← v₁.loc!) v₂
    return .lit .unit
  | .faa => do
    let l ← v₁.loc!
    let x ← load! l
    let x' := (← x.int!) + (← v₂.int!)
    _ ← store! l (x' : Val)
    return x

def Exp.yieldIfNotVal : Exp → ITree simpE Unit
  | .val _ => return ()
  | _ => yield

def Exp.denote (e : Exp) : ITree simpE Val :=
  let denoteYield e :=
    if e.isVal then denote e else yieldAfter (denote e)
  match e with
  | .val v => return v
  | .var x => fail s!"Unbound variable {reprStr x}"
  | .rec_ f x e => return .rec_ f x e
  | .app e₁ e₂ => do
    let f ← denoteYield e₁
    let v ← denoteYield e₂
    let ⟨f', x', e⟩ ← f.rec!
    let body := e.subst f' f |>.subst x' v
    body.yieldIfNotVal
    denote body
  | .binOp op e₁ e₂ => do
    let v₁ ← denoteYield e₁
    let v₂ ← denoteYield e₂
    op.denote v₁ v₂
  | .unOp op e => do
    let v ← denoteYield e
    op.denote v
  | .if e₀ e₁ e₂ => do
    let c ← denoteYield e₀
    if ← c.bool! then
      denoteYield e₁
    else
      denoteYield e₂
  | .fork e => do
    let _ ← ConcE.fork (denoteYield e >>= λ _ =>return ⟨⟩)
    return .lit .unit
  | .heapOp op e₁ e₂ => do
    let v₁ ← denoteYield e₁
    let v₂ ← denoteYield e₂
    op.denote v₁ v₂
  | .assert e => do
    let v ← denoteYield e
    if ← v.bool! then
      return .lit .unit
    else
      fail s!"Assertion failed {reprStr e}"
partial_fixpoint

/-
section Notation
open Lean Elab Elab.Term Parser

abbrev pair := Exp.binOp .pair
abbrev fst := Exp.unOp .fst
abbrev snd := Exp.unOp .snd
abbrev alloc e := Exp.heapOp .alloc (.val $ .lit $ .int 1) e
abbrev load e := Exp.heapOp .load e (.val $ .lit .unit)
abbrev store := Exp.heapOp .store
abbrev faa := Exp.heapOp .faa

instance : Coe Unit Val where
  coe _ := .lit .unit

declare_syntax_cat simp_binder
declare_syntax_cat simp_val
declare_syntax_cat simp_exp

def dollarTerm := leading_parser "$" >> (ident <|> ("(" >> termParser >> ")"))

syntax ("_" <|> ident <|> dollarTerm) : simp_binder

def expandSimpBinder : Syntax → MacroM Term
  | `(simp_binder| _) => `(Binder.anon)
  | `(simp_binder| $i:ident) => `(Binder.named $(Syntax.mkStrLit i.raw.getId.toString))
  | `(simp_binder| $$($t:term)) => return t
  | s =>
    -- Lean doesn't allow `(simp_binder| $$$i:ident), so we have to check the syntax manually
    if s.getKind == `simp_binder.pseudo.antiquot && s.getArgs.size == 4
        && s[0].getKind == `«$» && s[1].getKind == `null && s[2].getKind == `ident
        && s[3].getKind == `null
    then
      `($(⟨s[2]⟩))
    else Macro.throwUnsupported

elab "#testBinder " l:simp_binder : command => do
  let binder ← Command.liftTermElabM $ elabTerm (← liftMacroM $ expandSimpBinder l) (some (.const `HITrees.Examples.SimpLang.Binder []))
  logInfo m!"{binder}"
  return

syntax:max "()" : simp_val
syntax:max "-"? num : simp_val
syntax:max "(" simp_val ", " simp_val,+ ")" : simp_val
syntax:10 "λ " simp_binder+ " , " simp_exp:10 : simp_val
syntax:10 "rec " simp_binder ppSpace simp_binder+ " := " simp_exp:10 : simp_val
syntax:max dollarTerm : simp_val

/- simp_exp -/
syntax:max "(" simp_exp ")" : simp_exp
syntax:max ident : simp_exp -- var
syntax:max "# " simp_val : simp_exp -- val

syntax:65 simp_exp:66 " + " simp_exp:65 : simp_exp -- plus
syntax:60 simp_exp:61 " = " simp_exp:60 : simp_exp -- eq
syntax:max "(" simp_exp ", " simp_exp,+ ")" : simp_exp -- pair

syntax:100 "fst " simp_exp:101 : simp_exp -- fst
syntax:100 "snd " simp_exp:101: simp_exp -- fst

syntax:max "! " simp_exp:(max-1) : simp_exp -- load
syntax:max "ref " simp_exp : simp_exp -- alloc
syntax:15 simp_exp:15 " ← " simp_exp:15 : simp_exp -- store
syntax:100 "FAA " simp_exp:101 ppSpace simp_exp:101 : simp_exp -- FAA

syntax:9 simp_exp:10 " || " simp_exp:9 : simp_exp -- par

syntax:max "call/cc " "(" "λ " simp_binder ", "  simp_exp:1 ")" : simp_exp -- callcc
syntax:50 "throw " simp_exp:51 " to " simp_exp:51 : simp_exp -- throw

syntax:100 simp_exp:100 simp_exp:101 : simp_exp -- app
syntax:10 "if " simp_exp:10 " then " simp_exp:10 " else " simp_exp:10 : simp_exp -- if

syntax:10 "let " simp_binder " := " simp_exp:10 " in " simp_exp:1 : simp_exp -- let
syntax:5 simp_exp:6 "; " simp_exp:5 : simp_exp -- seq
syntax:10 "λ " simp_binder+ ", " simp_exp:10 : simp_exp -- lam
syntax:10 "rec " simp_binder ppSpace simp_binder+ " := " simp_exp:10 : simp_exp -- rec


syntax:max "skip" : simp_exp
syntax:max "assert " simp_exp:max : simp_exp
syntax:max dollarTerm : simp_exp

mutual
partial def expandSimpVal : Syntax → MacroM Term
  | `(simp_val| ()) => `(Val.lit .unit)
  | `(simp_val| $n:num) => `(Val.lit $ .int $n)
  | `(simp_val| -$n:num) => `(Val.lit $ .int (Int.neg $n))
  | `(simp_val| ($x, $y)) => do `(Val.pair $(← expandSimpVal x) $(← expandSimpVal y))
  | `(simp_val| ($x, $y, $zs,*)) => do
    let rest ← `(simp_val| ($y, $zs,*))
    `(Val.pair $(← expandSimpVal x) $(← expandSimpVal rest))
  | `(simp_val| rec $f:simp_binder $x:simp_binder := $e:simp_exp) => do
    `(Val.rec_ $(← expandSimpBinder f) $(← expandSimpBinder x) $(← expandSimpExp e))
  | `(simp_val| rec $f:simp_binder $x:simp_binder $xs:simp_binder* := $e:simp_exp) => do
    let rest ← `(simp_exp| rec _ $xs* := $e)
    `(Val.rec_ $(← expandSimpBinder f) $(← expandSimpBinder x) $(← expandSimpExp rest))
  | `(simp_val| λ $x:simp_binder , $e:simp_exp) => do
    `(Val.rec_ Binder.anon $(← expandSimpBinder x) $(← expandSimpExp e))
  | `(simp_val| λ $x:simp_binder $xs:simp_binder* , $e:simp_exp) => do
    let rest ← `(simp_exp| λ $xs* , $e)
    `(Val.rec_ Binder.anon $(← expandSimpBinder x) $(← expandSimpExp rest))
  | `(simp_val| $$($t:term)) => return t
  | s =>
    -- Lean doesn't allow `(simp_val| $$$i:ident), so we have to check the syntax manually
    if s.getKind == `simp_val.pseudo.antiquot && s.getArgs.size == 4
        && s[0].getKind == `«$» && s[1].getKind == `null && s[2].getKind == `ident
        && s[3].getKind == `null
    then
      `($(⟨s[2]⟩))
    else Macro.throwUnsupported

partial def expandSimpExp : Syntax → MacroM Term
  /- parentheses, var, and val -/
  | `(simp_exp| ($e)) => expandSimpExp e
  | `(simp_exp| $b:ident) => do `(Exp.var $(Syntax.mkStrLit b.raw.getId.toString))
  | `(simp_exp| # $v) => do `(Exp.val $(← expandSimpVal v))
  /- binOp -/
  | `(simp_exp| $e₁ + $e₂) => do `(Exp.binOp .plus $(← expandSimpExp e₁) $(← expandSimpExp e₂))
  | `(simp_exp| $e₁ = $e₂) => do `(Exp.binOp .eq $(← expandSimpExp e₁) $(← expandSimpExp e₂))
  | `(simp_exp| ($x, $y)) => do `(pair $(← expandSimpExp x) $(← expandSimpExp y))
  | `(simp_exp| ($x, $y, $zs,*)) => do
    let rest ← `(simp_exp| ($y, $zs,*))
    `(pair $(← expandSimpExp x) $(← expandSimpExp rest))
  /- unOp -/
  | `(simp_exp| fst $e) => do `(Exp.unOp .fst $(← expandSimpExp e))
  | `(simp_exp| snd $e) => do `(Exp.unOp .snd $(← expandSimpExp e))
  /- heap -/
  | `(simp_exp| ! $e) => do `(load $(← expandSimpExp e))
  | `(simp_exp| ref $e) => do `(alloc $(← expandSimpExp e))
  | `(simp_exp| $e₁ ← $e₂) => do `(store $(← expandSimpExp e₁) $(← expandSimpExp e₂))
  | `(simp_exp| FAA $e₁ $e₂) => do `(faa $(← expandSimpExp e₁) $(← expandSimpExp e₂))
  /- concurrency -/
  | `(simp_exp| $e₁ || $e₂) => do `(Exp.par $(← expandSimpExp e₁) $(← expandSimpExp e₂))
  /- call/cc -/
  | `(simp_exp| call/cc (λ $x, $e)) => do `(Exp.callcc $(← expandSimpBinder x) $(← expandSimpExp e))
  | `(simp_exp| throw $e₁ to $e₂) => do `(Exp.throw $(← expandSimpExp e₁) $(← expandSimpExp e₂))
  /- app -/
  | `(simp_exp| $e₁ $e₂) => do `(Exp.app $(← expandSimpExp e₁) $(← expandSimpExp e₂))
  /- if -/
  | `(simp_exp| if $e₁ then $e₂ else $e₃) => do `(Exp.if $(← expandSimpExp e₁) $(← expandSimpExp e₂) $(← expandSimpExp e₃))
  /- rec, λ, let in, seq -/
  | `(simp_exp| let $x := $e₁ in $e₂) => do expandSimpExp $ ← `(simp_exp| (λ $x, $e₂) $e₁)
  | `(simp_exp| $e₁ ; $e₂) => do expandSimpExp $ ← `(simp_exp| (λ _, $e₂) $e₁)
  | `(simp_exp| rec $f:simp_binder $x:simp_binder := $e:simp_exp) => do
    `(Exp.rec_ $(← expandSimpBinder f) $(← expandSimpBinder x) $(← expandSimpExp e))
  | `(simp_exp| rec $f:simp_binder $x:simp_binder $xs:simp_binder* := $e:simp_exp) => do
    let rest ← `(simp_exp| rec _ $xs* := $e)
    `(Exp.rec_ $(← expandSimpBinder f) $(← expandSimpBinder x) $(← expandSimpExp rest))
  | `(simp_exp| λ $x:simp_binder , $e:simp_exp) => do
    `(Exp.rec_ Binder.anon $(← expandSimpBinder x) $(← expandSimpExp e))
  | `(simp_exp| λ $x:simp_binder $xs:simp_binder* , $e:simp_exp) => do
    let rest ← `(simp_exp| λ $xs* , $e)
    `(Exp.rec_ Binder.anon $(← expandSimpBinder x) $(← expandSimpExp rest))
  | `(simp_exp| skip) =>
    `(Exp.app (Exp.val (Val.rec_ Binder.anon Binder.anon (Exp.val (Val.lit BaseLit.unit)))) (Exp.val (Val.lit BaseLit.unit)))
  | `(simp_exp| assert $e) => do `(Exp.assert $(← expandSimpExp e))
  | `(simp_exp| $$($t:term)) => return t
  | s =>
    -- Lean doesn't allow `(simp_exp| $$$i:ident), so we have to check the syntax manually
    if s.getKind == `simp_exp.pseudo.antiquot && s.getArgs.size == 4
        && s[0].getKind == `«$» && s[1].getKind == `null && s[2].getKind == `ident
        && s[3].getKind == `null
    then
      `($(⟨s[2]⟩))
    else Macro.throwUnsupported


end

elab "[SIMP| " e:simp_exp "]" : term => do elabTerm (← liftMacroM $ expandSimpExp e) (some (.const `HITrees.Examples.SimpLang.Exp []))
-/
