import HeapLang.Lang
import HeapLang.Semantics
import HeapLang.Notation

open ITree ITree.Effects ITree.Exec

namespace HeapLang

/-- TODO: have a better simp set -/

example s :
  exec heaplangEH hl(#1 + #1).denote s λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, BinOp.denote, BinOp.evalInt]
    apply exec.stop
    simp

example tp heap :
  exec heaplangEH hl(let x := #1; x + #1).denote ⟨tp, heap⟩ λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, Exp.subst, Exp.substStr, yieldAfter, Exp.yieldIfNotVal, Val.rec!, BinOp.denote, BinOp.evalInt, -bind_pure_comp]
    apply exec_yield_same
    apply exec_yield_same
    apply exec.stop
    simp

-- set_option pp.explicit true in
example tp heap :
  exec heaplangEH hl(let x := #1; assert(x + #1 = #2)).denote ⟨tp, heap⟩ λ t _ => t = return (.lit $ .unit) := by
    simp [Exp.denote, Exp.assert, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed, Val.bool!, Exp.isVal, Exp.subst, Exp.substStr, yieldAfter, Exp.yieldIfNotVal, Val.rec!, BinOp.denote, BinOp.evalInt, -bind_pure_comp]
    apply exec_yield_same
    apply exec_yield_same
    apply exec_yield_same
    apply exec_yield_same
    unfold instOfNatBaseLit
    simp
    apply exec.stop
    simp
