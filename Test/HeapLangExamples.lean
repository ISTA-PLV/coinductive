import Test.HeapLang

open ITree
open ITree.Effects
open ITree.Exec

namespace HeapLang

example s :
  exec heaplangEH hl(#1 + #1).denote s λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, BinOp.denote, BinOp.evalInt]
    apply exec.stop
    simp

example tid tpool heap :
  tid < tpool.length →
  exec heaplangEH hl(let x := #1; x + #1).denote ⟨tid, tpool, heap⟩ λ t _ => t = return (.lit $ .int 2) := by
    intro _
    simp [Exp.denote, Exp.isVal, Exp.subst, Exp.substStr, yieldAfter, Exp.yieldIfNotVal, Val.rec!, BinOp.denote, BinOp.evalInt, -bind_pure_comp]
    apply exec_yield_same
    · simp [*]
    simp [-bind_pure_comp]
    apply exec_yield_same
    · simp [*]
    simp [-bind_pure_comp]
    apply exec.stop
    simp
