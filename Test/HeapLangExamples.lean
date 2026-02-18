import Test.HeapLang

open ITree
open ITree.Effects
open ITree.Exec

namespace HeapLang

example s :
  exec heaplangEH (Exp.denote (.binop .plus (.val 1) (.val 1))) s λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, BinOp.denote, BinOp.evalInt]
    -- apply exec.bind
    -- simp [Val.int!]
    -- apply exec.stop
    -- simp
    apply exec.stop
    simp
