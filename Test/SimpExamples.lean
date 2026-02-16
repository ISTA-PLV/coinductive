import Test.SimpLang

open ITree
open ITree.Effects
open ITree.Exec

namespace SimpLang

example s :
  exec simpEH (Exp.denote (.binOp .plus (.val 1) (.val 1))) s λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, BinOp.denote]
    apply exec.bind
    simp [Val.int!]
    apply exec.stop
    simp
    apply exec.stop
    simp
