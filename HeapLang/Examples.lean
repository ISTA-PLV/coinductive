/- SPDX-License-Identifier: Apache-2.0 -/
module

import HeapLang.Lang
-- This meta import is important such that lake build works
-- otherwise one gets a "Could not find native implementation of external declaration" error
meta import HeapLang.Lang
meta import HeapLang.Semantics
import HeapLang.Notation

open ITree ITree.Effects ITree.Exec ITree.Eval

namespace HeapLang

-- test that we can evaluate looping programs
/-- info: none -/
#guard_msgs in
#eval evalN heaplangM 10 hl((rec f x := f x) #1).denote

/-- info: some (HeapLang.Val.lit (HeapLang.BaseLit.int 2)) -/
#guard_msgs in
#eval evalN heaplangM 10000 hl(#1 + #1).denote

/-- info: some (HeapLang.Val.lit (HeapLang.BaseLit.unit)) -/
#guard_msgs in
#eval evalN heaplangM 10000 hl(let x := ref(#0); x ← #1; assert(!x = #1)).denote

/-- info: some (HeapLang.Val.lit (HeapLang.BaseLit.unit)) -/
#guard_msgs in
#eval evalN heaplangM 10000 hl(let x := ref(#1); assert(!x = #1); let y := #1; x ← y * #2; assert(!x = y + #1)).denote

/-- info: some (HeapLang.Val.lit (HeapLang.BaseLit.unit)) -/
#guard_msgs in
#eval evalN heaplangM 10000 hl(
  let x := ref(#0);
  fork(x ← !x + #1);
  x ← !x + #1;
  assert(!x = #2)).denote

-- show that there can be a data-race
/-- info: some (HeapLang.Val.lit (HeapLang.BaseLit.unit)) -/
#guard_msgs in
#eval evalN heaplangM 10000 hl(
  let x := ref(#0);
  fork(#1; x ← !x + #1);
  x ← !x + #1;
  assert(!x = #1)).denote

/- TODO: have a better simp set -/

example s :
  exec (heaplangEH λ _ => 0) hl(#1 + #1).denote s λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, BinOp.denote, BinOp.evalInt, -bind_pure_comp]
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec.stop
    simp

example tp heap :
  exec (heaplangEH λ _ => 0) hl(let x := #1; x + #1).denote ⟨tp, heap, 0, 0⟩ λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, Exp.subst, Exp.substStr, yieldAfter, Exp.yieldIfNotVal, Val.rec!, BinOp.denote, BinOp.evalInt, -bind_pure_comp]
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec_yield_same
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec_yield_same
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec.stop
    simp

example tp heap :
  exec (heaplangEH λ _ => 1) hl(let x := #1; x + #1).denote ⟨tp, heap, 0, 3⟩ λ t _ => t = return (.lit $ .int 2) := by
    simp [Exp.denote, Exp.isVal, Exp.subst, Exp.substStr, yieldAfter, Exp.yieldIfNotVal, Val.rec!, BinOp.denote, BinOp.evalInt, -bind_pure_comp]
    apply exec_step (λ _ => 1)
    · simp
    simp [-bind_pure_comp]
    apply exec_yield_same
    apply exec_step (λ _ => 1)
    · simp
    simp [-bind_pure_comp]
    apply exec_yield_same
    apply exec_step (λ _ => 1)
    · simp
    simp [-bind_pure_comp]
    apply exec.stop
    simp

-- set_option pp.explicit true in
example tp heap :
  exec (heaplangEH  λ _ => 0) hl(let x := #1; assert(x + #1 = #2)).denote ⟨tp, heap, 0, 0⟩ λ t _ => t = return (.lit $ .unit) := by
    simp [Exp.denote, Exp.assert, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed, Val.bool!, Exp.isVal, Exp.subst, Exp.substStr, yieldAfter, Exp.yieldIfNotVal, Val.rec!, BinOp.denote, BinOp.evalInt, -bind_pure_comp]
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec_yield_same
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec_yield_same
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec_yield_same
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec_yield_same
    unfold instOfNatBaseLit
    simp [-bind_pure_comp]
    apply exec_step_0
    simp [-bind_pure_comp]
    apply exec.stop
    simp
