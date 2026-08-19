/- SPDX-License-Identifier: Apache-2.0 -/
module

import Lean
import ITree
meta import ITree

namespace Test
open ITree ITree.Effects ITree.Eval

def add_1_plus_1 : ITree failE Nat := do
  let x ← (pure 1);
  return x + 1

def add_1_plus_1_fail : ITree failE Nat := do
  let x ← (pure 1);
  fail s!"result: {x + 1}"

/-- info: Except.ok 2 -/
#guard_msgs in
#eval eval (Except String) add_1_plus_1

/-- info: Except.error "result: 2" -/
#guard_msgs in
#eval eval (Except String) add_1_plus_1_fail

local instance : MonadEval (ExceptT String Lean.Elab.Command.CommandElabM) Lean.Elab.Command.CommandElabM where
  monadEval x := do
    let r ← x
    match r with
    | .ok v => return v
    | .error msg => throw (Lean.Exception.error .missing s!"Evaluation failed with message: {msg}")

/-- error: Evaluation failed with message: result: 2 -/
#guard_msgs in
#eval eval (ExceptT String Lean.Elab.Command.CommandElabM) add_1_plus_1_fail

def print : Nat → ITree (logE Nat) Nat
  | 0 => return 0
  | n+1 => do log n; print n

/--
info: 9
---
info: 8
---
info: 7
---
info: 6
---
info: 5
---
info: 4
---
info: 3
---
info: 2
---
info: 1
---
info: 0
---
info: some 0
-/
#guard_msgs in
#eval evalN (Lean.Elab.Command.CommandElabM) 20000 (print 10)

def print_inf (n : Nat) : ITree (logE Nat) Empty :=
  do log n; print_inf (n + 1)
partial_fixpoint

/--
info: 0
---
info: 1
---
info: 2
---
info: 3
---
info: 4
---
info: none
-/
#guard_msgs in
#eval evalN (Lean.Elab.Command.CommandElabM) 5 (print_inf 0)

-- the following fails since the recursive occurrence is not under a lambda
-- #guard_msgs in
-- #eval evalN (Except String) 1 (ITree.spin (E:=failE) (R:=Empty))

def test_state : ITree (stateE Nat ⊕ₑ failE) Nat := do
  set 0;
  let x ← get;
  assert (x = 0)
  return x

local instance : MonadEval (StateT Nat (Except String)) IO where
  monadEval x := do
    let r := x.run 0
    match r with
    | .ok v => return v.1
    | .error msg => IO.ofExcept $ .error (s!"Evaluation failed: {msg}")

/-- info: some 0 -/
#guard_msgs in
#eval evalN (StateT Nat (Except String)) 20000 (test_state)

abbrev raceE := stateE Nat ⊕ₑ concE ⊕ₑ failE

abbrev raceM := StateT (ConcState ((n : Nat) × ITreeN raceE Nat n)) (StateT Nat (Except String))

local instance : MonadEval raceM IO where
  monadEval x := do
    let r := (x.run (ConcState.new)).run 0
    match r with
    | .ok v => return v.1.1
    | .error msg => IO.ofExcept $ .error (s!"Evaluation failed: {msg}")

def test_race : ITree raceE Nat := do
  set 0;
  fork (do let x ← get; yield; set (x + 1); yield)
  let x ← get; yield; set (x + 1); yield;

  let x' ← get; yield; assert (x' = 2); yield;
  return x'

def test_race_ok : ITree (stateE Nat ⊕ₑ concE ⊕ₑ failE) Nat := do
  set 0;
  fork (do let x ← get; yield; set (x + 1); yield)
  let x ← get; yield; set (x + 1); yield;

  let x' ← get; yield; assert (x' = 1); yield;
  return x'

def test_race_ok2 : ITree (stateE Nat ⊕ₑ concE ⊕ₑ failE) Nat := do
  set 0;
  fork (do let x ← get; yield; set (x + 1); yield)
  yield; yield; let x ← get; yield; set (x + 1); yield;

  let x' ← get; yield; assert (x' = 2); yield;
  return x'


/-- error: Evaluation failed: assertion failed -/
#guard_msgs in
#eval evalN raceM 20000 test_race

/-- info: some 1 -/
#guard_msgs in
#eval evalN raceM 20000 test_race_ok

/-- info: some 2 -/
#guard_msgs in
#eval evalN raceM 20000 test_race_ok2
