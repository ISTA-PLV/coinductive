/- SPDX-License-Identifier: Apache-2.0 -/
module

import Lean
import ITree.Effect
import ITree.Effects

namespace ITree
open Lean Meta

axiom E1 : Effect.{0}
axiom E2 : Effect.{0}
axiom E3 : Effect.{0}
axiom i2 : E2.I

abbrev t1 := (E1 ⊕ₑ E2 ⊕ₑ E3).O (.inr (.inl i2))
abbrev t2 := E2.O i2

-- test the unification hint on SumE by checking that t1 and t2
-- are unifiable even at instance reducibility level
run_meta
  let .true ← isDefEqI (mkConst ``t1) (mkConst ``t2) | throwError "unification failed!"
