import ITree

namespace Test
open ITree

def f {E R} : ITree E R := f
partial_fixpoint

def spin2 {E R} : ITree E R := ITree.tau spin2
partial_fixpoint

example {E R} : @spin2 E R = spin2 := by unfold spin2; rfl

-- TODO: I did not expect this to work. I guess it works, but we cannot prove it monotone
def test (t1 : ITree E R) : ITree E R :=
  match t1.unfold with
  | .ret r => return r
  | .tau t => test t
  | .vis i k => .vis i (λ o => test (k o))
partial_fixpoint
