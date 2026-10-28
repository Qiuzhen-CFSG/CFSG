module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The cubic relations of the order-243 Sylow subgroup of J₃

For a generating pair `x,y`, write `c = [x,y]`, `d = [c,x]`, and
`e = [c,y]`, using Lean's convention `[a,b] = aba⁻¹b⁻¹`. The relevant
relations are `c³ = 1`, centrality of `d,e`, and
`x³ = d²e`, `y³ = d²e²`. This predicate specifies relations only; it
asserts neither an order nor a presentation or multiplier calculation.

The concrete consumer is `Sporadic.Janko3.ThreePrimary`, where the relations
are checked on the original degree-6156 permutations. Together with the
separate generation and order assertions they specify the local input to
the covering-kernel calculation for Aschbacher–Smith I.1.4(2), printed p.408.
The local structure is recorded in GLS III, Table 5.3h.
-/

namespace Theory.GroupTheory
open Subgroup
open scoped commutatorElement

/-- Relations for the marked cubic pair; cardinality and generation are separate. -/
public structure CubicClassThreePair {G : Type*} [Group G] (x y : G) : Prop where
  commutator_cube : ⁅x, y⁆ ^ 3 = 1
  left_central : ⁅⁅x, y⁆, x⁆ ∈ center G
  right_central : ⁅⁅x, y⁆, y⁆ ∈ center G
  left_cube : x ^ 3 = ⁅⁅x, y⁆, x⁆ ^ 2 * ⁅⁅x, y⁆, y⁆
  right_cube : y ^ 3 = ⁅⁅x, y⁆, x⁆ ^ 2 * ⁅⁅x, y⁆, y⁆ ^ 2

end Theory.GroupTheory
