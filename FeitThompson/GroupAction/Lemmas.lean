module

public import FeitThompson.GroupAction.Defs

public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Basic

import FeitThompson.Commutator.Core
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupAction.Lemmas

open Theory.GroupAction

open scoped commutatorElement

-- The two legacy names used by some downstream consumers, as aliases for the
-- canonical Theory.GroupAction names (the `fixedPoints`- vs `fixedPoint`- prefix
-- and the `isTrivialAction`- vs `actsTrivially`- naming differences).
public abbrev fixedPointSubgroup_map_subtype_eq_inf {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H : Subgroup G) [IsInvariant A G H] :
    (fixedPointSubgroup A H).map H.subtype = H ⊓ fixedPointSubgroup A G := by
  simpa [fixedPointSubgroup] using fixedPoints_subgroup_map_subtype_eq_inf H

public theorem actsTrivially_of_isPGroup_on_cyclic_prime_order
    {A G : Type*} [Group A] [Group G] [Finite G] [MulDistribMulAction A G]
    {p : ℕ} (hp : Nat.Prime p) (hA : IsPGroup p A) (hG_cyclic : IsCyclic G)
    (hG_card : Nat.card G = p) :
    ActsTrivially (A := A) (G := G) := by
  intro a g
  exact (isTrivialAction_of_isPGroup_on_cyclic_prime_order hp hA hG_cyclic hG_card).acts_trivially a g
