module

public import FeitThompson.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Theory.GroupAction.Invariant

open scoped commutatorElement
open Theory.GroupAction

-- The legacy name `isInvariant_normalizer_of_isInvariant` (used by a couple of
-- downstream modules) is an alias for the canonical `isInvariant_normalizer`.
public abbrev isInvariant_normalizer_of_isInvariant {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H : Subgroup G) [IsInvariant A G H] :
    IsInvariant A G (Subgroup.normalizer H) :=
  Theory.GroupAction.isInvariant_normalizer H
