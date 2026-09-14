module

public import FeitThompson.GroupAction.Quotient
public import Theory.GroupAction.FixedPointTransport

open scoped Pointwise
open Theory.GroupAction

-- Legacy names, as explicit forwarders to the canonical Theory.GroupAction
-- `isTrivialActionOn*`-`fixedPoints`-prefixed theorems (naming difference only).
public theorem actsTriviallyOnSubgroup_iff_le_fixedPointSubgroup
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] (H : Subgroup G) :
    ActsTriviallyOnSubgroup (A := A) (G := G) (H := H) ↔ H ≤ FixedPoints.subgroup A G := by
  constructor
  · intro htriv x hx
    change ∀ a : A, a • x = x
    intro a
    exact htriv a x hx
  · intro hle
    intro a g hg
    exact (isTrivialActionOnSubgroup_of_le_fixedPoints_subgroup (A := A) (G := G) hle).acts_trivially a g hg

public theorem actsTriviallyOnSubgroup_of_le_fixedPointSubgroup
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] {H : Subgroup G} :
    H ≤ FixedPoints.subgroup A G → ActsTriviallyOnSubgroup (A := A) (G := G) (H := H) := by
  intro hle a g hg
  exact (isTrivialActionOnSubgroup_of_le_fixedPoints_subgroup (A := A) (G := G) hle).acts_trivially a g hg
