module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.QuotientGeometry

/-!
# The binary node-selection output

This intermediate output records an actual middle-node subgroup in the binary
four-dimensional component and an outer Sylow element. It does not assume an
S₈ equivalence or either permutation marking. Its construction from the proved
maximal invariant parabolic and the residual index three remains the binary
node inspection; the marking module carries out the subsequent transport.

Source: Aschbacher--Smith, 15.3.43, n = 1 paragraph, printed p.1140.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

/-- Geometric output of the binary node inspection, before choosing an
exceptional permutation comparison. -/
structure MiddleNodeData where
  linear : c.toComponentAction.image L ≃* LinearGroup 4
  basis : Basis 3
  intersection : ((c.toComponentAction.image (M ⊓ L)).subgroupOf
      (c.toComponentAction.image L)).map linear.toMonoidHom = minimalParabolic basis 1
  outer : ¬ c.toComponentAction.image S ≤ c.toComponentAction.image L


end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
