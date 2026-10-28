module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.Normalizers.Obstructions
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.ResidualNormalizers.EndpointActions
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.ResidualNormalizers.FirstTail
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.ResidualNormalizers.LastHead

/-!
# The marked two-residual normalizer restriction in binary five-space

For distinct nonadjacent nodes, only the endpoint choices for beta need
exclusion. Four explicit conjugation obstructions give the required two
ordered pairs once the endpoint maximal parabolics normalize O². The
intermediate-kernel argument proves those bounds from the two-group property
of the actual complementary three-dimensional actions. In marked coordinates,
both action images are upper unitriangular over the binary field, hence
two-groups.

The final theorem discharges both action-image premises and restricts the
ordered pair to `(2, 0)` or `(1, 3)`, using zero-based node indices. The
identification of these actual O² residuals with the source's marked local
subgroups belongs to the parent assembly.
Source: Aschbacher–Smith, 13.8.25, combined manuscript of 1 March 2004,
printed p.960 (PDF p.977).
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi.ResidualNormalizers
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- The node restriction follows once both complementary action images are two-groups. -/
theorem fiveNodeResidual_normalizer_pair_of_action_ranges (b : FiveBasis)
    (hfirst : IsPGroup 2 (firstTailAction b).range)
    (hlast : IsPGroup 2 (lastHeadAction b).range)
    (beta delta : Fin 4)
    (hgap : beta.val + 1 < delta.val ∨ delta.val + 1 < beta.val)
    (hN : normalizer (fiveNodeResidual b beta : Set (LinearGroup 5)) ≤
      normalizer (fiveNodeResidual b delta : Set (LinearGroup 5))) :
    (beta = 2 ∧ delta = 0) ∨ (beta = 1 ∧ delta = 3) :=
  fiveNodeResidual_normalizer_pair_of_endpoint_bounds b
    (first_normalizer_of_tail_range_isPGroup b hfirst)
    (last_normalizer_of_head_range_isPGroup b hlast) beta delta hgap hN

/-- Normalizer containment for distinct nonadjacent marked nodes forces the
interior node and its unique nonadjacent partner, in either orientation. -/
theorem fiveNodeResidual_normalizer_pair (b : FiveBasis)
    (beta delta : Fin 4)
    (hgap : beta.val + 1 < delta.val ∨ delta.val + 1 < beta.val)
    (hN : normalizer (fiveNodeResidual b beta : Set (LinearGroup 5)) ≤
      normalizer (fiveNodeResidual b delta : Set (LinearGroup 5))) :
    (beta = 2 ∧ delta = 0) ∨ (beta = 1 ∧ delta = 3) :=
  fiveNodeResidual_normalizer_pair_of_action_ranges b
    (firstTailAction_range_isPGroup b) (lastHeadAction_range_isPGroup b)
    beta delta hgap hN

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
