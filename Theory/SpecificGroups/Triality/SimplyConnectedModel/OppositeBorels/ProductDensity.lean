module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.Tangents
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.ProductDensity.GeometricCriterion

/-!
# Density of the concrete Spin opposite product

The positive root-generated subgroup times the negative torus-and-root
candidate is Zariski dense in the concrete Clifford Spin group. The inclusion
differentials span its tangent space, so the regular multiplication map has
dense image. Containment of the positive root-generated subgroup in the
positive candidate gives density of the product of the two candidates.

This supplies the density part of Steinberg (6.2)(c),
`refs/KGroup/GLS3/Chapter2St2.tex`, for the actual carrier and root subgroups.
Borel certification and the remaining big-cell assertions are separate.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels
open Theory.AlgebraicGroup
open scoped Pointwise
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The concrete positive unipotent candidate times the negative candidate
is Zariski dense in Spin. -/
theorem positiveUnipotent_negativeCandidate_product_dense :
    Dense (((positiveUnipotent k).toSubgroup : Set (Points k)) *
      ((negativeCandidate k).toSubgroup : Set (Points k))) :=
  Bor1.closedSubgroup_product_dense_of_tangent_span
    (positiveUnipotent k) (negativeCandidate k) (SimplyConnected.isConnected k)
    (positiveUnipotent_negativeCandidate_tangent_span k)

/-- The pointwise product of the two concrete opposite candidates is
Zariski dense in Spin. -/
theorem candidates_product_dense :
    Dense (((positiveCandidate k).toSubgroup : Set (Points k)) *
      ((negativeCandidate k).toSubgroup : Set (Points k))) := by
  apply (positiveUnipotent_negativeCandidate_product_dense k).mono
  exact Set.mul_subset_mul
    (fun _ hx => rootGenerated_le_torusRootGenerated k (positiveRoots k) hx)
    (Set.Subset.refl _)

end Triality.SimplyConnected.OppositeBorels
