module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.Reduction
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.ExternalWeights.InvariantSubspace

/-!
The tangent of a closed subgroup normalized by a torus decomposes into its
intersections with the ambient tangent weight spaces. For each normalizer
element we first restrict the actual conjugation morphism to the subgroup.
Differentiating and comparing coordinate pullbacks proves that the embedded
subgroup tangent is invariant. Rationality of the ambient conjugation
representation then supplies the invariant-subspace weight decomposition.

This proves the weight-decomposition input to the external-action reductions
for Borel III, 9.4--9.5 (`refs/KGroup/Bor1/Chapter3.tex`). Only normalization
by the torus is required; fixed-tangent lifting is a separate input.
-/

universe u

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

open Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Differentiated conjugation by a normalizer element preserves the embedded
tangent of a closed subgroup. -/
public theorem closedSubgroupTangent_invariant_of_mem_normalizer
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) (hg : g ∈ H.normalizer)
    (D : IdentityPointDerivation G) (hD : D ∈ closedSubgroupTangent H) :
    ((Theory.AlgebraicGroup.identityTangentRepresentation G).action g).1 D ∈
      closedSubgroupTangent H := by
  let cG : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G g
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  have hcH (x : Variety.Point H.carrierVariety) :
      (cG.comp H.inclusion).onPoints x ∈ H := by
    change g * H.inclusion.onPoints x * g⁻¹ ∈ H.toSubgroup
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp (H.pointEquiv x).property
  let cH : AlgebraicGroup.Morphism H.carrierVariety H.carrierVariety :=
    (cG.comp H.inclusion).codRestrictClosedSubgroup H hcH
  obtain ⟨E, rfl⟩ := hD
  refine ⟨Bor1.identityTangentMorphismLinearMap cH E, ?_⟩
  apply Derivation.ext
  intro a
  rw [Bor1.identityTangentMorphismLinearMap_apply, Bor1.identityTangentMorphismLinearMap_apply,
    Theory.AlgebraicGroup.identityTangentRepresentation_action_apply,
    Bor1.identityTangentMorphismLinearMap_apply]
  apply congrArg E
  apply Variety.PolynomialFunction.ext
  intro x
  change a (H.inclusion.onPoints (cH.onPoints x)) =
    a ((AlgebraicGroup.conjugationByMorphism G g).toFun (H.inclusion.onPoints x))
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  rfl

/-- The embedded tangent of a subgroup normalized by a closed torus is the
sum of its intersections with the torus's ambient tangent weight spaces. -/
public theorem hasExternalTangentWeightDecomposition_of_normalizes
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G)
    (hT : IsSubtorus T) (hTN : T ≤ H.normalizer) :
    HasExternalTangentWeightDecomposition H T := by
  apply closedSubtorusRepresentation_invariant_weightSpace_iSup_eq
    (Theory.AlgebraicGroup.identityTangentRepresentation G)
    (Theory.AlgebraicGroup.identityTangentRepresentation_isRational G) T hT
  intro t D hD
  exact closedSubgroupTangent_invariant_of_mem_normalizer H (T.includePoint t)
    (hTN (T.pointEquiv t).property) D hD

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
