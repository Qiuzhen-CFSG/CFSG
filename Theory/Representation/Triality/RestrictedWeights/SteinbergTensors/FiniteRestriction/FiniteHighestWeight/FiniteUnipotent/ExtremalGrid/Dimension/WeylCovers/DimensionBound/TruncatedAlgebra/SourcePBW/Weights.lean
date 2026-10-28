module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.WeightCone.RootActions

/-!
# Coefficient weights for the source straightening argument

Actual root coefficients preserve torus eigenvectors with the expected
character shift. Restricting any torus character to the supplied simple SL2
chart gives an integral diagonal weight. Both statements include the zero
vector, as required when a lowering word vanishes.

The coefficient shift reuses the established weight-cone API; the rank-one
comparison uses the chart's literal direct-diagonal coroot.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
lemma rootCoefficient_weight (S:Geometry K) (rho:RationalRepresentation K V)
    (hr:IsRationalRepresentation rho) (r:S.roots.Root) (j:ℕ)
    {χ:TorusWeight S.torus} {v:V} (hv:v∈weightSpace rho S.torus χ) :
    rootCoefficient S rho hr r j v∈weightSpace rho S.torus
      (χ*((S.roots.rootWeight r)⁻¹)^j) :=
  WeightCone.root_coefficient_weight S.roots S.realized rho hr r (S.rootParameter r) j hv
omit [FiniteDimensional k V] in
lemma rankOne_weight_of_torus (S:Geometry K) (i:Fin 4) (C:SimpleRootSL2Chart S i)
    (rho:RationalRepresentation K V) {χ:TorusWeight S.torus} {v:V}
    (hv:v∈weightSpace rho S.torus χ) : ∃m:ℤ,rankOneHasWeight (rankOneChartMap C) rho m v := by
  obtain ⟨a,ha⟩ := dLaurentCharacter_surjective 1 (χ.comp (S.leftSimpleCoroot i))
  refine ⟨a 0,?_⟩
  intro z
  change (rho.action ((rankOneChartMap C).onPoints
    (standardSL2DiagonalMorphism.onPoints (rankOneTorusPoint z)))).val v = _
  rw [rankOneChartMap_diagonal,hv]
  congr 1
  change (dPointEquiv 1 ((χ.comp (S.leftSimpleCoroot i)).onPoints (rankOneTorusPoint z)) 0 : k) = _
  rw [←ha,dLaurentCharacter_apply]
  simp only [Fin.prod_univ_one,rankOneTorusPoint_coordinate,Units.val_zpow_eq_zpow_val]
end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
