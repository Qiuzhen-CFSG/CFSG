module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.Realization
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Extremal

/-!
# The algebraic branch of left extremal D4 interpolation

The full spaces of positive and negative covariant regular functions are
controlled by highest-weight covers for their actual Borel characters.
`Dimension.Realization` proves the needed surjective matrix-coefficient
comparison for every covariant function. Finite-dimensional covers with the
extremal Weyl bound remain explicit inputs below; constructing them is
required before asserting `leftDimensionBounds` unconditionally.

The left embedding and inverse opposite character are unchanged. The
reduction works for every exponent, in particular for the required `n = 1`.
Source: GLS3, Definition 2.8.1 and Theorem 2.8.2, and
`refs/KGroup/GLS3/Chapter2St2.tex`, 13.2(d).
-/

public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Highest-weight covers with the Weyl bound control both full spaces of
regular covariant functions. Their construction and bounds are explicit. -/
theorem leftDimensionBounds_of_highestWeightCovers (S : Geometry K) (n : ℕ)
    (Cpos : HighestWeightCover S S.bigCell.data.B
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (Cneg : HighestWeightCover S S.bigCell.data.Bopp
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (hpos : Module.finrank k Cpos.Space ≤ (2 ^ n) ^ 12)
    (hneg : Module.finrank k Cneg.Space ≤ (2 ^ n) ^ 12) :
    LeftDimensionBounds S n := by
  exact ⟨⟨Cpos.covariantSpace_finite S.bigCell.data.positive_witness,
      (Cpos.finrank_covariantSpace_le S.bigCell.data.positive_witness).trans hpos⟩,
    ⟨Cneg.covariantSpace_finite S.bigCell.data.opposite_witness,
      (Cneg.finrank_covariantSpace_le S.bigCell.data.opposite_witness).trans hneg⟩⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
