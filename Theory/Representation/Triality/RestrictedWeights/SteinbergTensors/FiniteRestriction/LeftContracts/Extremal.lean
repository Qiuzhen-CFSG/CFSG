module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Cells
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid

/-!
# Extremal dimension and cell-sum obligations in left coordinates

Only the covariance character changes. All cells, inclusions, dimensions and
cardinality bounds remain the literal published ones. These definitions do
not assert the extremal calculation. Source: Steinberg §13.2(d) and §13.3.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

namespace ExtremalGrid
/-- The algebraic dimension estimate required for the two extremal spaces.
This is a proof obligation, not a field of `Geometry`. -/
def LeftDimensionBounds (S : Geometry K) (n : ℕ) : Prop :=
  (FiniteDimensional k (covariantSpace S S.roots.positive
      (S.leftWeightEmbedding (maximalRestrictedWeight n))) ∧
    Module.finrank k (covariantSpace S S.roots.positive
      (S.leftWeightEmbedding (maximalRestrictedWeight n))) ≤ (2 ^ n) ^ 12) ∧
  (FiniteDimensional k (covariantSpace S (S.roots.neg ⁻¹' S.roots.positive)
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) ∧
    Module.finrank k (covariantSpace S (S.roots.neg ⁻¹' S.roots.positive)
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) ≤ (2 ^ n) ^ 12)

/-- The two nonzero norm calculations, kept separate from evaluation injectivity. -/
def LeftCellSums (S : Geometry K) (n : ℕ) : Prop :=
  HasNonzeroCellSum S n S.roots.positive (S.roots.neg ⁻¹' S.roots.positive)
    (S.leftWeightEmbedding (maximalRestrictedWeight n)) ∧
  HasNonzeroCellSum S n (S.roots.neg ⁻¹' S.roots.positive) S.roots.positive
    (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹

end ExtremalGrid

/-- Conditional extremal assembly, preserving every finite cell and its size. -/
theorem leftExtremalCellInjectivity_of_dimension_of_sums (S : Geometry K) (n : ℕ)
    (hn : 0 < n) (hdim : ExtremalGrid.LeftDimensionBounds S n)
    (hcard : ExtremalGrid.CellCardinalities S n) (hsum : ExtremalGrid.LeftCellSums S n) :
    LeftExtremalCellInjectivity S n := by
  constructor
  · let := hdim.1.1
    apply ExtremalGrid.cellInjective_of_dimension_of_sum S n hn _ _ _
      (negativeRoots_isPGroup S) _ hsum.1
    rw [hcard.1]
    exact hdim.1.2
  · let := hdim.2.1
    apply ExtremalGrid.cellInjective_of_dimension_of_sum S n hn _ _ _
      (positiveRoots_isPGroup S) _ hsum.2
    rw [hcard.2]
    exact hdim.2.2

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
