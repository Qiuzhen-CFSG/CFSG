module

public import Theory.Representation.Triality.RestrictedWeights.ConcretePBW
public import Theory.Representation.Triality.RestrictedWeights.ConcreteBasicFamily
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers

/-!
# Full covariant-space bounds for concrete triality interpolation

The proved PBW span bounds every cyclic extremal module. The actual fundamental
modules give nonempty positive and opposite cyclic families. Maximizing their
dimension constructs universal highest-weight covers; the matrix-coefficient
surjection then bounds the full spaces of covariant regular functions.
Only the shared universality input for the original Spin carrier remains.
Source: Steinberg 13.2(d), GLS3 2.8.1–2.8.2.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction ExtremalGrid
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k:Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu:IsUniversalVersion (groupVariety k))

/-- Both cyclic bounds concern every source module, including reducible ones. -/
theorem leftExtremalCyclicDimensionBounds (n:ℕ) :
    LeftExtremalCyclicDimensionBounds (finiteGeometry k hu) n :=
  ⟨cyclicHighest_dimensionBound k hu n,cyclicOppositeHighest_dimensionBound k hu n⟩

/-- Actual universal highest-weight covers for both Borel signs. -/
theorem exists_leftExtremalHighestWeightCovers (n:ℕ) :
    ∃ Cpos : HighestWeightCover (finiteGeometry k hu) (finiteGeometry k hu).bigCell.data.B
        ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n)),
      ∃ Cneg : HighestWeightCover (finiteGeometry k hu) (finiteGeometry k hu).bigCell.data.Bopp
        ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n))⁻¹,
        Module.finrank k Cpos.Space ≤ (2^n)^12 ∧
        Module.finrank k Cneg.Space ≤ (2^n)^12 :=
  exists_leftExtremalHighestWeightCovers_of_fundamentals_of_cyclicBounds
    (finiteGeometry k hu) n (fundamentalExistence k hu)
    (leftExtremalCyclicDimensionBounds k hu n)

/-- The full regular-function spaces satisfy the interpolation dimension bounds. -/
theorem leftDimensionBounds (n:ℕ) : LeftDimensionBounds (finiteGeometry k hu) n := by
  obtain ⟨Cpos,Cneg,hpos,hneg⟩ := exists_leftExtremalHighestWeightCovers k hu n
  exact leftDimensionBounds_of_highestWeightCovers (finiteGeometry k hu) n Cpos Cneg hpos hneg

end Triality.RestrictedWeights.Concrete
