module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.SourceCharts.Sections
public import Theory.Representation.Triality.RestrictedWeights.ConcreteTopSource
public import Theory.Representation.Triality.RestrictedWeights.ConcreteBasicFamily
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers

/-!
# Both nonzero finite-cell sums for the actual Spin triality geometry

The proved fundamental modules supply the two cyclic extremal highest vectors.
The actual opposition word supplies a torus inverter, and the proved top-word
source gives nonvanishing in the published root order. SourceCharts constructs
the two covariant matrix coefficients, bounds their chart support, and extracts
the top coefficient. Mixed-grid interpolation then proves both literal cell sums.

Only the universal geometry and the actual fixed-cell coordinates remain inputs;
no representation-existence, chart, weight bound, coefficient or sum is assumed.
This includes n=1, hence the field of order two.

Source: Steinberg (1963), Sections 8--9; GLS3 Chapter2St2, 13.2(d), 13.3(a).
-/

public noncomputable section
open Theory.AlgebraicGroup Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction ExtremalGrid
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

/-- The actual two-sign norm-section conclusion, ready for finite realization. -/
theorem leftCellSums_of_coordinates (n : ℕ) (hn : 0 < n)
    (C : TwistedCellCoordinates (finiteGeometry k hu) n
      (Triality.Standard.binaryParameters n hn)) :
    LeftCellSums (finiteGeometry k hu) n := by
  obtain ⟨⟨A⟩,⟨B⟩⟩ := exists_leftExtremalCyclicHighestWeightModules_of_fundamentals
    (finiteGeometry k hu) n (fundamentalExistence k hu)
  obtain ⟨r,hi⟩ := exists_torus_inverter k hu
  constructor
  · exact SourceCharts.negative_cell_sum (finiteGeometry k hu) A.action A.rational n A.vector
      A.highest A.cyclic r hi
      (negative_topOperator_ne_zero k hu A.action A.rational n A.vector A.highest) _ C rfl
  · exact SourceCharts.positive_cell_sum (finiteGeometry k hu) B.action B.rational n B.vector
      B.highest B.cyclic r hi
      (positive_topOperator_ne_zero k hu B.action B.rational n B.vector B.highest) _ C rfl

end Triality.RestrictedWeights.Concrete
