module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootRelations
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates.FixedFields

/-!
# The original finite triality cells in their actual cubic-field coordinates

The pinned root relations supply unique ordered coordinates and exact
Frobenius/diagram equivariance. Choose the genuine coefficient-field embedding;
the constructed witness preserves both literal root-product equations and
the actual elementary-subgroup inclusions, including at exponent one.
Source: Steinberg 6.2(b), 11.8 and 13.3(a).
-/

public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction ExtremalGrid
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k:Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu:IsUniversalVersion (groupVariety k))

/-- Both finite cells with their original root order and scalar embedding. -/
def cellCoordinates (n:ℕ) (hn:0<n) :
    TwistedCellCoordinates (finiteGeometry k hu) n (Standard.binaryParameters n hn) :=
  twistedCellCoordinates_of_relations (finiteGeometry k hu) (rootPairParameterRelations k hu)
    n hn (BinaryDegree.CarrierTransport.coefficientEmbedding k n hn)

/-- Exact cardinalities of the literal positive and negative finite cells. -/
theorem cellCardinalities (n:ℕ) (hn:0<n) : CellCardinalities (finiteGeometry k hu) n :=
  binary_cellCardinalities_of_coordinates (finiteGeometry k hu) n hn (cellCoordinates k hu n hn)

end Triality.RestrictedWeights.Concrete
