module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Extremal
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.CellPolynomialSums

/-!+# Left-weight extremal assembly from actual cell coordinates

The coordinate witness discharges both finite cardinality estimates. The
algebraic dimension bounds and nonzero sums of actual covariant functions are
still explicit. Their proofs, and construction of the coordinate witness, are
required before asserting unconditional extremal injectivity.

This sibling imports the left contracts without making the raw `ExtremalGrid`
module depend on its own consumer. Source: GLS3, Theorem 2.8.2, and Steinberg,
`Chapter2St2.tex`, Sections 13.2(d) and 13.3(a).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup ExtremalGrid
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Both left-weight clauses follow from the algebraic bounds, norm sections,
and actual finite root-coordinate charts. Every extra premise remains visible. -/
theorem leftExtremalCellInjectivity_of_coordinates (S : Geometry K) (n : ℕ)
    (hn : 0 < n)
    (C : TwistedCellCoordinates S n (Triality.Standard.binaryParameters n hn))
    (hdim : LeftDimensionBounds S n) (hsum : LeftCellSums S n) :
    LeftExtremalCellInjectivity S n :=
  leftExtremalCellInjectivity_of_dimension_of_sums S n hn hdim
    (binary_cellCardinalities_of_coordinates S n hn C) hsum

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
