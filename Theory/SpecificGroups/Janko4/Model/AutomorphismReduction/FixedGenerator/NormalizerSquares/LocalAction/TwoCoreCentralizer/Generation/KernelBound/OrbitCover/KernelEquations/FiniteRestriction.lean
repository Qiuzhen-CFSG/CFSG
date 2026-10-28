module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Linearization
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorSpace
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.InvariantForm
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations

/-!
# Finite restrictions from the exterior-space stabilizer

The homology-kernel condition and preservation of the bilinear form and
exterior space force the base column into the explicit quadratic chart.
`Reconstruction` proves reconstruction and normalization in its 22 coordinates;
`QuadraticRelations` uses these conclusions to prove all nine quadratic
equations in the twelve free coordinates. The theorem below combines them,
discharging both extra premises of the quadratic-relations theorem.

The intended inputs are exactly `KernelConditions g`, preservation of
`invariantForm`, and membership in `formStabilizer exteriorFormSpace`.
See `KernelEquations/source/README.md` for the matrix and invariant provenance.
Source motivation: GLS3, Table 5.3i, printed p.270. This finite matrix
implication leaves ambient exterior-space invariance to the assembly owner.
-/

public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- The literal homology-kernel condition and preservation of the bilinear form
and exterior space imply reconstruction, normalization, and all nine chart
equations for the image of the base column. -/
theorem matrix_equations_of_exterior_stabilizer (g : BinaryMatrixˣ)
    (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace) :
    SatisfiesEquations ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)) := by
  obtain ⟨hrec, hzero⟩ :=
    matrix_reconstruction_of_exterior_stabilizer g hker hform hext
  exact ⟨hrec, hzero,
    matrix_quadratic_relations_of_exterior_stabilizer g hker hform hext hrec hzero⟩

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
