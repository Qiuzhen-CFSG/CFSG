module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Linearization
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.DisplacementCoordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate

/-!
# Quadratic relations for the normalized exterior chart

An ambient matrix in the homology kernel preserving the invariant form and
exterior space satisfies the nine chart quadrics, provided its base image
reconstructs in the chart and has constant coordinate one. Reconstruction
places the displacement restriction in the certified linear space. Pairing
and exterior preservation then give the finite polynomial constraints, whose
Boolean certificate proves all nine quadrics after normalization.

Reconstruction and normalization remain explicit inputs for the parent kernel
restriction theorem to discharge. The chart is exactly `OrbitCover/Coordinates`
and `OrbitCover/Data`; invariant provenance and source motivation (GLS3,
Table 5.3i, printed p.270) are documented in `KernelEquations/source/README.md`.
See `QuadraticRelations/source/README.md` for the finite certificates.
-/

public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- Exterior-space preservation forces the nine quadrics for a reconstructed,
normalized base image in the original chart. -/
theorem matrix_quadratic_relations_of_exterior_stabilizer (g : BinaryMatrixˣ)
    (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hrec : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) =
      synthesize (coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule))))
    (hzero : coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)) 0 = 1) :
    ∀ i : Fin 9,
      coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)) (quadraticIndex i) =
        quadraticCoordinate i
          (freeCoordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule))) := by
  have hnorm : coordinates (restrictionImage (restrictionMatrix g)) 0 = 1 := by
    simpa only [restrictionImage_matrix g hker] using hzero
  have hquad := quadratic_relations_of_restriction (restrictionMatrix g)
    (restrictionMatrix_mem_linearSpace g hker hform hext hrec)
    (restrictionMatrix_pairing g hker hform)
    (restrictionTestForm_preserved g hker hext) hnorm
  simpa only [restrictionImage_matrix g hker] using hquad

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
