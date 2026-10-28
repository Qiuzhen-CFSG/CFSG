module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.Chart
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Directions
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Defect
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Exterior
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Span

/-!
# Elimination of the scalar reconstruction defect

On the span of the 124 published affine directions, two Frobenius functionals
combine the pairing and first exterior-form preservation equations into exactly
the scalar chart defect. The checked bilinear coefficients are symmetric, so the
cross terms vanish over F₂; the checked diagonal coefficients give the defect.
The second functional annihilates every original restricted exterior generator.
Thus the three hypotheses below force the defect to vanish, without any other
preservation, invertibility, normalization, or reconstruction premise.

The numerical witnesses are certified in the descendants of this module.
Source, provenance, and matrix conventions: `Reconstruction/source/README.md`.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction
open ScalarCertificate

/-- The two actual preservation equations eliminate the sole scalar chart defect
on the affine direction space. -/
theorem defectScalar_eq_zero_of_preservation (S : RestrictionMatrix)
    (haff : S - 1 ∈ affineDirections)
    (hpair : Sᵀ * restrictionPairing * S = restrictionPairing)
    (hext : Sᵀ * restrictionTestForm 0 * S ∈ restrictionExteriorSpace) :
    defectScalar (S - 1) = 0 := by
  have hdir (i : Fin 124) : polynomial (affineDirection i) = defectScalar (affineDirection i) := by
    rw [polynomial, direction_polynomial, defectScalar_direction]
  rw [← polynomial_on_span bilinear_direction_symmetric hdir haff,
    polynomial_preservation_expression, hpair, map_add, map_add,
    le_of_mem_restrictionExteriorSpace hext]
  have hE : le (restrictionTestForm 0) = 0 := exterior_annihilated 0
  have hc : ∀ c : ZMod 2, c + c = 0 := by decide
  simp only [hE, hc]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction
