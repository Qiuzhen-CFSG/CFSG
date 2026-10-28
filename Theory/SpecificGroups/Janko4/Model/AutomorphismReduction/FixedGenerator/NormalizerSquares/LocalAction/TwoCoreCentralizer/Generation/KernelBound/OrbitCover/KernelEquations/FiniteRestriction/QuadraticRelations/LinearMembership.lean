module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.DisplacementCoordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Transport

/-!
# Linear restrictions on the displacement action

The exact inputs are the natural homology kernel, preservation of the ambient
form and exterior span, and reconstruction of the base image in the existing
22-column chart. No normalization is used.

The transport below identifies the two mixed-space preservation conditions
for the restriction and its pairing adjoint. RadicalCertificate identifies
and factors the actual mixed radical rows; FiniteAlgebra certifies that these
conditions and reconstruction imply membership in the published 125-generator
space. The final theorem assembles both certificates with no extra premises.
See LinearMembership/source/README.md for the finite contracts and retained
numerical discovery; provenance is source/README.md.
-/

public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open LinearMembership

/-- The original hypotheses give both linear stabilizer constraints and the
chart condition, once the concrete radical calculation is supplied. The
remaining implication to restrictionLinearSpace is a separate finite linear
algebra certificate. -/
theorem restrictionMatrix_mixed_linear_conditions (g : BinaryMatrixˣ)
    (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hrec : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) =
      synthesize (coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule))))
    (himage : mixedImageSpace = mixedSpace)
    (hfactor : ∀ R ∈ exteriorRadical displacementVectors,
      mixedEmbeddingᵀ * R =
        mixedEvaluation R * restrictionExtraction * (matrixA - 1)) :
    PreservesMixedSpace (restrictionMatrix g) ∧
      PreservesMixedSpace (pairingAdjoint (restrictionMatrix g)) ∧
      restrictionImage (restrictionMatrix g) =
        synthesize (coordinates (restrictionImage (restrictionMatrix g))) := by
  obtain ⟨hS, hAdj⟩ :=
    restrictionMatrix_mixed_constraints g hker hform hext himage hfactor
  refine ⟨hS, hAdj, ?_⟩
  simpa only [restrictionImage_matrix g hker] using hrec

/-- The homology kernel, preservation of the ambient form and exterior span,
and reconstruction of the base image force the displacement restriction into
the prescribed 125-generator linear space. No normalization is required. -/
theorem restrictionMatrix_mem_linearSpace (g : BinaryMatrixˣ)
    (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hrec : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) =
      synthesize (coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)))) :
    restrictionMatrix g ∈ restrictionLinearSpace := by
  obtain ⟨hS, hAdj, hImage⟩ := restrictionMatrix_mixed_linear_conditions g hker hform hext
    hrec mixedImageSpace_eq_mixedSpace radical_mixed_factorization
  exact mem_restrictionLinearSpace_of_mixed (restrictionMatrix g) hS hAdj hImage

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
