module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Linearization
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.Chart
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Transport
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate

/-!
# Chart reconstruction from the exterior-space stabilizer

The kernel and the two invariant forms act on the literal fifty-dimensional
space of displacements. The mixed-radical image and row factorization imply
two linear right-stabilizer restrictions on this action. The certified finite
algebra calculation places each invertible such action in the displayed
affine space. The scalar certificate, using the displacement pairing and
the first exterior form, removes its one remaining scalar chart defect.
`Reconstruction.Chart` then supplies reconstruction and normalization.

The conditional reduction remains available; the final theorem discharges
every finite certificate under exactly the original three hypotheses.
See `Reconstruction/source/README.md` for the certificates, their provenance,
and the original ATLAS column conventions.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open LinearMembership Reconstruction

/-- Reduction of the original implication to independent finite certificates.
The assembly owner must supply every certificate before asserting the theorem
under only the kernel, bilinear-form and exterior-space hypotheses. -/
theorem matrix_reconstruction_of_finite_certificates
    (himage : mixedImageSpace = mixedSpace)
    (hfactor : ∀ R ∈ exteriorRadical displacementVectors,
      mixedEmbeddingᵀ * R =
        mixedEvaluation R * restrictionExtraction * (matrixA - 1))
    (haffine : ∀ S : RestrictionMatrix, IsUnit S →
      PreservesMixedSpace S → PreservesMixedSpace (pairingAdjoint S) →
        S - 1 ∈ affineDirections)
    (hscalar : ∀ S : RestrictionMatrix, S - 1 ∈ affineDirections →
      Sᵀ * restrictionPairing * S = restrictionPairing →
      Sᵀ * restrictionTestForm 0 * S ∈ restrictionExteriorSpace →
        defectScalar (S - 1) = 0)
    (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace) :
    let v := (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)
    v = synthesize (coordinates v) ∧ coordinates v 0 = 1 := by
  obtain ⟨hS, hAdj⟩ :=
    restrictionMatrix_mixed_constraints g hker hform hext himage hfactor
  have hunit : IsUnit (restrictionMatrix g) :=
    ⟨⟨restrictionMatrix g, restrictionMatrix (g⁻¹ : BinaryMatrixˣ),
      restrictionMatrix_mul_inverse g hker,
      restrictionMatrix_inverse_mul g hker⟩, rfl⟩
  have haff := haffine (restrictionMatrix g) hunit hS hAdj
  have hzero := hscalar (restrictionMatrix g) haff
    (restrictionMatrix_pairing g hker hform)
    (restrictionTestForm_preserved g hker hext 0)
  exact matrix_reconstruction_of_affine_and_scalar g hker haff hzero

/-- The literal homology-kernel condition and preservation of the ambient
bilinear form and exterior space force reconstruction and normalization in
the published twenty-two-column chart. -/
theorem matrix_reconstruction_of_exterior_stabilizer
    (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace) :
    let v := (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)
    v = synthesize (coordinates v) ∧ coordinates v 0 = 1 :=
  matrix_reconstruction_of_finite_certificates
    mixedImageSpace_eq_mixedSpace radical_mixed_factorization
    mem_affineDirections_of_mixed defectScalar_eq_zero_of_preservation
    g hker hform hext

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
