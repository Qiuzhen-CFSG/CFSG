module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.Equations
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.KernelSpanning.Reduced
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.KernelSpanning.Candidates

/-!
# The kernel of the affine equations lies in the candidate span

The certified acyclic elimination reconstructs a solution from its 127 free
coordinates. Each reconstruction vector is a checked combination of the 124
published affine directions, identity, and the two scalar directions.
Consequently every solution of the 2373 raw equations lies in their span.
No mixed-space preservation or invertibility assumption is used here.

See AffineRestriction/source/README.md and KernelSpanning/source/README.md.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate
open LinearMembership GeneratorCertificates Binary KernelSpanning

/-- Completeness of the displayed homogeneous equations in the published candidate space. -/
theorem mem_candidateAlgebra_of_rawEquations (S : RestrictionMatrix)
    (hS : RawEquations S) : S ∈ candidateAlgebra := by
  have h := congrArg (@unflat 50 50) (reconstruct_solution S hS)
  rw [unflat_flat, unflat_sum] at h
  rw [h]
  apply Submodule.sum_mem
  intro k _
  rw [unflat_smul]
  exact Submodule.smul_mem _ _ (basis_mem k)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate
