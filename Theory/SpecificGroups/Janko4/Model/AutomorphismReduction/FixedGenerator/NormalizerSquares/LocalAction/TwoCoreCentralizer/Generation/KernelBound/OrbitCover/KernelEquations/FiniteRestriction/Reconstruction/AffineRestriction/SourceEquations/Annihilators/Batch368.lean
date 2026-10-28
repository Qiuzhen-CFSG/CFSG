module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Columns

/-!
# Mixed annihilator checks

The matrices and masks are in the published ATLAS column convention.
See AffineRestriction/source/README.md and SourceEquations/source/README.md.
Generated witness entries are untrusted; the accompanying proofs are checked
by Lean's kernel and use only the displayed mixed-space generators.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
open LinearMembership GeneratorCertificates Binary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem annihilator_368 (k : Fin 16) :
    ∀ j, pairing (rectDecode 50 (slices 12 50
      (annihilatorMask ⟨368 + k.val, by omega⟩))) (mixedGenerator j) = 0 := by
  apply annihilator_of_scan mixedColumns columns_correct
  have h : ∀ k : Fin 16, scan
      (annihilatorMask ⟨368 + k.val, by omega⟩) mixedColumns.toList = 0 := by
    decide +kernel
  exact h k

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
