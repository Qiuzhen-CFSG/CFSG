module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.KernelSpanning.BasisData

/-!
# Reduced coordinate identities

Finite witness from the saved full Gaussian elimination. Every identity
is checked in Lean; see KernelSpanning/source/README.md.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
open LinearMembership GeneratorCertificates Binary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reduced_0100 (j : Fin 100) :
    reducedRow ⟨100 + j.val, by omega⟩ = 2 ^ (100 + j.val) ^^^
      xorList (List.ofFn (fun k : Fin 127 =>
        if (bs.get k).testBit (100 + j.val) then 2 ^ (free.get k).val else 0)) := by
  have h : ∀ j : Fin 100,
      reducedRow ⟨100 + j.val, by omega⟩ = 2 ^ (100 + j.val) ^^^
        xorList (List.ofFn (fun k : Fin 127 =>
          if (bs.get k).testBit (100 + j.val) then 2 ^ (free.get k).val else 0)) := by
    decide +kernel
  exact h j

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
