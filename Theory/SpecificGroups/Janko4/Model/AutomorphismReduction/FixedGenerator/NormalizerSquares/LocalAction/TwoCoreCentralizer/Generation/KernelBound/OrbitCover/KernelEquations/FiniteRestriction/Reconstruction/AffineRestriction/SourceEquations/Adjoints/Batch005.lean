module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Witnesses

/-!
# Selected adjoint coefficient products

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
theorem adjoint_left_005 (k : Fin 5) :
    rectDecode 12 (pairingAnnihilatorRows.get ⟨5 + k.val, by omega⟩) =
      restrictionPairing * (rectDecode 50 (slices 12 50
        (annihilatorMask (adjointWitness.get ⟨5 + k.val, by omega⟩))))ᵀ := by
  have ht : rectDecode 12 (annihilatorTransposeRows.get ⟨5 + k.val, by omega⟩) =
      (rectDecode 50 (slices 12 50
        (annihilatorMask (adjointWitness.get ⟨5 + k.val, by omega⟩))))ᵀ := by
    have h : ∀ (k : Fin 5) (i : Fin 50) (j : Fin 12),
        ((annihilatorTransposeRows.get ⟨5 + k.val, by omega⟩).get i).testBit j.val =
          (annihilatorMask (adjointWitness.get ⟨5 + k.val, by omega⟩)).testBit
            (50 * j.val + i.val) := by decide +kernel
    ext i j
    simp only [rectDecode, Matrix.transpose_apply, slices, get_ofFn, bit,
      Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and, Nat.testBit_shiftRight]
    rw [h k i j]
  rw [← ht]
  symm
  apply product_of_scan restrictionPairingRows
  have h : ∀ (k : Fin 5) (i : Fin 50), scan (restrictionPairingRows.get i)
      (annihilatorTransposeRows.get ⟨5 + k.val, by omega⟩).toList =
        (pairingAnnihilatorRows.get ⟨5 + k.val, by omega⟩).get i := by decide +kernel
  exact h k

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
