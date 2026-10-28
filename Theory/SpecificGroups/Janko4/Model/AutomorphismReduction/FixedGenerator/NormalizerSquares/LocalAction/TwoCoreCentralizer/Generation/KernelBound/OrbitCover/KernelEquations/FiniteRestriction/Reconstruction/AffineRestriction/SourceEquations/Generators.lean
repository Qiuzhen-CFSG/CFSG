module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Witnesses

/-!
# Mixed generator transposes and inverse products

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
theorem generator_transpose_correct (u : Fin 5) :
    rectDecode 12 (generatorTransposeRows.get u) =
      (mixedGenerator ⟨u.val, by omega⟩)ᵀ := by
  have h : ∀ (u : Fin 5) (i : Fin 50) (j : Fin 12),
      ((generatorTransposeRows.get u).get i).testBit j.val =
        ((mixedGeneratorRows.get ⟨u.val, by omega⟩).get j).testBit i.val := by
    decide +kernel
  ext i j
  exact congrArg (fun b => if b then (1 : ZMod 2) else 0) (h u i j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem generator_inverse_correct (u : Fin 5) :
    rectDecode 50 (generatorInverseRows.get u) =
      mixedGenerator ⟨u.val, by omega⟩ * pairingInverse := by
  symm
  apply product_of_scan (mixedGeneratorRows.get ⟨u.val, by omega⟩) pairingInverseRows
  have h : ∀ (u : Fin 5) (i : Fin 12),
      scan ((mixedGeneratorRows.get ⟨u.val, by omega⟩).get i) pairingInverseRows.toList =
        (generatorInverseRows.get u).get i := by decide +kernel
  exact h u

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
