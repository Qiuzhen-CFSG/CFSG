module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Annihilators
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Generators
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints

/-!
# Published source row checks

The matrices and masks are in the published ATLAS column convention.
See AffineRestriction/source/README.md and SourceEquations/source/README.md.
Generated witness entries are untrusted; the accompanying proofs are checked
by Lean's kernel and use only the displayed mixed-space generators.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
open LinearMembership GeneratorCertificates Binary

def rowWitness2108 : Vector (Fin 90) 32 :=
  ⟨#[32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_2108 (S : RestrictionMatrix)
    (hS : PreservesMixedSpace (pairingAdjoint S))
    (k : Fin 32) : ev (flat S) (rawRows.get ⟨2108 + k.val, by omega⟩) = 0 := by
  have h : ∀ (k : Fin 32) (i : Fin 50), scan
      ((pairingAnnihilatorRows.get (rowWitness2108.get k)).get i) (generatorInverseRows.get 1).toList =
        (slices 50 50 (rawRows.get ⟨2108 + k.val, by omega⟩)).get i := by
    simp only [rawRows, slices, get_ofFn]
    decide +kernel
  apply adjoint_vanishes S hS _
    (annihilator_correct (adjointWitness.get (rowWitness2108.get k))) 1
  rw [← decode_slices]
  rw [← adjoint_left_correct]
  have ht := generator_inverse_correct (1 : Fin 5)
  have hu : (⟨(1 : Fin 5).val, by omega⟩ : Fin 40) = 1 := by decide +kernel
  rw [hu] at ht
  rw [← ht]
  exact (product_of_scan (pairingAnnihilatorRows.get (rowWitness2108.get k)) (generatorInverseRows.get 1) _ (h k)).symm

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
