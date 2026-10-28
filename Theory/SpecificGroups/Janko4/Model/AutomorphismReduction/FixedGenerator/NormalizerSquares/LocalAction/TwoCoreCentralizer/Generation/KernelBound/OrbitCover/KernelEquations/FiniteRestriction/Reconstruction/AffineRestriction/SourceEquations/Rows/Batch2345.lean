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

def rowWitness2345 : Vector (Fin 90) 28 :=
  ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_2345 (S : RestrictionMatrix)
    (hS : PreservesMixedSpace (pairingAdjoint S))
    (k : Fin 28) : ev (flat S) (rawRows.get ⟨2345 + k.val, by omega⟩) = 0 := by
  have h : ∀ (k : Fin 28) (i : Fin 50), scan
      ((pairingAnnihilatorRows.get (rowWitness2345.get k)).get i) (generatorInverseRows.get 4).toList =
        (slices 50 50 (rawRows.get ⟨2345 + k.val, by omega⟩)).get i := by
    simp only [rawRows, slices, get_ofFn]
    decide +kernel
  apply adjoint_vanishes S hS _
    (annihilator_correct (adjointWitness.get (rowWitness2345.get k))) 4
  rw [← decode_slices]
  rw [← adjoint_left_correct]
  have ht := generator_inverse_correct (4 : Fin 5)
  have hu : (⟨(4 : Fin 5).val, by omega⟩ : Fin 40) = 4 := by decide +kernel
  rw [hu] at ht
  rw [← ht]
  exact (product_of_scan (pairingAnnihilatorRows.get (rowWitness2345.get k)) (generatorInverseRows.get 4) _ (h k)).symm

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
