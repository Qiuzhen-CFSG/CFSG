module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Annihilators
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Generators

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

def rowWitness0720 : Vector (Fin 560) 32 :=
  ⟨#[160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191], rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_0720 (S : RestrictionMatrix)
    (hS : PreservesMixedSpace S)
    (k : Fin 32) : ev (flat S) (rawRows.get ⟨720 + k.val, by omega⟩) = 0 := by
  have h : ∀ (k : Fin 32) (i : Fin 50), scan
      ((generatorTransposeRows.get 1).get i) (slices 12 50 (annihilatorMask (rowWitness0720.get k))).toList =
        (slices 50 50 (rawRows.get ⟨720 + k.val, by omega⟩)).get i := by
    simp only [rawRows, slices, get_ofFn, Vector.toList_ofFn]
    decide +kernel
  apply right_vanishes S hS _
    (annihilator_correct (rowWitness0720.get k)) 1
  rw [← decode_slices]
  have ht := generator_transpose_correct (1 : Fin 5)
  have hu : (⟨(1 : Fin 5).val, by omega⟩ : Fin 40) = 1 := by decide +kernel
  rw [hu] at ht
  rw [← ht]
  exact (product_of_scan (generatorTransposeRows.get 1) (slices 12 50 (annihilatorMask (rowWitness0720.get k))) _ (h k)).symm

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
