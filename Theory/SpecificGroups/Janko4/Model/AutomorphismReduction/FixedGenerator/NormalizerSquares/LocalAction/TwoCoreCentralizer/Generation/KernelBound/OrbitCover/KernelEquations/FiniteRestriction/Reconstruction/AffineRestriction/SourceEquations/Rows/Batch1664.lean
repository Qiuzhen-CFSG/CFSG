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

def rowWitness1664 : Vector (Fin 560) 16 :=
  ⟨#[544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559], rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_1664 (S : RestrictionMatrix)
    (hS : PreservesMixedSpace S)
    (k : Fin 16) : ev (flat S) (rawRows.get ⟨1664 + k.val, by omega⟩) = 0 := by
  have h : ∀ (k : Fin 16) (i : Fin 50), scan
      ((generatorTransposeRows.get 2).get i) (slices 12 50 (annihilatorMask (rowWitness1664.get k))).toList =
        (slices 50 50 (rawRows.get ⟨1664 + k.val, by omega⟩)).get i := by
    simp only [rawRows, slices, get_ofFn, Vector.toList_ofFn]
    decide +kernel
  apply right_vanishes S hS _
    (annihilator_correct (rowWitness1664.get k)) 2
  rw [← decode_slices]
  have ht := generator_transpose_correct (2 : Fin 5)
  have hu : (⟨(2 : Fin 5).val, by omega⟩ : Fin 40) = 2 := by decide +kernel
  rw [hu] at ht
  rw [← ht]
  exact (product_of_scan (generatorTransposeRows.get 2) (slices 12 50 (annihilatorMask (rowWitness1664.get k))) _ (h k)).symm

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
