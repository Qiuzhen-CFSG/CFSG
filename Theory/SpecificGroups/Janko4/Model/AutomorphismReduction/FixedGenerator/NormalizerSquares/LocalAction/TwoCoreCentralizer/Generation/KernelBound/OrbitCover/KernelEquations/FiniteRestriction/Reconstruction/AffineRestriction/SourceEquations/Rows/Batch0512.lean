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

def rowWitness0512 : Vector (Fin 560) 32 :=
  ⟨#[512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543], rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_0512 (S : RestrictionMatrix)
    (hS : PreservesMixedSpace S)
    (k : Fin 32) : ev (flat S) (rawRows.get ⟨512 + k.val, by omega⟩) = 0 := by
  have h : ∀ (k : Fin 32) (i : Fin 50), scan
      ((generatorTransposeRows.get 0).get i) (slices 12 50 (annihilatorMask (rowWitness0512.get k))).toList =
        (slices 50 50 (rawRows.get ⟨512 + k.val, by omega⟩)).get i := by
    simp only [rawRows, slices, get_ofFn, Vector.toList_ofFn]
    decide +kernel
  apply right_vanishes S hS _
    (annihilator_correct (rowWitness0512.get k)) 0
  rw [← decode_slices]
  have ht := generator_transpose_correct (0 : Fin 5)
  have hu : (⟨(0 : Fin 5).val, by omega⟩ : Fin 40) = 0 := by decide +kernel
  rw [hu] at ht
  rw [← ht]
  exact (product_of_scan (generatorTransposeRows.get 0) (slices 12 50 (annihilatorMask (rowWitness0512.get k))) _ (h k)).symm

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
