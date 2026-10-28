module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.SelfAdjoint.Checked

/-!
# The complete self-adjoint displacement kernel

For a matrix in the published 102-generator nilpotent span, self-adjointness
for the actual restriction pairing is a linear equation on its coefficients.
The checked products identify its full matrix-valued evaluation; a recovery
identity reconstructs every coefficient vector in the kernel from 45 free
entries. Conversely, all 45 displayed coefficient vectors have zero full
evaluation. Their combinations of the original matrices are exactly the
published generators of selfAdjointSpace.

This proves the conditional finite helper with no group, generation, or
exterior-preservation hypothesis. It does not assert the parent's final
restriction theorem. See SelfAdjoint/source/README.md and source/README.md
for reproduction, the exact finite contract, and the original matrix source.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra

namespace SelfAdjointCertificate

attribute [local irreducible] productWords imageWords evaluationRows rowIndices columnIndices
  freeIndices recoveryRows remainderRows nilWords selfAdjointWords selfAdjointKernelWords
  restrictionPairingRows

/-- The linear equation imposing self-adjointness in characteristic two. -/
private def evaluation : RestrictionMatrix →ₗ[ZMod 2] RestrictionMatrix where
  toFun X := Xᵀ * restrictionPairing + restrictionPairing * X
  map_add' X Y := by
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' r X := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      RingHom.id_apply]

private theorem product_decode (k : Fin 102) :
    packedMatrix (productWords.get k) = restrictionPairing * nilBasis k := by
  change packedMatrix (productWords.get k) =
    rectDecode 50 restrictionPairingRows * packedMatrix (nilWords.get k)
  rw [packedMatrix, packedMatrix, ← decode_slices, ← decode_slices, ← decode_mulRows]
  congr 1
  apply Vector.ext
  intro i hi
  simpa only [slices, mulRows, Vector.getElem_ofFn] using
    (product_checks k ⟨i, hi⟩).symm

private theorem image_decode (k : Fin 102) :
    packedMatrix (imageWords.get k) = evaluation (nilBasis k) := by
  have h : packedMatrix (imageWords.get k) =
      (packedMatrix (productWords.get k))ᵀ + packedMatrix (productWords.get k) := by
    have hrows : slices 50 50 (imageWords.get k) =
        Vector.ofFn (fun i =>
          (transRows 50 (slices 50 50 (productWords.get k))).get i ^^^
            (slices 50 50 (productWords.get k)).get i) := by
      apply Vector.ext
      intro i hi
      change (slices 50 50 (imageWords.get k)).get ⟨i, hi⟩ =
        (Vector.ofFn _).get ⟨i, hi⟩
      simpa only [get_ofFn] using image_checks k ⟨i, hi⟩
    rw [packedMatrix, ← decode_slices, hrows, decode_xor_rows, decode_transRows,
      decode_slices]
    rfl
  rw [h, product_decode, Matrix.transpose_mul, restrictionPairing_transpose]
  rfl

private theorem evaluation_combination (c : Fin 102 → ZMod 2) (i : Fin 57) :
    ev c (evaluationRows.get i) =
      evaluation (combination nilBasis c) (rowIndices.get i) (columnIndices.get i) := by
  change _ = evaluation (∑ k, c k • nilBasis k) _ _
  rw [map_sum]
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← image_decode, ev]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]
  change c k * bit (evaluationRows.get i) k.val =
    c k * bit (imageWords.get k) ((columnIndices.get i).val + 50 * (rowIndices.get i).val)
  simp only [bit, evaluation_checks]

/-- Recovery of every coefficient, using the actual pairing equation. -/
private theorem kernel_reconstruct (c : Fin 102 → ZMod 2)
    (hc : evaluation (combination nilBasis c) = 0) :
    c = ∑ k : Fin 45, c (freeIndices.get k) •
      (fun i => bit (selfAdjointKernelWords.get k) i.val) := by
  apply coefficient_kernel evaluationRows freeIndices selfAdjointKernelWords
    recoveryRows remainderRows recovery_checks remainder_checks c
  intro i
  rw [evaluation_combination, hc]
  rfl

private theorem basis_combination (k : Fin 45) :
    combination nilBasis (fun i => bit (selfAdjointKernelWords.get k) i.val) =
      selfAdjointBasis k := by
  change _ = packedMatrix (selfAdjointWords.get k)
  rw [← combination_checks k, packed_combination]
  rfl

/-- Every displayed kernel vector vanishes on all 2500 output coordinates. -/
private theorem kernel_vanish (k : Fin 45) :
    evaluation (combination nilBasis (fun i => bit (selfAdjointKernelWords.get k) i.val)) = 0 := by
  have h := packed_combination imageWords (selfAdjointKernelWords.get k)
  rw [kernel_checks] at h
  simp only [image_decode] at h
  have hz : packedMatrix 0 = 0 := by ext i j; simp [packedMatrix, unflat, bit]
  rw [hz] at h
  rw [h]
  change evaluation (∑ i, bit (selfAdjointKernelWords.get k) i.val • nilBasis i) =
    ∑ i, bit (selfAdjointKernelWords.get k) i.val • evaluation (nilBasis i)
  rw [map_sum]
  simp only [map_smul]

/-- The displayed columns are the full kernel of the actual self-adjoint equation. -/
private theorem kernel_iff (c : Fin 102 → ZMod 2) :
    evaluation (combination nilBasis c) = 0 ↔
      ∃ d : Fin 45 → ZMod 2, c = ∑ k : Fin 45, d k •
        (fun i => bit (selfAdjointKernelWords.get k) i.val) := by
  constructor
  · intro hc
    exact ⟨fun k => c (freeIndices.get k), kernel_reconstruct c hc⟩
  · rintro ⟨d, rfl⟩
    rw [map_sum]
    simp only [map_smul]
    rw [map_sum]
    simp only [map_smul, kernel_vanish, smul_zero, Finset.sum_const_zero]

end SelfAdjointCertificate

attribute [local irreducible] nilWords selfAdjointWords selfAdjointKernelWords
  restrictionPairingRows restrictionPairing

/-- Self-adjoint members of the published 102-generator space lie in the
published 45-generator space, with no further matrix or group hypothesis. -/
theorem selfAdjoint_mem (X : RestrictionMatrix) (hX : X ∈ nilSpace)
    (hself : Xᵀ * restrictionPairing = restrictionPairing * X) :
    X ∈ selfAdjointSpace := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hX
  have hz : SelfAdjointCertificate.evaluation (combination nilBasis c) = 0 := by
    change (∑ i, c i • nilBasis i)ᵀ * restrictionPairing +
      restrictionPairing * (∑ i, c i • nilBasis i) = 0
    rw [hc, hself]
    ext i j
    exact CharTwo.add_self_eq_zero ((restrictionPairing * X) i j)
  obtain ⟨d, hk⟩ := (SelfAdjointCertificate.kernel_iff c).mp hz
  have he := congrArg (combination nilBasis) hk
  rw [map_sum] at he
  simp only [map_smul, SelfAdjointCertificate.basis_combination] at he
  change (∑ i, c i • nilBasis i) = _ at he
  rw [hc] at he
  rw [he]
  exact Submodule.sum_mem _ (fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
