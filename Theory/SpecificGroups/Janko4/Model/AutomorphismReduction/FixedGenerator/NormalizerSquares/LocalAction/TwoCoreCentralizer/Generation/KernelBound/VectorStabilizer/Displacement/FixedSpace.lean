module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.FirstChecks

/-!
# The fixed-column and scalar-kernel reductions

Subtracting the identity puts a marked restriction in the complete
fixed-column coefficient kernel. Its 103 directions share a nonzero
eigenvector. Invertibility of the original restriction excludes eigenvalue
one for its displacement, leaving the 102 displayed directions.

All numerical input is certified in FirstChecks; source/generate.py records
the recovery construction, using full linear remainders.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra

attribute [local irreducible] linearWords fixedWords nilWords firstEvaluationRows
  firstKernelWords firstFree firstRecoveryRows firstRemainderRows
  scalarEvaluationRows scalarKernelWords scalarFree scalarRecoveryRows scalarRemainderRows
  eigenvectorRows eigenvectorWord eigenvalueWords restrictionLinearBasis

theorem linear_words_decode (i : Fin 125) :
    packedMatrix (linearWords.get i) = restrictionLinearBasis i := by
  rw [packedMatrix, ← decode_slices, linear_words_rows]
  unfold restrictionLinearBasis
  rfl

theorem identity_mem : (1 : RestrictionMatrix) ∈ restrictionLinearSpace := by
  have h : packedMatrix (scan identityCoefficients linearWords.toList) = 1 := by
    rw [packedMatrix, ← decode_slices, identity_words, rectDecode_one]
  rw [← h]
  exact combination_mem restrictionLinearBasis linearWords linear_words_decode identityCoefficients

theorem fixed_basis_combination (k : Fin 103) :
    combination restrictionLinearBasis (fun i => bit (firstKernelWords.get k) i.val) =
      fixedBasis k := by
  change _ = packedMatrix (fixedWords.get k)
  rw [← fixed_combination_checks k, packed_combination]
  simp only [linear_words_decode]

theorem mem_fixedSpace {X : RestrictionMatrix} (hX : X ∈ restrictionLinearSpace)
    (hzero : X *ᵥ Pi.single 0 1 = 0) : X ∈ fixedSpace := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hX
  have hz : ∀ i, ev c (firstEvaluationRows.get i) = 0 := by
    intro i
    have he : ev c (firstEvaluationRows.get i) = (combination restrictionLinearBasis c) i 0 := by
      simp only [ev, combination, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_comm]
      unfold restrictionLinearBasis decodeRestrictionRows
      change c k * bit (firstEvaluationRows.get i) k.val =
        c k * bit ((restrictionLinearRows.get k).get i) 0
      simp only [bit, first_evaluation_bits]
    rw [he]
    change (∑ k, c k • restrictionLinearBasis k) i 0 = 0
    rw [hc]
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using congrFun hzero i
  have hk := coefficient_kernel firstEvaluationRows firstFree firstKernelWords
    firstRecoveryRows firstRemainderRows first_recovery_checks first_remainder_checks c hz
  have he := congrArg (combination restrictionLinearBasis) hk
  rw [map_sum] at he
  simp only [map_smul, fixed_basis_combination] at he
  change (∑ k, c k • restrictionLinearBasis k) = _ at he
  rw [hc] at he
  rw [he]
  exact Submodule.sum_mem _ (fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem displacement_mem_fixed {S : RestrictionMatrix} (hS : S ∈ restrictionLinearSpace)
    (hfirst : S *ᵥ Pi.single 0 1 = Pi.single 0 1) : S - 1 ∈ fixedSpace := by
  apply mem_fixedSpace (restrictionLinearSpace.sub_mem hS identity_mem)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfirst, sub_self]

theorem fixed_basis_eigenvector (k : Fin 103) :
    fixedBasis k *ᵥ eigenvector = bit (eigenvalueWords.get k) 0 • eigenvector := by
  change packedMatrix (fixedWords.get k) *ᵥ eigenvector = _
  rw [packedMatrix, ← decode_slices]
  apply packed_mulVec _ eigenvectorRows
  · intro i
    simp only [bit, eigenvector_rows, eigenvector]
  · intro i
    rw [eigenvector_checks]
    cases hb : (eigenvalueWords.get k).testBit 0
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, bit, Nat.testBit_zero,
        zero_smul, Pi.zero_apply]
      rfl
    · simp only [hb, ↓reduceIte, bit, eigenvector_rows, eigenvector,
        one_smul]

theorem nil_basis_combination (k : Fin 102) :
    combination fixedBasis (fun i => bit (scalarKernelWords.get k) i.val) = nilBasis k := by
  change _ = packedMatrix (nilWords.get k)
  rw [← nil_combination_checks k, packed_combination]
  rfl

/-- Invertibility excludes the nonzero eigenvalue of the displacement. -/
theorem displacement_mem_nil {S T : RestrictionMatrix} (hinv : T * S = 1)
    (hS : S ∈ restrictionLinearSpace)
    (hfirst : S *ᵥ Pi.single 0 1 = Pi.single 0 1) : S - 1 ∈ nilSpace := by
  have hfixed := displacement_mem_fixed hS hfirst
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hfixed
  let a : ZMod 2 := ∑ k : Fin 103, c k * bit (eigenvalueWords.get k) 0
  have heigen : (S - 1) *ᵥ eigenvector = a • eigenvector := by
    rw [← hc, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, fixed_basis_eigenvector, smul_smul]
    exact Finset.sum_smul.symm
  have ha : a = 0 := by
    rcases binary_scalar a with ha | ha
    · exact ha
    · have hzero : S *ᵥ eigenvector = 0 := by
        rw [ha, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec] at heigen
        have h := (sub_eq_iff_eq_add).mp heigen
        exact h.trans (by ext i; exact CharTwo.add_self_eq_zero _)
      have h := congrArg (fun v => T *ᵥ v) hzero
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_zero] at h
      exact (eigenvector_nonzero h).elim
  have hz : ∀ i : Fin 1, ev c (scalarEvaluationRows.get i) = 0 := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [← ha]
    dsimp [a, ev]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm]
    simp only [bit, scalar_evaluation_bits]
  have hk := coefficient_kernel scalarEvaluationRows scalarFree scalarKernelWords
    scalarRecoveryRows scalarRemainderRows scalar_recovery_checks scalar_remainder_checks c hz
  have he := congrArg (combination fixedBasis) hk
  rw [map_sum] at he
  simp only [map_smul, nil_basis_combination] at he
  change (∑ k, c k • fixedBasis k) = _ at he
  rw [hc] at he
  rw [he]
  exact Submodule.sum_mem _ (fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
