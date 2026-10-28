module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.RationalMaps
/-!
# Preservation of the Leech bilinear form

The saved inverse matrices are transposes. Their checked inverse identities
therefore imply orthogonality on arbitrary rational vectors. The coordinate
bijection transports this identity to the actual Leech form.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices
open scoped Matrix BigOperators

def coordinateEquiv : Fin 24 ≃ Omega :=
  ⟨coordinate, coordinateIndex, coordinateIndex_coordinate, coordinateIndex_apply⟩

theorem reindex_form (x y : Fin 24 → ℚ) :
    rationalForm (reindex x) (reindex y) = (1 / 8 : ℚ) * (x ⬝ᵥ y) := by
  change (1 / 8 : ℚ) * (∑ i : Omega, x (coordinateIndex i) * y (coordinateIndex i)) = _
  exact congrArg ((1 / 8 : ℚ) * ·) (coordinateEquiv.symm.sum_comp (fun i => x i * y i))

theorem matrixAInv_transpose : matrixAInv = matrixA.transpose := by
  have h : matrixAInvData = matrixAData.transpose := by decide +kernel
  simp only [matrixAInv, matrixA, matrixAInvDataQ, matrixADataQ, h,
    Matrix.transpose_smul, Matrix.transpose_map]

theorem matrixBInv_transpose : matrixBInv = matrixB.transpose := by
  have h : matrixBInvData = matrixBData.transpose := by decide +kernel
  simp only [matrixBInv, matrixB, matrixBInvDataQ, matrixBDataQ, h,
    Matrix.transpose_smul, Matrix.transpose_map]

theorem matrix_preserves_dot (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hM : M.transpose * M = 1) (x y : Fin 24 → ℚ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ y := by
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec, dotProduct_comm]

theorem mapA_form (x y : RationalCoordinates) :
    rationalForm (mapA x) (mapA y) = rationalForm x y := by
  have hM : matrixA.transpose * matrixA = 1 := by
    rw [← matrixAInv_transpose]; exact matrixA_right
  change rationalForm (reindex (matrixA *ᵥ reindex.symm x))
    (reindex (matrixA *ᵥ reindex.symm y)) = _
  rw [reindex_form, matrix_preserves_dot _ hM]
  have h := reindex_form (reindex.symm x) (reindex.symm y)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem mapB_form (x y : RationalCoordinates) :
    rationalForm (mapB x) (mapB y) = rationalForm x y := by
  have hM : matrixB.transpose * matrixB = 1 := by
    rw [← matrixBInv_transpose]; exact matrixB_right
  change rationalForm (reindex (matrixB *ᵥ reindex.symm x))
    (reindex (matrixB *ᵥ reindex.symm y)) = _
  rw [reindex_form, matrix_preserves_dot _ hM]
  have h := reindex_form (reindex.symm x) (reindex.symm y)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
