module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.Weyl
open Matrix Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
/-!
# A determinant-one coordinate transposition

The negative of the transposition of coordinates zero and two preserves the
identity Hermitian form and has determinant one in every characteristic.
Its conjugation swaps the two diagonal parameters in the actual SU image in
PGL. In particular it supplies the odd-characteristic swap without replacing
PSU by the larger projective unitary group.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), PDF pp.418–419;
GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
-/

@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
variable {F : Type*} [Field F]
variable (J : HermitianForm 3 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)
/-- The negative coordinate transposition, with its actual inverse. -/
def negativeSwapGL : GL (Fin 3) F where
  val := !![0, 0, -1; 0, -1, 0; -1, 0, 0]
  inv := !![0, 0, -1; 0, -1, 0; -1, 0, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
include hJ in
/-- Both the Hermitian and determinant-one equations hold. -/
theorem negativeSwapGL_special : negativeSwapGL (F := F) ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [negativeSwapGL, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
  · apply Units.ext
    simp [negativeSwapGL, GeneralLinearGroup.val_det_apply, Matrix.det_fin_three]
/-- The literal image of this SU element in the projective group. -/
def negativeSwap : ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective ⟨negativeSwapGL, negativeSwapGL_special J hJ⟩
/-- Conjugation exchanges the two independent norm-one coordinates. -/
theorem negativeSwap_diagonal (a : C × C) :
    negativeSwap J hJ * diagonalProjective J hJ C hC a * (negativeSwap J hJ)⁻¹ =
      diagonalProjective J hJ C hC (a.2, a.1) := by
  rw [negativeSwap, diagonalProjective, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalSpecial, diagonalGL_val, entries, negativeSwapGL, Matrix.mul_apply,
      Fin.sum_univ_succ, mul_assoc, mul_comm]
theorem negativeSwap_first (g : C) :
    negativeSwap J hJ * first J hJ C hC g * (negativeSwap J hJ)⁻¹ = second J hJ C hC g :=
  negativeSwap_diagonal J hJ C hC (g, 1)
theorem negativeSwap_second (g : C) :
    negativeSwap J hJ * second J hJ C hC g * (negativeSwap J hJ)⁻¹ = first J hJ C hC g :=
  negativeSwap_diagonal J hJ C hC (1, g)
end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
