module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.Diagonal
public import Mathlib.Algebra.CharP.Two

/-!
# Coordinate permutations of the projective unitary diagonal torus

The coordinate cycle acts by `(a,b) ↦ ((a*b)⁻¹,a)` and normalizes the
literal image in PGL. In characteristic two the coordinate transposition
has determinant one and exchanges the marked generators.

These are the Weyl elements for the local argument in Aschbacher–Smith
I.1.3(2), PDF p.418; GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
variable {F : Type*} [Field F]
variable (J : HermitianForm 3 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- The coordinate cycle, with its inverse matrix specified explicitly. -/
def cycleGL : GL (Fin 3) F where
  val := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  inv := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The transposition of the first and last coordinate. -/
def swapGL : GL (Fin 3) F where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

include hJ in
/-- The coordinate cycle preserves every identity Gram matrix and has determinant one. -/
theorem cycleGL_special : cycleGL (F := F) ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleGL, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
  · apply Units.ext
    simp [cycleGL, GeneralLinearGroup.val_det_apply, Matrix.det_fin_three]

include hJ in
/-- In characteristic two the coordinate transposition also has determinant one. -/
theorem swapGL_special [CharP F 2] : swapGL (F := F) ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapGL, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
  · apply Units.ext
    simp [swapGL, GeneralLinearGroup.val_det_apply, Matrix.det_fin_three, CharTwo.neg_eq]

/-- The projective coordinate three-cycle. -/
def cycle : ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective ⟨cycleGL, cycleGL_special J hJ⟩

/-- The projective coordinate transposition. -/
def swap [CharP F 2] : ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective ⟨swapGL, swapGL_special J hJ⟩

/-- The cycle acts on the two independent diagonal coordinates. -/
theorem cycle_diagonal (a : C × C) :
    cycle J hJ * diagonalProjective J hJ C hC a * (cycle J hJ)⁻¹ =
      diagonalProjective J hJ C hC ((a.1 * a.2)⁻¹, a.1) := by
  rw [cycle, diagonalProjective, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalSpecial, diagonalGL_val, entries, cycleGL, Matrix.mul_apply,
      Fin.sum_univ_succ, mul_assoc, mul_comm]

/-- The transposition swaps the two independent coordinates. -/
theorem swap_diagonal [CharP F 2] (a : C × C) :
    swap J hJ * diagonalProjective J hJ C hC a * (swap J hJ)⁻¹ =
      diagonalProjective J hJ C hC (a.2, a.1) := by
  rw [swap, diagonalProjective, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalSpecial, diagonalGL_val, entries, swapGL, Matrix.mul_apply,
      Fin.sum_univ_succ, mul_assoc, mul_comm]

theorem swap_first [CharP F 2] (g : C) :
    swap J hJ * first J hJ C hC g * (swap J hJ)⁻¹ = second J hJ C hC g :=
  swap_diagonal J hJ C hC (g, 1)

theorem swap_second [CharP F 2] (g : C) :
    swap J hJ * second J hJ C hC g * (swap J hJ)⁻¹ = first J hJ C hC g :=
  swap_diagonal J hJ C hC (1, g)

/-- The actual cycle has order dividing three, before and after projectivization. -/
theorem cycle_cube : cycle J hJ ^ 3 = 1 := by
  rw [cycle, ← map_pow]
  have hc : (⟨cycleGL, cycleGL_special J hJ⟩ : J.specialSubgroup) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleGL, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hc, map_one]

/-- Normalization holds for the image in PGL, with the scalar quotient retained. -/
theorem cycle_normalizes : cycle J hJ ∈ normalizer (torus J hJ C hC : Set _) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    rw [cycle_diagonal]
    exact ⟨_, rfl⟩
  · rintro ⟨a, ha⟩
    have he : cycle J hJ *
        diagonalProjective J hJ C hC (a.2, (a.1 * a.2)⁻¹) * (cycle J hJ)⁻¹ =
        diagonalProjective J hJ C hC a := by
      rw [cycle_diagonal]
      congr 1
      ext <;> simp [mul_comm]
    have hx : x = diagonalProjective J hJ C hC (a.2, (a.1 * a.2)⁻¹) := by
      have hh := ha.symm.trans he.symm
      exact mul_left_cancel (mul_right_cancel hh)
    rw [hx]
    exact ⟨_, rfl⟩

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
