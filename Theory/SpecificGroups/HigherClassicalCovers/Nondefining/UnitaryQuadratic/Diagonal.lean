module

public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Torus
public import Theory.GroupTheory.PerfectCentralCoverThreeCycleNorm

/-!
# Permuting the rank-three unitary diagonal torus

The determinant-one norm-one diagonal torus maps to the literal SU image
in PGL. Its restriction to any odd-order subgroup of field units is injective:
a scalar in the kernel has order dividing four. Explicit signed transpositions
swap any two of the first three coordinates, compensating the determinant by
minus one on the fourth coordinate. An explicit three-cycle permutes the first
three coordinates and fixes the last. These matrices preserve the identity
Hermitian form in every characteristic.

These are the concrete normalizers for the three-cycle norm argument in
`UnitaryQuadratic.lean`, used for the covering-kernel step of Aschbacher–Smith
A.2.17, printed p.39, with the conventions of I.1.1–I.1.2, printed p.407.
The subgroup-index input remains separate.
-/

@[expose] public noncomputable section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open scoped IsMulCommutative

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic

variable {F : Type*} [Field F]
variable (J : HermitianForm 4 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- The actual projective image of the three-parameter determinant-one diagonal torus. -/
noncomputable def diagonalProjective : (Fin 3 → C) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (ProjectiveKernel.project J).comp (OddFourRanks.torusSpecial J hJ C hC)

/-- Odd-order coefficients exclude the fourth-torsion scalar kernel. -/
theorem diagonalProjective_injective [Finite F] (ho : (Nat.card C).Coprime 2) :
    Function.Injective (diagonalProjective J hJ C hC) := by
  have hfour (u : C) (hu : u ^ 4 = 1) : u = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (ho.pow_right 2)
      (orderOf_dvd_natCard u) (orderOf_dvd_of_pow_eq_one hu)
  intro a b h
  apply OddFourRanks.torusCentralizer_injective J hJ C hC hfour
  exact Subtype.ext h

/-- The three-cycle on the first three coordinates, fixing the fourth. -/
def cycleGL : GL (Fin 4) F where
  val := !![0,0,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1]
  inv := !![0,1,0,0; 0,0,1,0; 1,0,0,0; 0,0,0,1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The three coordinate swaps, with determinant corrected on the fourth coordinate. -/
def swapMatrix (k : Fin 3) : Matrix (Fin 4) (Fin 4) F :=
  ![!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,-1],
    !![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,-1],
    !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,-1]] k

/-- Each signed transposition is its own inverse. -/
def swapGL (k : Fin 3) : GL (Fin 4) F where
  val := swapMatrix k
  inv := swapMatrix k
  val_inv := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

include hJ in
/-- The coordinate three-cycle belongs to the actual special unitary subgroup. -/
theorem cycleGL_special : cycleGL (F := F) ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleGL, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
  · apply Units.ext
    simp [cycleGL, GeneralLinearGroup.val_det_apply, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ, Fin.succAbove]

include hJ in
/-- The signed transpositions preserve the form and have determinant one. -/
theorem swapGL_special (k : Fin 3) : swapGL (F := F) k ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, mul_one]
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [swapGL, swapMatrix, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
  · apply Units.ext
    fin_cases k <;>
      simp [swapGL, swapMatrix, GeneralLinearGroup.val_det_apply, Matrix.det_succ_row_zero,
        Fin.sum_univ_succ, Fin.succAbove]

/-- The actual projective image of the coordinate three-cycle. -/
noncomputable def cycle : ProjectiveSpecialUnitaryMatrixGroup J :=
  ProjectiveKernel.project J ⟨cycleGL, cycleGL_special J hJ⟩

/-- The actual projective image of a signed coordinate transposition. -/
noncomputable def swap (k : Fin 3) : ProjectiveSpecialUnitaryMatrixGroup J :=
  ProjectiveKernel.project J ⟨swapGL k, swapGL_special J hJ k⟩

private theorem cycleMatrix_diagonal (d : Fin 4 → F) :
    (cycleGL (F := F)).val * diagonal d * (cycleGL⁻¹).val =
      diagonal ![d 2,d 0,d 1,d 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleGL, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul_diagonal]

/-- Conjugation by the cycle rotates the independent diagonal parameters. -/
theorem cycle_diagonal (a : Fin 3 → C) :
    cycle J hJ * diagonalProjective J hJ C hC a * (cycle J hJ)⁻¹ =
      diagonalProjective J hJ C hC ![a 2,a 0,a 1] := by
  rw [cycle, diagonalProjective, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change cycleGL.val * (OddFourRanks.torusMatrix C a).val * (cycleGL⁻¹).val =
    (OddFourRanks.torusMatrix C ![a 2,a 0,a 1]).val
  rw [OddFourRanks.torusMatrix_val, OddFourRanks.torusMatrix_val, cycleMatrix_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [OddFourRanks.torusEntries, mul_assoc, mul_comm, mul_left_comm]

/-- The three transpositions on the independent parameters. -/
def swapEntries (k : Fin 3) (a : Fin 3 → C) : Fin 3 → C :=
  ![![a 1,a 0,a 2], ![a 2,a 1,a 0], ![a 0,a 2,a 1]] k

private theorem swapMatrix_diagonal (k : Fin 3) (d : Fin 4 → F) :
    (swapGL (F := F) k).val * diagonal d * ((swapGL k)⁻¹).val =
      diagonal (![![d 1,d 0,d 2,d 3], ![d 2,d 1,d 0,d 3], ![d 0,d 2,d 1,d 3]] k) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [swapGL, swapMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul_diagonal]

/-- Conjugation by each signed matrix has the indicated coordinate action. -/
theorem swap_diagonal (k : Fin 3) (a : Fin 3 → C) :
    swap J hJ k * diagonalProjective J hJ C hC a * (swap J hJ k)⁻¹ =
      diagonalProjective J hJ C hC (swapEntries C k a) := by
  rw [swap, diagonalProjective, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change (swapGL k).val * (OddFourRanks.torusMatrix C a).val * ((swapGL k)⁻¹).val =
    (OddFourRanks.torusMatrix C (swapEntries C k a)).val
  rw [OddFourRanks.torusMatrix_val, OddFourRanks.torusMatrix_val, swapMatrix_diagonal]
  congr 1
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [OddFourRanks.torusEntries, swapEntries, mul_assoc, mul_comm, mul_left_comm]

/-- The specified projective cycle has cube one. -/
theorem cycle_cube : cycle J hJ ^ 3 = 1 := by
  rw [cycle, ← map_pow]
  have hc : (⟨cycleGL, cycleGL_special J hJ⟩ : J.specialSubgroup) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleGL, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hc, map_one]

/-- Every pair of independent coordinates has an ambient special-unitary swap. -/
theorem exists_coordinate_swap (i j : Fin 3) (hij : i ≠ j) :
    ∃ s : ProjectiveSpecialUnitaryMatrixGroup J, ∀ u : C,
      s * diagonalProjective J hJ C hC (Pi.mulSingle i u) * s⁻¹ =
        diagonalProjective J hJ C hC (Pi.mulSingle j u) ∧
      s * diagonalProjective J hJ C hC (Pi.mulSingle j u) * s⁻¹ =
        diagonalProjective J hJ C hC (Pi.mulSingle i u) := by
  fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
  all_goals solve
  | refine ⟨swap J hJ 0, ?_⟩
    intro u
    constructor <;> rw [swap_diagonal] <;> congr 1 <;> ext l <;>
      fin_cases l <;> simp [swapEntries]
  | refine ⟨swap J hJ 1, ?_⟩
    intro u
    constructor <;> rw [swap_diagonal] <;> congr 1 <;> ext l <;>
      fin_cases l <;> simp [swapEntries]
  | refine ⟨swap J hJ 2, ?_⟩
    intro u
    constructor <;> rw [swap_diagonal] <;> congr 1 <;> ext l <;>
      fin_cases l <;> simp [swapEntries]

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
