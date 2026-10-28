module

public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.Algebra.CharP.Two

/-!
# A Witt basis marking the prescribed isotropic line

In characteristic two a trace-one element `c` gives the Witt basis
`(1,1,0), (0,0,1), (c,c+1,0)` for the identity Hermitian form. Its first
vector marks the line used in the unitary-five flag calculation. The inverse
matrix and the Gram matrix are verified directly.

Source: the unitary parabolic calculation underlying Aschbacher--Smith,
F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Levi
variable {F : Type*} [Field F] [CharP F 2]

def lineBasis (c : F) : GL (Fin 3) F where
  val := !![1, 0, c; 1, 0, c + 1; 0, 1, 0]
  inv := !![c + 1, c, 0; 0, 0, 1; 1, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero,
        ← add_assoc, mul_add]
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero,
        ← add_assoc, mul_add, add_mul]
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

theorem lineBasis_gram (J : HermitianForm 3 F) (hJ : J.form = 1)
    (c : F) (hc : c + J.conj c = 1) :
    J.conjTranspose (lineBasis c).val * J.form * (lineBasis c).val =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  have hc' : J.conj c = c + 1 := by
    calc
      J.conj c = c + (c + J.conj c) := by simp [← add_assoc, CharTwo.add_self_eq_zero]
      _ = c + 1 := by rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineBasis, hJ, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, hc', CharTwo.add_self_eq_zero, add_mul, mul_add, add_left_comm, ← add_assoc]

theorem lineBasis_first (c : F) :
    (lineBasis c).val *ᵥ ![1, 0, 0] = ![1, 1, 0] := by
  ext i
  fin_cases i <;> simp [lineBasis, mulVec, dotProduct, Fin.sum_univ_three]
end Theory.SpecificGroups.UnitaryFive.LineCore.Levi
