module

public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# A noncentral element of order three in SU₃ in characteristic two

The cyclic coordinate permutation and the transposition of the first two
coordinates preserve the identity Hermitian form. In characteristic two both
have determinant one. Their matrices do not commute, and the cyclic one has
order three. These explicit elements lie in the full special unitary group.

The Ree centralizer assembly uses this witness to disprove normality of an
order-three subgroup after transporting the finite element-conjugacy theorem.
No order formula, simplicity result or projective quotient is used.

Source context: the universal SU₃ centralizer in GLS3, Table 4.7.3A,
`refs/KGroup/GLS3/chapter4.tex`, printed p.227. The proof here is a direct
calculation with the two permutation matrices.
-/

public section

open Matrix BenderSuzuki.MatrixGroups

namespace Matrix.SU3

variable {F : Type*} [Field F]

private def threeCycleSL : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

private def threeCycle (J : HermitianForm 3 F) (hJ : J.form = 1) :
    J.specialSubgroup :=
  ⟨SpecialLinearGroup.toGL threeCycleSL, by
    rw [J.mem_specialSubgroup_iff, hJ]
    constructor
    · change J.conjTranspose threeCycleSL.val * 1 * threeCycleSL.val = 1
      rw [mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [threeCycleSL, HermitianForm.conjTranspose, Matrix.mul_apply,
          Fin.sum_univ_three]
    · simp⟩

private theorem threeCycle_cube (J : HermitianForm 3 F) (hJ : J.form = 1) :
    threeCycle J hJ ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change threeCycleSL.val ^ 3 = (1 : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeCycleSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private theorem threeCycle_orderOf (J : HermitianForm 3 F) (hJ : J.form = 1) :
    orderOf (threeCycle J hJ) = 3 := by
  apply orderOf_eq_prime (threeCycle_cube J hJ)
  intro h
  have he := congrArg (fun A : J.specialSubgroup => A.val.val 0 0) h
  change (threeCycleSL (F := F)).val 0 0 = (1 : Matrix (Fin 3) (Fin 3) F) 0 0 at he
  simp [threeCycleSL] at he

private def swapSL [CharP F 2] : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

private def swap [CharP F 2] (J : HermitianForm 3 F) (hJ : J.form = 1) :
    J.specialSubgroup :=
  ⟨SpecialLinearGroup.toGL swapSL, by
    rw [J.mem_specialSubgroup_iff, hJ]
    constructor
    · change J.conjTranspose swapSL.val * 1 * swapSL.val = 1
      rw [mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [swapSL, HermitianForm.conjTranspose, Matrix.mul_apply,
          Fin.sum_univ_three]
    · simp⟩

/-- In characteristic two, coordinate permutations supply a noncentral
element of order three in the full special unitary group. -/
theorem exists_noncentral_order_three [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = 1) :
    ∃ x y : J.specialSubgroup, orderOf x = 3 ∧ x * y ≠ y * x := by
  refine ⟨threeCycle J hJ, swap J hJ, threeCycle_orderOf J hJ, ?_⟩
  intro h
  have he := congrArg (fun A : J.specialSubgroup => A.val.val 0 0) h
  change ((threeCycleSL (F := F)).val * (swapSL (F := F)).val) 0 0 =
    ((swapSL (F := F)).val * (threeCycleSL (F := F)).val) 0 0 at he
  simp [threeCycleSL, swapSL, Matrix.mul_apply, Fin.sum_univ_three] at he

end Matrix.SU3
