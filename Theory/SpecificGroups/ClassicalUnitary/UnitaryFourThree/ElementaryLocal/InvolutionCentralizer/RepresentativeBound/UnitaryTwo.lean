module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The order of the concrete two-dimensional unitary group over Nine

An orthonormal two-by-two matrix is determined by its first column `(a,b)`
and its determinant `d`: the second column is `(-d * star b, d * star a)`.
Conversely a unit first column and a norm-one scalar give such a matrix.
There are 24 unit columns and four norm-one scalars in `FiniteField.Nine`;
these two small counts are checked by kernel reduction. Thus GU₂(3) has
order 96, without enumerating all four matrix entries simultaneously.

This is the block-group order used to bound the full projective involution
centralizer in PSU₄(3). The convention GU = the full isometry group is that
of GLS3, chapter 2, §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

open Matrix
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeBound

private abbrev F := FiniteField.Nine
private abbrev U := Matrix.unitaryGroup (Fin 2) F
private abbrev UnitColumn := {v : F × F // star v.1 * v.1 + star v.2 * v.2 = 1}
private abbrev UnitScalar := {d : F // star d * d = 1}

private theorem column_card : Fintype.card UnitColumn = 24 := by decide
private theorem scalar_card : Fintype.card UnitScalar = 4 := by decide

private def matrix (v : UnitColumn) (d : UnitScalar) : Matrix (Fin 2) (Fin 2) F :=
  !![v.val.1, -d.val * star v.val.2; v.val.2, d.val * star v.val.1]

private theorem matrix_unitary (v : UnitColumn) (d : UnitScalar) :
    matrix v d ∈ Matrix.unitaryGroup (Fin 2) F := by
  rw [Matrix.mem_unitaryGroup_iff']
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j
  · simpa [matrix, Matrix.mul_apply, Fin.sum_univ_succ] using v.property
  · simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]; ring
  · simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]; ring
  · simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    calc
      _ = (star d.val * d.val) * (star v.val.1 * v.val.1 + star v.val.2 * v.val.2) := by ring
      _ = 1 := by rw [d.property, v.property, mul_one]

private theorem matrix_det (v : UnitColumn) (d : UnitScalar) : (matrix v d).det = d.val := by
  simp only [matrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  calc
    _ = d.val * (star v.val.1 * v.val.1 + star v.val.2 * v.val.2) := by ring
    _ = d.val := by rw [v.property, mul_one]

private def param (x : UnitColumn × UnitScalar) : U := ⟨matrix x.1 x.2, matrix_unitary x.1 x.2⟩

private theorem param_bijective : Function.Bijective param := by
  constructor
  · intro x y h
    have hm : matrix x.1 x.2 = matrix y.1 y.2 := congrArg Subtype.val h
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (congrArg (fun A => A 0 0) hm) (congrArg (fun A => A 1 0) hm)
    · apply Subtype.ext
      simpa only [matrix_det] using congrArg Matrix.det hm
  · intro A
    have hn : star (A.val 0 0) * A.val 0 0 + star (A.val 1 0) * A.val 1 0 = 1 := by
      have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 0 0)
        (Matrix.mem_unitaryGroup_iff'.mp A.property)
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
    have ho : star (A.val 0 0) * A.val 0 1 + star (A.val 1 0) * A.val 1 1 = 0 := by
      have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 0 1)
        (Matrix.mem_unitaryGroup_iff'.mp A.property)
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
    let v : UnitColumn := ⟨(A.val 0 0, A.val 1 0), hn⟩
    let d : UnitScalar := ⟨A.val.det, (Matrix.det_of_mem_unitary A.property).1⟩
    refine ⟨(v,d), ?_⟩
    apply Subtype.ext
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · change -A.val.det * star (A.val 1 0) = A.val 0 1
      rw [Matrix.det_fin_two]
      linear_combination (A.val 0 1) * hn - (A.val 0 0) * ho
    · rfl
    · change A.val.det * star (A.val 0 0) = A.val 1 1
      rw [Matrix.det_fin_two]
      linear_combination (A.val 1 1) * hn - (A.val 1 0) * ho

/-- The full identity-form unitary matrix group GU₂(3) has order 96. -/
public theorem unitaryTwo_card :
    Nat.card (Matrix.unitaryGroup (Fin 2) FiniteField.Nine) = 96 := by
  rw [← Nat.card_congr (Equiv.ofBijective param param_bijective), Nat.card_prod,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, column_card, scalar_card]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeBound
