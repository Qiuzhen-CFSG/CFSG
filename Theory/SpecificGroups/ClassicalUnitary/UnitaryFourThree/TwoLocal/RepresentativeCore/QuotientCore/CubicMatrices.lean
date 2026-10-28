module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Mathlib.LinearAlgebra.UnitaryGroup
/-!
# A cubic detector for GU₂(3) modulo its quaternion subgroup

An orthonormal first column and a norm-one determinant parametrize GU₂(3).
The two finite calculations below are checked by kernel reduction on these
24 × 4 parameters: commutators with a fixed cubic have cube in Q₈, and a
matrix centralizing this cubic modulo Q₈ has cube equal to a quaternion
matrix times the scalar determined by its determinant. Scalars are retained.

The parametrization proof adapts `RepresentativeBound/UnitaryTwo.lean`.
Source conventions: GLS3, chapter 2, §2.7. The application is the PSU₄(3)
case of Aschbacher–Smith, Theorem 0.1.2(4), printed p.4.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.CubicMatrices
private abbrev F := FiniteField.Nine
private abbrev U := Matrix.unitaryGroup (Fin 2) F
private abbrev UnitColumn := {v : F × F // star v.1 * v.1 + star v.2 * v.2 = 1}
private abbrev UnitScalar := {d : F // star d * d = 1}


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


def cubic : Mat₂ := !![⟨1,1⟩, ⟨1,1⟩; ⟨2,1⟩, ⟨1,2⟩]
def qmem (A : Mat₂) : Prop := ∃ q : QuaternionGroup 2, A = quaternionMatrix q
instance (A : Mat₂) : Decidable (qmem A) := inferInstanceAs (Decidable (∃ q, A = quaternionMatrix q))
def ccomm (A : Mat₂) : Mat₂ := A * cubic * A.conjTranspose * cubic.conjTranspose
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem param_comm_cube : ∀ x : UnitColumn × UnitScalar, qmem ((ccomm (param x).val) ^ 3) := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem param_central_cube : ∀ x : UnitColumn × UnitScalar,
    qmem (ccomm (param x).val) →
    ((param x).val.det = 1 ∨ (param x).val.det = -1) ∧
    ∃ q : QuaternionGroup 2, (param x).val ^ 3 =
      (if (param x).val.det = 1 then (1 : F) else imaginary) • quaternionMatrix q := by
  decide +kernel
theorem comm_cube (A : Matrix.unitaryGroup (Fin 2) FiniteField.Nine) : qmem ((ccomm A.val) ^ 3) := by
  obtain ⟨x,rfl⟩ := param_bijective.surjective A
  exact param_comm_cube x

theorem central_cube (A : Matrix.unitaryGroup (Fin 2) FiniteField.Nine) (h : qmem (ccomm A.val)) :
    (A.val.det = 1 ∨ A.val.det = -1) ∧
    ∃ q : QuaternionGroup 2, A.val ^ 3 =
      (if A.val.det = 1 then (1 : FiniteField.Nine) else imaginary) • quaternionMatrix q := by
  obtain ⟨x,rfl⟩ := param_bijective.surjective A
  exact param_central_cube x h

theorem cubic_unitary : cubic.conjTranspose * cubic = 1 := by decide
theorem cubic_det : cubic.det = 1 := by decide
theorem cubic_cube : cubic ^ 3 = 1 := by decide

theorem cubic_inv_not_scalar : ∀ (q : QuaternionGroup 2) (u : FiniteField.Nine),
    cubic.conjTranspose ≠ u • quaternionMatrix q := by decide +kernel

theorem scalar_quaternion_of_one : ∀ (q r : QuaternionGroup 2) (u : FiniteField.Nine),
    (1 : Mat₂) = u • quaternionMatrix r → qmem (u • quaternionMatrix q) := by
  decide +kernel

theorem scalar_unit (d : FiniteField.Nine) :
    IsUnit (if d = 1 then (1 : FiniteField.Nine) else imaginary) := by
  split_ifs <;> exact isUnit_iff_ne_zero.mpr (by decide)
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.CubicMatrices
