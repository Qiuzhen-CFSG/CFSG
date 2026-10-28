module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.NormalCentralizer.Blocks
/-!
# Quaternion normalization and scalar commutants on a unitary plane

A unitary matrix over Nine is determined by its first column and its
norm-one determinant. The finite plane calculation proves that it permutes
the eight literal quaternion matrices by conjugation. Commuting with the
two quaternion generators forces a scalar matrix.

All finite calculations are checked by kernel reduction. The unitary
parametrization follows the one in `RepresentativeBound.UnitaryTwo`.
Source: GLS3, chapter 2, §2.7, in the concrete field-of-nine model.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.NormalCentralizer

private def plane (a b d : FiniteField.Nine) : Mat₂ := !![a, -d * star b; b, d * star a]

private theorem unitary_shape (A : U₂) : A.val = plane (A.val 0 0) (A.val 1 0) A.val.det := by
  have hn : star (A.val 0 0) * A.val 0 0 + star (A.val 1 0) * A.val 1 0 = 1 := by
    have h := congrArg (fun B : Mat₂ => B 0 0) (Matrix.mem_unitaryGroup_iff'.mp A.property)
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
  have ho : star (A.val 0 0) * A.val 0 1 + star (A.val 1 0) * A.val 1 1 = 0 := by
    have h := congrArg (fun B : Mat₂ => B 0 1) (Matrix.mem_unitaryGroup_iff'.mp A.property)
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change A.val 0 1 = -A.val.det * star (A.val 1 0)
    rw [Matrix.det_fin_two]
    symm
    linear_combination (A.val 0 1) * hn - (A.val 0 0) * ho
  · rfl
  · change A.val 1 1 = A.val.det * star (A.val 0 0)
    rw [Matrix.det_fin_two]
    symm
    linear_combination (A.val 1 1) * hn - (A.val 1 0) * ho

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem plane_normalizes : ∀ a b d : FiniteField.Nine,
    star a * a + star b * b = 1 → star d * d = 1 →
    ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      plane a b d * quaternionMatrix q = quaternionMatrix r * plane a b d := by
  decide +kernel


theorem unitary_normalizes (A : U₂) (q : QuaternionGroup 2) :
    ∃ r : QuaternionGroup 2, A.val * quaternionMatrix q = quaternionMatrix r * A.val := by
  have hn : star (A.val 0 0) * A.val 0 0 + star (A.val 1 0) * A.val 1 0 = 1 := by
    have h := congrArg (fun B : Mat₂ => B 0 0) (Matrix.mem_unitaryGroup_iff'.mp A.property)
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
  have hd := (Matrix.det_of_mem_unitary A.property).1
  simpa only [← unitary_shape A] using
    plane_normalizes (A.val 0 0) (A.val 1 0) A.val.det hn hd q

private theorem entries_commuting_scalar : ∀ a b c d : FiniteField.Nine,
    (!![a,b;c,d] : Mat₂) * quaternionI = quaternionI * !![a,b;c,d] →
    (!![a,b;c,d] : Mat₂) * quaternionJ = quaternionJ * !![a,b;c,d] →
    (!![a,b;c,d] : Mat₂) = Matrix.scalar (Fin 2) a := by
  decide +kernel

theorem commuting_scalar (A : Mat₂)
    (hI : A * quaternionI = quaternionI * A)
    (hJ : A * quaternionJ = quaternionJ * A) :
    A = Matrix.scalar (Fin 2) (A 0 0) := by
  have he : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := by
    apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl
  have h := entries_commuting_scalar (A 0 0) (A 0 1) (A 1 0) (A 1 1)
  rw [← he] at h
  exact h hI hJ

theorem quaternionI_not_scalar (u : FiniteField.Nine) : quaternionI ≠ Matrix.scalar (Fin 2) u := by
  exact (by decide : ∀ u : FiniteField.Nine, quaternionI ≠ Matrix.scalar (Fin 2) u) u

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.NormalCentralizer
