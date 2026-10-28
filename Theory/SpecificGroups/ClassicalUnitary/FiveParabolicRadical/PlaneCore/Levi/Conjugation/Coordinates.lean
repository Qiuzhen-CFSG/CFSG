module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Restriction
import Mathlib.Tactic.LinearCombination

/-!
# Coordinates of the plane Levi action

The rule `(x,z) ↦ (A*x,A*z*A*)` preserves the Hermitian relation
`z + z* = x*x*` and the unipotent multiplication law. It therefore defines
an SL₂ action by automorphisms. The geometric conjugation identity and the
identification of the generated subgroup are established in `Conjugation`.

Source: the standard unitary plane-parabolic calculation underlying
Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.12(7),
printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

theorem planeAdjoint_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    planeAdjoint J (A * B) = planeAdjoint J B * planeAdjoint J A := by
  simp [planeAdjoint, Matrix.map_mul, Matrix.transpose_mul]

@[simp] theorem planeAdjoint_one : planeAdjoint J (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  simp [planeAdjoint]

namespace Parameters
variable {J}

def planeTransform (A : Matrix (Fin 2) (Fin 2) F) (u : Parameters J) : Parameters J where
  x := A *ᵥ u.x
  z := A * u.z * planeAdjoint J A
  relation := by
    intro i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      planeAdjoint, Matrix.transpose_apply, Matrix.map_apply, map_add, map_mul, conj_conj]
    linear_combination
      (A i 0 * J.conj (A j 0)) * u.relation 0 0 +
      (A i 0 * J.conj (A j 1)) * u.relation 0 1 +
      (A i 1 * J.conj (A j 0)) * u.relation 1 0 +
      (A i 1 * J.conj (A j 1)) * u.relation 1 1

@[simp] theorem planeTransform_x (A : Matrix (Fin 2) (Fin 2) F) (u : Parameters J) :
    (planeTransform A u).x = A *ᵥ u.x := rfl
@[simp] theorem planeTransform_z (A : Matrix (Fin 2) (Fin 2) F) (u : Parameters J) :
    (planeTransform A u).z = A * u.z * planeAdjoint J A := rfl

theorem planeTransform_mul (A : Matrix (Fin 2) (Fin 2) F) (u v : Parameters J) :
    planeTransform A (u * v) = planeTransform A u * planeTransform A v := by
  apply ext
  · simp [Matrix.mulVec_add]
  · ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      planeAdjoint, map_add, map_mul]
    ring

@[simp] theorem planeTransform_one (u : Parameters J) :
    planeTransform 1 u = u := by
  apply ext <;> simp

theorem planeTransform_comp (A B : Matrix (Fin 2) (Fin 2) F) (u : Parameters J) :
    planeTransform (A * B) u = planeTransform A (planeTransform B u) := by
  apply ext
  · simp [Matrix.mulVec_mulVec]
  · simp [planeAdjoint_mul, mul_assoc]

/-- The natural SL₂ action on the two unipotent coordinates. -/
def planeAction : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Parameters J) where
  toFun A :=
    { toFun := planeTransform A.val
      invFun := planeTransform A⁻¹.val
      left_inv := by
        intro u
        rw [← planeTransform_comp]
        change planeTransform (A⁻¹ * A).val u = u
        simp
      right_inv := by
        intro u
        rw [← planeTransform_comp]
        change planeTransform (A * A⁻¹).val u = u
        simp
      map_mul' := planeTransform_mul A.val }
  map_one' := by
    ext u : 1
    exact planeTransform_one u
  map_mul' A B := by
    ext u : 1
    exact planeTransform_comp A.val B.val u

@[simp] theorem planeAction_x (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (u : Parameters J) : (planeAction A u).x = A.val *ᵥ u.x := rfl

@[simp] theorem planeAction_z (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (u : Parameters J) : (planeAction A u).z = A.val * u.z * planeAdjoint J A.val := rfl

end Parameters
end Theory.SpecificGroups.UnitaryFive.PlaneCore
