module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Conjugation.Coordinates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Geometric conjugation by the plane SL₂ Levi

The hyperbolic correction of the flag basis commutes with the unipotent
coordinate matrices. A block calculation consequently gives the actual
conjugation formula, first in GL₅, then in the exact SU stabilizer, and finally
in the projective plane parabolic. The resulting coordinates are precisely
`Parameters.planeAction`.

Source: the standard unitary plane-parabolic calculation underlying
Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.12(7),
printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

namespace Parameters
variable {J}

theorem planeBasis_matrix (c : F) (u : Parameters J) :
    planeBasis c * matrix u * planeBasisInv c = ambientMatrix u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBasis, planeBasisInv, matrix, ambientMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

theorem ambientGL_eq_planeBasis (c : F) (u : Parameters J) :
    ambientGL u = planeBasisGL c * toGL u * (planeBasisGL c)⁻¹ := by
  apply Units.ext
  rw [ambientGL_val]
  exact (planeBasis_matrix c u).symm

omit [CharP F 2] in
private theorem block_entry (A : Matrix.SpecialLinearGroup (Fin 2) F) (i j : Fin 5) :
    (planeBlockMatrix J (planeSLtoGL A) * planeBlockInvMatrix J (planeSLtoGL A)) i j =
      (1 : Matrix (Fin 5) (Fin 5) F) i j :=
  congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j)
    (planeBlock_mul_inv J (planeSLtoGL A))

omit [CharP F 2] in
theorem planeBlock_conjugation (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (u : Parameters J) :
    planeBlockMatrix J (planeSLtoGL A) * matrix u *
      planeBlockInvMatrix J (planeSLtoGL A) = matrix (planeAction A u) := by
  ext i j
  have hv : (planeSLtoGL A).val = A.val := rfl
  have h := block_entry (J := J) A i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, planeBlockMatrix, planeBlockInvMatrix, planeAdjoint,
      planeMiddleScalar, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, hv] at h ⊢ <;>
    first | exact h | ring

theorem planeBlockGL_conjugation (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (u : Parameters J) :
    planeBlockGL J (planeSLtoGL A) * toGL u * (planeBlockGL J (planeSLtoGL A))⁻¹ =
      toGL (planeAction A u) := by
  apply Units.ext
  exact planeBlock_conjugation A u

theorem planeLeviGL_conjugation (c : F) (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (u : Parameters J) :
    planeLeviGL J c (planeSLtoGL A) * ambientGL u *
      (planeLeviGL J c (planeSLtoGL A))⁻¹ = ambientGL (planeAction A u) := by
  have h := congrArg (MulAut.conj (planeBasisGL c)) (planeBlockGL_conjugation A u)
  simp only [map_mul, map_inv] at h
  change planeLeviGL J c (planeSLtoGL A) * (planeBasisGL c * toGL u * (planeBasisGL c)⁻¹) *
    (planeLeviGL J c (planeSLtoGL A))⁻¹ =
      planeBasisGL c * toGL (planeAction A u) * (planeBasisGL c)⁻¹ at h
  simpa only [← ambientGL_eq_planeBasis c] using h

theorem planeSLStabilizer_conjugation (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : Matrix.SpecialLinearGroup (Fin 2) F) (u : Parameters J) :
    planeSLStabilizer J c hc hJ A * toStabilizer hJ u *
      (planeSLStabilizer J c hc hJ A)⁻¹ = toStabilizer hJ (planeAction A u) := by
  apply Subtype.ext
  apply Subtype.ext
  exact planeLeviGL_conjugation c A u

theorem planeSLParabolic_conjugation (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : Matrix.SpecialLinearGroup (Fin 2) F) (u : Parameters J) :
    planeSLParabolic J c hc hJ A * toParabolic hJ u *
      (planeSLParabolic J c hc hJ A)⁻¹ = toParabolic hJ (planeAction A u) := by
  let q : specialStabilizer J (plane F) →* planeParabolic J :=
    (project J).subgroupMap (specialStabilizer J (plane F))
  change q (planeSLStabilizer J c hc hJ A) * q (toStabilizer hJ u) *
    (q (planeSLStabilizer J c hc hJ A))⁻¹ = q (toStabilizer hJ (planeAction A u))
  rw [← map_inv, ← map_mul, ← map_mul, planeSLStabilizer_conjugation]

end Parameters
end Theory.SpecificGroups.UnitaryFive.PlaneCore
