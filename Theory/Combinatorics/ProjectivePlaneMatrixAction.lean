module

public import Theory.Combinatorics.FullCollineation
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Matrix collineations of the coordinate projective plane

In the orthogonality model, determinant-one matrices act on point vectors by
left multiplication and on line covectors by inverse transpose. The identity
`(Av) · ((A⁻¹)ᵀw) = v · w` proves that these two permutations preserve incidence.
This construction retains both coordinate actions without installing two
conflicting actions on the same projectivization type.
-/

namespace Matrix.SpecialLinearGroup

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- The contragredient homomorphism on determinant-one matrices. -/
@[expose] public def inverseTranspose : SpecialLinearGroup n K →* SpecialLinearGroup n K where
  toFun A := A⁻¹.transpose
  map_one' := by apply Subtype.ext; simp [transpose]
  map_mul' A B := by
    change ((A * B)⁻¹).transpose = (A⁻¹).transpose * (B⁻¹).transpose
    rw [_root_.mul_inv_rev]
    apply Subtype.ext
    exact Matrix.transpose_mul _ _

/-- The point and covector actions preserve their natural pairing. -/
public theorem dotProduct_inverseTranspose (A : SpecialLinearGroup n K) (v w : n → K) :
    (A • v) ⬝ᵥ (inverseTranspose A • w) = v ⬝ᵥ w := by
  change (A.val *ᵥ v) ⬝ᵥ (A⁻¹.val.transpose *ᵥ w) = v ⬝ᵥ w
  rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    ← coe_mul, inv_mul_cancel, coe_one, Matrix.one_mulVec, dotProduct_comm]

end Matrix.SpecialLinearGroup

namespace Configuration

open Projectivization

variable {K : Type*} [Field K]

/-- Incidence is preserved by the natural point action and contragredient line action. -/
public theorem specialLinear_mem_iff (A : Matrix.SpecialLinearGroup (Fin 3) K)
    (p l : Projectivization K (Fin 3 → K)) :
    A • p ∈ Matrix.SpecialLinearGroup.inverseTranspose A • l ↔ p ∈ l := by
  induction p using Projectivization.ind with | h v hv =>
  induction l using Projectivization.ind with | h w hw =>
  simp only [smul_mk, ofField.mem_iff, orthogonal_mk,
    Matrix.SpecialLinearGroup.dotProduct_inverseTranspose]

/-- The matrix-induced collineation, including its point and line permutations. -/
@[expose] public noncomputable def specialLinearCollineation :
    Matrix.SpecialLinearGroup (Fin 3) K →*
      Collineation (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K)) where
  toFun A := ⟨(MulAction.toPerm A,
    MulAction.toPerm (Matrix.SpecialLinearGroup.inverseTranspose A)),
    specialLinear_mem_iff A⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, MulAction.toPerm_one]
    rfl
  map_mul' A B := by
    apply Collineation.ext
    · intro p
      exact mul_smul A B p
    · intro l
      change (Matrix.SpecialLinearGroup.inverseTranspose (A * B)) • l = _
      rw [map_mul, mul_smul]
      rfl

@[simp] public theorem specialLinearCollineation_point
    (A : Matrix.SpecialLinearGroup (Fin 3) K) (p : Projectivization K (Fin 3 → K)) :
    Collineation.pointHom _ _ (specialLinearCollineation A) p = A • p := rfl

@[simp] public theorem specialLinearCollineation_line
    (A : Matrix.SpecialLinearGroup (Fin 3) K) (l : Projectivization K (Fin 3 → K)) :
    Collineation.lineHom _ _ (specialLinearCollineation A) l =
      Matrix.SpecialLinearGroup.inverseTranspose A • l := rfl

end Configuration
