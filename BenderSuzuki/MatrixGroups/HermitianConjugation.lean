module
public import BenderSuzuki.MatrixGroups.Unitary

/-!
# Hermitian preservation after a basis change

For the exact stored involution of a two-dimensional Hermitian form,
conjugating a matrix by an invertible basis matrix preserves the original
form exactly when the original matrix preserves the transported Gram matrix.
The proof reverses products under conjugate transpose and cancels the
invertible basis matrix and its adjoint on the two sides.

This shared criterion supports both alternating and symmetric hyperbolic
coordinates for the actual unitary group. The proof and its private adjoint
helpers were moved unchanged from ABG's special-unitary equivalence proof
(II.2 Lemma 1(vi), article p.17); the new hyperbolic-torus consumer uses the
same matrix/form identity. No coefficient or involution instances are replaced.
-/

open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F : Type*} [Field F]

private theorem adjoint_mul (J : HermitianForm 2 F)
    (A B : Matrix (Fin 2) (Fin 2) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm 2 F) :
    J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

private def adjointUnit (J : HermitianForm 2 F) (C : GL (Fin 2) F) : GL (Fin 2) F where
  val := J.conjTranspose C.val
  inv := J.conjTranspose (C⁻¹).val
  val_inv := by rw [← adjoint_mul]; simpa using adjoint_one J
  inv_val := by rw [← adjoint_mul]; simpa using adjoint_one J

public theorem conjugate_preserves_iff (J : HermitianForm 2 F) (C B : GL (Fin 2) F) :
    J.conjTranspose (C * B * C⁻¹).val * J.form * (C * B * C⁻¹).val = J.form ↔
    J.conjTranspose B.val * (J.conjTranspose C.val * J.form * C.val) * B.val =
      J.conjTranspose C.val * J.form * C.val := by
  have he :
      J.conjTranspose B.val * (J.conjTranspose C.val * J.form * C.val) * B.val =
        (adjointUnit J C).val *
          (J.conjTranspose (C * B * C⁻¹).val * J.form * (C * B * C⁻¹).val) * C.val := by
    simp only [Units.val_mul, adjoint_mul]
    change _ = (adjointUnit J C).val *
      (((adjointUnit J C)⁻¹).val * (J.conjTranspose B.val * (adjointUnit J C).val) *
        J.form * (C.val * B.val * (C⁻¹).val)) * C.val
    simp only [← mul_assoc, Units.mul_inv, one_mul, Units.inv_mul_cancel_right]
    rfl
  rw [he]
  change _ ↔ (adjointUnit J C).val * _ * C.val =
    (adjointUnit J C).val * J.form * C.val
  rw [Units.mul_left_inj, Units.mul_right_inj]


end BenderSuzuki.MatrixGroups.HermitianForm

