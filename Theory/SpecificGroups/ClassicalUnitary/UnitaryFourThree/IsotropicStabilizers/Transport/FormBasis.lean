module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.Coordinates

/-!
# An isometry from the antidiagonal form to the identity form over Nine

Normalize the antidiagonal Hermitian form by an orthonormal basis, using the
cube involution and the actual cardinality nine. The inverse basis matrix has
Gram matrix equal to the antidiagonal form in the identity Hermitian space.
This supplies a genuine ambient isometry; prescribing the image of an isotropic
line or plane requires an additional basis construction.

Source: Huppert II.10.4, via `PrimeFrobeniusNormalization`; the unitary conventions
and Witt extension statement in GLS3, chapter 2, section 2.7. This is a geometric
input for the condition K contribution to Aschbacher–Smith, Theorem 0.1.2(4),
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers

/-- The identity and antidiagonal forms over Nine are actually isometric. -/
theorem exists_coordinate_form_basis : ∃ C : GL (Fin 4) FiniteField.Nine,
    (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form := by
  let : CharP FiniteField.Nine 3 :=
    charP_of_card_eq_prime_pow (p := 3) (f := 2) (by norm_num)
  obtain ⟨P, hP⟩ := coordinateForm.exists_orthonormal_basis_of_prime_frobenius
    coordinateForm_conj_cube (by norm_num)
  refine ⟨P⁻¹, ?_⟩
  change (P⁻¹).val.conjTranspose * 1 * (P⁻¹).val = coordinateForm.form
  have hP' : P.val.conjTranspose * coordinateForm.form * P.val = 1 := hP
  have hcancel : (P⁻¹).val.conjTranspose * P.val.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul]
    simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.conjTranspose_one]
  calc
    (P⁻¹).val.conjTranspose * 1 * (P⁻¹).val =
        (P⁻¹).val.conjTranspose *
          (P.val.conjTranspose * coordinateForm.form * P.val) * (P⁻¹).val := by rw [hP']
    _ = coordinateForm.form := by
      simp only [← mul_assoc, hcancel, one_mul, Units.mul_inv_cancel_right]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
