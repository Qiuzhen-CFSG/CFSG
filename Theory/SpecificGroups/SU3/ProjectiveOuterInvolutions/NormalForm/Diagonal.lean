module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation

/-!
# Eliminating involutions in the diagonal quotient of PSU₃

For any unitary `u`, its determinant has norm one. The unitary matrix
`det(u)⁻¹ • u³` has determinant one and the same image in PGL as `u³`.
Consequently every cube of a unitary conjugation is inner, and an involutory
unitary conjugation must itself be inner.

This is the exponent-three consequence of the diagonal quotient calculation
in GLS, Volume 3, Theorem 2.5.12(c), proved directly on the exact matrix image.
It requires no order formula or simplicity assertion for PSU₃.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

public theorem unitary_det_norm_one (u : J.unitarySubgroup) :
    J.conj u.val.val.det * u.val.val.det = 1 := by
  have h := congrArg Matrix.det ((J.mem_unitarySubgroup_iff _).mp u.property)
  have hadj : (J.conjTranspose u.val.val).det = J.conj u.val.val.det := by
    change ((u.val.val.map J.conj).transpose).det = _
    rw [Matrix.det_transpose]
    exact (J.conj.map_det _).symm
  rw [Matrix.det_mul, Matrix.det_mul, hadj] at h
  exact (mul_right_cancel₀ J.form_nondegenerate) (by
    calc
      (J.conj u.val.val.det * u.val.val.det) * J.form.det =
          J.conj u.val.val.det * J.form.det * u.val.val.det := by ring
      _ = 1 * J.form.det := by simpa using h)

public theorem scalar_mem_unitary_of_norm_one (d : Eˣ) (hd : J.conj (d : E) * d = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) d ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (Matrix.scalar (Fin 3) (d : E)) * J.form *
    Matrix.scalar (Fin 3) (d : E) = J.form
  have hadj : J.conjTranspose (Matrix.scalar (Fin 3) (d : E)) =
      Matrix.scalar (Fin 3) (J.conj d) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply]
    · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
  rw [hadj]
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  calc
    J.conj (d : E) * J.form i j * d = (J.conj (d : E) * d) * J.form i j := by ring
    _ = J.form i j := by rw [hd, one_mul]

public theorem unitaryConj_cube_is_inner (u : J.unitarySubgroup) :
    ∃ b : ProjectiveSpecialUnitaryMatrixGroup J, (J.unitaryConj u)^3 = MulAut.conj b := by
  let d := Matrix.GeneralLinearGroup.det u.val
  have hd : J.conj ((d⁻¹ : Eˣ) : E) * ((d⁻¹ : Eˣ) : E) = 1 := by
    simp only [Units.val_inv_eq_inv_val, d, Matrix.GeneralLinearGroup.val_det_apply]
    change J.conj (u.val.val.det⁻¹) * u.val.val.det⁻¹ = 1
    rw [map_inv₀, ← mul_inv, unitary_det_norm_one, inv_one]
  let v : J.specialSubgroup :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) d⁻¹ * u.val^3, by
      refine ⟨J.unitarySubgroup.mul_mem (scalar_mem_unitary_of_norm_one J d⁻¹ hd)
        (J.unitarySubgroup.pow_mem u.property 3), ?_⟩
      change Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin 3) d⁻¹ * u.val^3) = 1
      simp [map_mul, map_pow, Matrix.GeneralLinearGroup.det_scalar, d]⟩
  refine ⟨J.specialToProjective v, ?_⟩
  have hv : (J.specialToProjective v).val = (Matrix.ProjGenLinGroup.mk u.val)^3 := by
    simp [J.specialToProjective_apply_val, v, map_mul, map_pow]
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  change (J.unitaryConj u (J.unitaryConj u (J.unitaryConj u b))).val =
    (J.specialToProjective v).val * b.val * ((J.specialToProjective v).val)⁻¹
  simp only [J.unitaryConj_apply_val, hv, pow_succ, pow_zero, one_mul, _root_.mul_inv_rev]
  group

public theorem unitaryConj_is_inner_of_sq_eq_one (u : J.unitarySubgroup) (hu : (J.unitaryConj u)^2 = 1) :
    ∃ b : ProjectiveSpecialUnitaryMatrixGroup J, J.unitaryConj u = MulAut.conj b := by
  obtain ⟨b, hb⟩ := unitaryConj_cube_is_inner J u
  refine ⟨b, ?_⟩
  simpa [show (3 : ℕ) = 2+1 from rfl, pow_succ, hu] using hb

end BenderSuzuki.MatrixGroups.HermitianForm
