module

public import Theory.SpecificGroups.ProjectiveLinearInvolutions
public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Involutions in projective unitary groups in dimension three

Normalize the given Hermitian form over the field of order `p²`, keeping its
stored Frobenius involution. Conjugating `diag(-1,-1,1)` by the orthonormal
basis matrix produces a determinant-one isometry of the original form.
Its image in PGL is nontrivial because the diagonal matrix is not scalar.
Thus the actual PSU₃ model has even order when the fixed-field prime is odd.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(7), printed p.214; the basis normalization uses Huppert II.10.4.
The private conjugation calculation is the dimension-three version of
`BenderSuzuki.MatrixGroups.HermitianConjugation.conjugate_preserves_iff`.
-/

public section

open Matrix
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace Matrix.SU3
variable {F : Type*} [Field F]

private theorem adjoint_mul (J : HermitianForm 3 F)
    (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm 3 F) : J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

private def adjointUnit (J : HermitianForm 3 F) (C : GL (Fin 3) F) : GL (Fin 3) F where
  val := J.conjTranspose C.val
  inv := J.conjTranspose (C⁻¹).val
  val_inv := by rw [← adjoint_mul]; simpa using adjoint_one J
  inv_val := by rw [← adjoint_mul]; simpa using adjoint_one J

private theorem conjugate_preserves_iff (J : HermitianForm 3 F) (C B : GL (Fin 3) F) :
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

private theorem exists_involution_of_basis (J : HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    (P : GL (Fin 3) F) (hP : J.conjTranspose P.val * J.form * P.val = 1) :
    ∃ x : ProjectiveSpecialUnitaryMatrixGroup J, orderOf x = 2 := by
  let D := Matrix.SpecialLinearGroup.toGL (SL3.standardInvolution F)
  let C := P * D * P⁻¹
  have hDsq : D ^ 2 = 1 := by
    rw [← map_pow, SL3.standardInvolution_sq, map_one]
  have hCmem : C ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · apply (conjugate_preserves_iff J P D).mpr
      rw [hP, mul_one]
      change J.conjTranspose (SL3.standardInvolution F).val *
        (SL3.standardInvolution F).val = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [HermitianForm.conjTranspose, SL3.standardInvolution,
          Matrix.mul_apply, Fin.sum_univ_three]
    · simp [C, D]
  let x : ProjectiveSpecialUnitaryMatrixGroup J :=
    ⟨Matrix.ProjGenLinGroup.mk C, ⟨C, hCmem, rfl⟩⟩
  refine ⟨x, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    change (Matrix.ProjGenLinGroup.mk C) ^ 2 = 1
    have hCsq : C ^ 2 = 1 := by
      change (MulAut.conj P D) ^ 2 = 1
      rw [← map_pow, hDsq, map_one]
    rw [← map_pow, hCsq, map_one]
  · intro hx
    have hx' := congrArg Subtype.val hx
    change Matrix.ProjGenLinGroup.mk C = 1 at hx'
    have hc : Matrix.ProjGenLinGroup.mk C =
        MulAut.conj (Matrix.ProjGenLinGroup.mk P) (Matrix.ProjGenLinGroup.mk D) := by
      simp [C, MulAut.conj_apply]
    rw [hc] at hx'
    have hd : Matrix.ProjGenLinGroup.mk D = 1 :=
      (map_eq_one_iff (MulAut.conj (Matrix.ProjGenLinGroup.mk P))
        (MulAut.conj (Matrix.ProjGenLinGroup.mk P)).injective).mp hx'
    have hdcenter := Matrix.ProjGenLinGroup.mk_eq_one.mp hd
    exact SL3.standardInvolution_not_mem_center F h2
      ((Matrix.SpecialLinearGroup.toGL_mem_center_iff _).mp hdcenter)

/-- The noncentral diagonal involution survives in the actual projective image. -/
theorem exists_projective_orderOf_eq_two_of_prime_frobenius [Finite F] (J : HermitianForm 3 F) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    ∃ x : ProjectiveSpecialUnitaryMatrixGroup J, orderOf x = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨P, hP⟩ := J.exists_orthonormal_basis_of_prime_frobenius hc hcard
  exact exists_involution_of_basis J
    (Field.two_ne_zero_of_odd_card F (by rw [hcard]; exact hodd.pow)) P hP

/-- Even order follows from an actual element of order two, for every allowed form. -/
theorem two_dvd_projective_card_of_prime_frobenius [Finite F]
    (J : HermitianForm 3 F) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    2 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨x, hx⟩ := exists_projective_orderOf_eq_two_of_prime_frobenius J p hp hodd hcard hc
  simpa only [hx] using orderOf_dvd_natCard x

end Matrix.SU3
