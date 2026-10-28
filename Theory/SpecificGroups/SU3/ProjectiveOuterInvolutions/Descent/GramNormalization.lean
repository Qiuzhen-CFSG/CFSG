module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation

/-!
# Making a semilinear descent basis unitary

Suppose `u * conj(P) = P`, where `u` is unitary and `P` is invertible.
The Hermitian Gram matrix of the columns of `P` is fixed by conjugation:
the columns of `conj(P)` have the same pairings because `u` is unitary.
Being both fixed and Hermitian, the Gram matrix is symmetric.

A congruence over the fixed field taking this nondegenerate symmetric form
to the original Gram matrix changes `P` to a unitary matrix without changing
the semilinear descent equation. This lemma consumes, but does not assert,
existence of the fixed-field congruence.

This is the linear-algebra assembly in the twisted A₂ case of GLS,
Volume 3, Proposition 4.9.2(b2,g), used in Volume 4, Chapter 4,
Lemma 3.4(a,c).
-/

open BenderSuzuki.MatrixGroups Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private theorem descent_adjoint_mul (A B : Matrix (Fin 3) (Fin 3) E) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : E →+* E).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem descent_adjoint_adjoint (A : Matrix (Fin 3) (Fin 3) E) :
    J.conjTranspose (J.conjTranspose A) = A := by
  ext i j
  exact J.conj_involutive _

private theorem descent_adjoint_form : J.conjTranspose J.form = J.form := by
  ext i j
  exact J.form_hermitian i j

/-- A linear descent basis becomes unitary after normalizing its symmetric
Gram matrix by a matrix fixed by conjugation. -/
public theorem unitary_coboundary_of_gram_normalization
    (hJ : J.form.map J.conj = J.form)
    (u : J.unitarySubgroup) (P : GL (Fin 3) E)
    (hP : u.val * GeneralLinearGroup.map J.conj.toRingHom P = P)
    (hnormalize : ∀ S : Matrix (Fin 3) (Fin 3) E,
      S.transpose = S → S.map J.conj = S → S.det ≠ 0 →
      ∃ C : GL (Fin 3) E, C.val.map J.conj = C.val ∧
        C.val.transpose * S * C.val = J.form) :
    ∃ v : J.unitarySubgroup,
      u.val = v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹ := by
  let S := J.conjTranspose P.val * J.form * P.val
  have hu := (J.mem_unitarySubgroup_iff u.val).mp u.property
  have hPm : u.val.val * P.val.map J.conj = P.val := congrArg Units.val hP
  have hmapAdj : (J.conjTranspose P.val).map J.conj =
      J.conjTranspose (P.val.map J.conj) := by rfl
  have hSfix : S.map J.conj = S := by
    calc
      S.map J.conj = J.conjTranspose (P.val.map J.conj) * J.form *
          (P.val.map J.conj) := by
        simp only [S, Matrix.map_mul, hmapAdj, hJ]
      _ = J.conjTranspose (P.val.map J.conj) *
          (J.conjTranspose u.val.val * J.form * u.val.val) * (P.val.map J.conj) := by
        rw [hu]
      _ = S := by
        dsimp only [S]
        conv_rhs => rw [← hPm]
        rw [descent_adjoint_mul]
        simp only [mul_assoc]
  have hSherm : J.conjTranspose S = S := by
    simp only [S, descent_adjoint_mul, descent_adjoint_adjoint, descent_adjoint_form,
      mul_assoc]
  have hSsymm : S.transpose = S := by
    change (S.map J.conj).transpose = S at hSherm
    rwa [hSfix] at hSherm
  have hSdet : S.det ≠ 0 := by
    have had : (J.conjTranspose P.val).det = J.conj P.val.det := by
      change ((P.val.map J.conj).transpose).det = _
      rw [Matrix.det_transpose]
      exact (J.conj.map_det P.val).symm
    dsimp only [S]
    rw [Matrix.det_mul, Matrix.det_mul, had]
    exact mul_ne_zero (mul_ne_zero (by simpa using P.det_ne_zero) J.form_nondegenerate)
      P.det_ne_zero
  obtain ⟨C, hCfix, hC⟩ := hnormalize S hSsymm hSfix hSdet
  have hCadj : J.conjTranspose C.val = C.val.transpose := by
    change (C.val.map J.conj).transpose = C.val.transpose
    rw [hCfix]
  have hPC : P * C ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff]
    change J.conjTranspose (P.val * C.val) * J.form * (P.val * C.val) = J.form
    rw [descent_adjoint_mul, hCadj]
    simpa only [S, mul_assoc] using hC
  refine ⟨⟨P * C, hPC⟩, (eq_mul_inv_iff_mul_eq).mpr ?_⟩
  change u.val * GeneralLinearGroup.map J.conj.toRingHom (P * C) = P * C
  have hCeq : GeneralLinearGroup.map J.conj.toRingHom C = C := Units.ext hCfix
  rw [map_mul, hCeq, ← mul_assoc, hP]

end BenderSuzuki.MatrixGroups.HermitianForm
