module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
import BenderSuzuki.External.Huppert.II.theorem_10_4

/-!
# Projective descent from a similarity of fixed-field Gram matrices

A linear descent basis has a nondegenerate symmetric Gram matrix over the
fixed field. A fixed-field congruence taking it to a scalar multiple of the
original form changes the descent basis to a unitary similitude. Surjectivity
of the quadratic norm supplies a scalar correction making this basis unitary.
That correction changes its coboundary only by a projective scalar.

This proves the assembly from a supplied fixed-field similarity. Existence of
that similarity remains explicit; symmetric ternary forms over an odd finite
field need not all be congruent to one fixed matrix without scaling.

Adapted from `ProjectiveOuterInvolutions.Descent.GramNormalization`.
Source: GLS3, §§2.7 and 4.3, and Aschbacher–Smith F.6.18(10)–(11), pp.309–310.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
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


private theorem descent_adjoint_smul (c : E) (A : Matrix (Fin 3) (Fin 3) E) :
    J.conjTranspose (c • A) = J.conj c • J.conjTranspose A := by
  ext i j
  exact map_mul J.conj c (A j i)

/-- A fixed-field similarity, followed by scalar norm correction, makes a descent
basis unitary. Scalar correction preserves precisely the projective coboundary. -/
public theorem projective_coboundary_of_gram_similarity [Finite E]
    (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hJ : J.form.map J.conj = J.form)
    (u : J.unitarySubgroup) (P : GL (Fin 3) E)
    (hP : u.val * GeneralLinearGroup.map J.conj.toRingHom P = P)
    (hnormalize : ∀ S : Matrix (Fin 3) (Fin 3) E,
      S.transpose = S → S.map J.conj = S → S.det ≠ 0 →
      ∃ (a : E) (C : GL (Fin 3) E), a ≠ 0 ∧ J.conj a = a ∧
        C.val.map J.conj = C.val ∧ C.val.transpose * S * C.val = a • J.form) :
    ∃ v : J.unitarySubgroup,
      ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
        (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹) := by
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

  obtain ⟨a, C, ha0, hafix, hCfix, hC⟩ := hnormalize S hSsymm hSfix hSdet
  have hCadj : J.conjTranspose C.val = C.val.transpose := by
    change (C.val.map J.conj).transpose = C.val.transpose
    rw [hCfix]
  let D := P * C
  have hDgram : J.conjTranspose D.val * J.form * D.val = a • J.form := by
    change J.conjTranspose (P.val * C.val) * J.form * (P.val * C.val) = _
    rw [descent_adjoint_mul, hCadj]
    simpa only [S, mul_assoc] using hC
  have hD : u.val = D * (GeneralLinearGroup.map J.conj.toRingHom D)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).mpr
    have hCeq : GeneralLinearGroup.map J.conj.toRingHom C = C := Units.ext hCfix
    dsimp only [D]
    rw [map_mul, hCeq, ← mul_assoc, hP]
  obtain ⟨k, hk0, hk⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective
    J q hcard hfixed a⁻¹ (by rw [map_inv₀, hafix]) (inv_ne_zero ha0)
  let ku : Eˣ := Units.mk0 k hk0
  let V := D * GeneralLinearGroup.scalar (Fin 3) ku
  have hVval : V.val = k • D.val := by
    ext i j
    simp [V, ku, GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  have hV : V ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff, hVval, descent_adjoint_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hDgram, smul_smul]
    rw [hk, inv_mul_cancel₀ ha0, one_smul]
  have hVproj : ProjGenLinGroup.mk V = ProjGenLinGroup.mk D := by
    simp [V, map_mul, ProjGenLinGroup.mk_scalar]
  refine ⟨⟨V, hV⟩, ?_⟩
  change ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
    (V * (GeneralLinearGroup.map J.conj.toRingHom V)⁻¹)
  rw [map_mul, map_inv, ← ProjGenLinGroup.map_mk, hVproj,
    ProjGenLinGroup.map_mk, ← map_inv, ← map_mul, ← hD]

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
