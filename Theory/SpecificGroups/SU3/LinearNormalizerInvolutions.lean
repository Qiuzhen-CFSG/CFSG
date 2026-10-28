module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.ScalarKernel

/-!
# Linear involutions in the normalizer of the natural special unitary group

A linear normalizer transports the Hermitian form to another SU₃-invariant
form. Their quotient commutes with the actual special-unitary matrices, so
the scalar-centralizer theorem makes the transported form a scalar multiple
of the original. For a square-one matrix that scalar has square one, hence
is one in characteristic two. The same argument applies to the determinant.

This retains the full special unitary group, including its cubic center.
It supplies the linear part of the outer-involution assertion in
Aschbacher–Smith, K.3.3, printed p.456 (1 March 2004 manuscript).
-/

open BenderSuzuki.MatrixGroups Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerInvolutions
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private theorem transpose_mul (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  ext i j
  simp only [HermitianForm.conjTranspose, Matrix.mul_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

private theorem transpose_one : J.conjTranspose 1 = 1 := by
  ext i j
  by_cases h : i = j
  · subst j; simp [HermitianForm.conjTranspose]
  · simp [HermitianForm.conjTranspose, h, Ne.symm h]

private def adjoint (A : GL (Fin 3) F) : GL (Fin 3) F where
  val := J.conjTranspose A.val
  inv := J.conjTranspose A.inv
  val_inv := by rw [← transpose_mul]; simpa using transpose_one J
  inv_val := by rw [← transpose_mul]; simpa using transpose_one J

private theorem adjoint_mul (A B : GL (Fin 3) F) :
    adjoint J (A * B) = adjoint J B * adjoint J A :=
  Units.ext (transpose_mul J _ _)

private theorem adjoint_one : adjoint J 1 = 1 := Units.ext (transpose_one J)

private def gram : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero J.form J.form_nondegenerate

private theorem special_equation (X : J.specialSubgroup) :
    adjoint J X.val * gram J * X.val = gram J :=
  Units.ext ((J.mem_specialSubgroup_iff X.val).mp X.property).1

variable [CharP F 2]

/-- A linear involution normalizing the literal SU₃ group is special unitary. -/
public theorem mem_special_of_square_one
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∃ z : F, J.conj z ≠ z) (S : GL (Fin 3) F)
    (hS : S * S = 1)
    (hN : ∀ X : J.specialSubgroup, S * X.val * S ∈ J.specialSubgroup) :
    S ∈ J.specialSubgroup := by
  let K := adjoint J S * gram J * S
  have hAS : adjoint J S * adjoint J S = 1 := by
    rw [← adjoint_mul, hS, adjoint_one]
  have hK (X : J.specialSubgroup) : adjoint J X.val * K * X.val = K := by
    have hh := special_equation J ⟨S * X.val * S, hN X⟩
    simp only [adjoint_mul] at hh
    have hh := congrArg (fun a => adjoint J S * a * S) hh
    simpa only [K, mul_assoc, ← mul_assoc (adjoint J S) (adjoint J S), hAS,
      one_mul, ← mul_assoc _ S S, hS, mul_one] using hh
  have hcomm (X : J.specialSubgroup) : Commute ((gram J)⁻¹ * K) X.val := by
    have hX := special_equation J X
    have hKX := hK X
    have he : adjoint J X.val = gram J * X.val⁻¹ * (gram J)⁻¹ := by
      calc
        _ = (adjoint J X.val * gram J * X.val) * X.val⁻¹ * (gram J)⁻¹ := by simp [mul_assoc]
        _ = _ := by rw [hX]
    rw [he] at hKX
    have hh := congrArg (fun a => X.val * (gram J)⁻¹ * a) hKX
    have hh' : (gram J)⁻¹ * K * X.val = X.val * ((gram J)⁻¹ * K) := by
      simpa [mul_assoc] using hh
    exact hh'
  have hcentral := J.projective_centralizer_scalar hJ hconj ((gram J)⁻¹ * K) (by
    intro b
    obtain ⟨X, rfl⟩ := J.specialToProjective_surjective b
    simpa only [specialToProjective_apply_val] using (hcomm X).map ProjGenLinGroup.mk)
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcentral
  have hform : J.conjTranspose S.val * J.form * S.val = c • J.form := by
    have hh := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => (gram J).val * a) hc
    have hh' : (gram J).val * Matrix.scalar (Fin 3) c = K.val := by
      simpa [← Units.val_mul, mul_assoc] using hh
    simpa [gram, K, adjoint, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] using hh'.symm
  have hsval : S.val * S.val = 1 := congrArg Units.val hS
  have hadjval : J.conjTranspose S.val * J.conjTranspose S.val = 1 :=
    congrArg Units.val hAS
  have hsquare : J.form = (c * c) • J.form := by
    calc
      _ = (J.conjTranspose S.val * J.conjTranspose S.val) * J.form *
          (S.val * S.val) := by rw [hadjval, hsval, one_mul, mul_one]
      _ = J.conjTranspose S.val * (J.conjTranspose S.val * J.form * S.val) * S.val := by
        simp only [mul_assoc]
      _ = (c * c) • J.form := by
        rw [hform, Matrix.mul_smul, Matrix.smul_mul, hform, smul_smul]
  have hc2 : c * c = 1 := by
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 2) hsquare
    simpa [hJ] using hh.symm
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa [pow_two] using hc2)
  apply (J.mem_specialSubgroup_iff S).mpr
  refine ⟨by simpa [hc1] using hform, ?_⟩
  apply Units.ext
  have hd : S.val.det * S.val.det = 1 := by rw [← Matrix.det_mul, hsval, Matrix.det_one]
  exact CharTwo.sq_injective (by simpa [pow_two] using hd)

end BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerInvolutions
