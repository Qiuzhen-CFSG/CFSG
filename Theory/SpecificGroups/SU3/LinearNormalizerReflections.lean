module
public import Theory.LinearAlgebra.RankOneEigenbasis
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.ScalarKernel
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.Coordinates

/-!
# Orthogonal coordinates for linear SU₃ reflections

A linear normalizer transports the Hermitian form to a scalar multiple of
itself, by the actual special-unitary scalar-centralizer theorem. A reflection
fixes a plane; nondegeneracy forces that scalar to be one. Its moved line is
then perpendicular to the plane and its eigenvalue has norm one. Normalizing
the two nondegenerate blocks gives orthonormal reflection coordinates without
changing the operator, field involution, or central cover.

Source: Aschbacher--Smith H.2, printed p.378; Huppert II.10.4.
-/
public section
open Matrix Module Submodule BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections
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


/-- Every linear normalizer is a similitude of the stored Hermitian form. -/
theorem similitude [CharP F 2]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∃ z : F, J.conj z ≠ z) (S : GL (Fin 3) F)
    (hN : ∀ X : J.specialSubgroup, S * X.val * S⁻¹ ∈ J.specialSubgroup) :
    ∃ c : F, J.conjTranspose S.val * J.form * S.val = c • J.form := by
  let K := adjoint J S * gram J * S
  have hAS : adjoint J S * adjoint J S⁻¹ = 1 := by
    rw [← adjoint_mul, inv_mul_cancel, adjoint_one]
  have hK (X : J.specialSubgroup) : adjoint J X.val * K * X.val = K := by
    have hh := special_equation J ⟨S * X.val * S⁻¹, hN X⟩
    simp only [adjoint_mul] at hh
    have hh := congrArg (fun a => adjoint J S * a * S) hh
    simpa only [K, mul_assoc, ← mul_assoc (adjoint J S) (adjoint J S⁻¹), hAS,
      one_mul, inv_mul_cancel, mul_one] using hh
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
  refine ⟨c,?_⟩
  have hh := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => (gram J).val * a) hc
  have hh' : (gram J).val * Matrix.scalar (Fin 3) c = K.val := by
    simpa [← Units.val_mul, mul_assoc] using hh
  simpa [gram, K, adjoint, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] using hh'.symm
end BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections

namespace BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private theorem transpose_transpose (A : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (J.conjTranspose A) = A := by
  ext i j
  exact J.conj_involutive _

private theorem transpose_form : J.conjTranspose J.form = J.form := by
  ext i j
  exact J.form_hermitian i j

/-- The original Hermitian form in the columns of an actual invertible matrix. -/
private def transportedForm (P : GL (Fin 3) F) : HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := J.conjTranspose P.val * J.form * P.val
  form_hermitian := by
    have h : J.conjTranspose (J.conjTranspose P.val * J.form * P.val) =
        J.conjTranspose P.val * J.form * P.val := by
      simp only [transpose_mul,transpose_transpose,transpose_form,mul_assoc]
    intro i j
    exact congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i j) h
  form_nondegenerate := by
    have had : (J.conjTranspose P.val).det = J.conj P.val.det := by
      change ((P.val.map J.conj).transpose).det = _
      rw [Matrix.det_transpose]
      exact (J.conj.map_det P.val).symm
    rw [Matrix.det_mul,Matrix.det_mul,had]
    exact mul_ne_zero (mul_ne_zero (by simpa using P.det_ne_zero) J.form_nondegenerate)
      P.det_ne_zero

/-- A reflection similitude is an isometry. Its moved line is perpendicular
to the fixed plane and has a norm-one eigenvalue. -/
private theorem diagonal_similitude (lam : Fˣ) (hlam : lam ≠ 1) (c : F)
    (h : J.conjTranspose (Matrix.diagonal ![1,1,(lam : F)]) * J.form *
      Matrix.diagonal ![1,1,(lam : F)] = c • J.form) :
    c = 1 ∧ J.form 0 2 = 0 ∧ J.form 1 2 = 0 ∧
      J.form 2 0 = 0 ∧ J.form 2 1 = 0 ∧ J.conj (lam : F) * (lam : F) = 1 := by
  have he (i j : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i j) h
  have h00 := he 0 0
  have h01 := he 0 1
  have h10 := he 1 0
  have h11 := he 1 1
  have h02 := he 0 2
  have h12 := he 1 2
  have h20 := he 2 0
  have h21 := he 2 1
  have h22 := he 2 2
  simp [conjTranspose,Matrix.mul_apply,Fin.sum_univ_three] at h00 h01 h10 h11 h02 h12 h20 h21 h22
  have hc : c = 1 := by
    by_contra hn
    have hz (x : F) (hx : x = c*x) : x = 0 := by
      exact (mul_eq_zero.mp (show (c-1)*x=0 by linear_combination -hx)).resolve_left
        (sub_ne_zero.mpr hn)
    have hd := J.form_nondegenerate
    apply hd
    simp [Matrix.det_fin_three,hz _ h00,hz _ h01,hz _ h10,hz _ h11]
  subst c
  have hn : (lam : F) ≠ 1 := fun he => hlam (Units.ext he)
  have hcn : J.conj (lam : F) ≠ 1 := fun he => hn (J.conj.injective (he.trans (map_one _).symm))
  have hz (a x : F) (ha : a ≠ 1) (hx : a*x=x) : x = 0 :=
    (mul_eq_zero.mp (show (a-1)*x=0 by linear_combination hx)).resolve_left (sub_ne_zero.mpr ha)
  have hz02 := hz (lam : F) (J.form 0 2) hn (by simpa [mul_comm] using h02)
  have hz12 := hz (lam : F) (J.form 1 2) hn (by simpa [mul_comm] using h12)
  have hz20 := h20.resolve_left hcn
  have hz21 := h21.resolve_left hcn
  have hn22 : J.form 2 2 ≠ 0 := by
    intro hz22
    apply J.form_nondegenerate
    simp [Matrix.det_fin_three,hz02,hz12,hz20,hz21,hz22]
  refine ⟨rfl,hz02,hz12,hz20,hz21,?_⟩
  apply mul_right_cancel₀ hn22
  linear_combination h22
end BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections

namespace BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections
variable {K : Type*} [Field K] [Finite K]
private theorem normalize_fixed_plane
    (H : HermitianForm 3 K) (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // H.conj x = x} = q) (lam : Kˣ)
    (h02 : H.form 0 2 = 0) (h12 : H.form 1 2 = 0)
    (h20 : H.form 2 0 = 0) (h21 : H.form 2 1 = 0) :
    ∃ Q : GL (Fin 3) K,
      H.conjTranspose Q.val * H.form * Q.val = 1 ∧
      Q.val * Matrix.diagonal ![1,1,(lam : K)] =
        Matrix.diagonal ![1,1,(lam : K)] * Q.val := by
  classical
  let B : Matrix (Fin 2) (Fin 2) K :=
    !![H.form 0 0, H.form 0 1; H.form 1 0, H.form 1 1]
  have hd : H.form.det = B.det * H.form 2 2 := by
    simp [B, Matrix.det_fin_three, Matrix.det_fin_two, h02, h12, h20, h21]
    ring
  have hn := H.form_nondegenerate
  rw [hd] at hn
  obtain ⟨hB, ha⟩ := mul_ne_zero_iff.mp hn
  let H₂ : HermitianForm 2 K :=
    { conj := H.conj
      conj_involutive := H.conj_involutive
      form := B
      form_hermitian := by
        intro i j
        fin_cases i <;> fin_cases j <;>
          exact H.form_hermitian _ _
      form_nondegenerate := hB }
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 2 H₂ q hcard hfixed
  obtain ⟨b, hb, hnorm⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective H q hcard hfixed
    (H.form 2 2)⁻¹ (by rw [map_inv₀, H.form_hermitian]) (inv_ne_zero ha)
  have hlast : H.conj b * H.form 2 2 * b = 1 := by
    calc
      _ = (b * H.conj b) * H.form 2 2 := by ring
      _ = 1 := by rw [hnorm, inv_mul_cancel₀ ha]
  let M : Matrix (Fin 3) (Fin 3) K :=
    !![P.val 0 0, P.val 0 1, 0; P.val 1 0, P.val 1 1, 0; 0, 0, b]
  have hM : M.det ≠ 0 := by
    have he : M.det = P.val.det * b := by
      simp [M, Matrix.det_fin_three, Matrix.det_fin_two]
      ring
    rw [he]
    exact mul_ne_zero P.det_ne_zero hb
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hM, ?_, ?_⟩
  · change H.conjTranspose M * H.form * M = 1
    have he (i j : Fin 2) := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A i j) hP
    have h00 := he 0 0
    have h01 := he 0 1
    have h10 := he 1 0
    have h11 := he 1 1
    simp [conjTranspose, H₂, B, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        h02, h12, h20, h21, h00, h01, h10, h11, hlast]
  · change M * _ = _ * M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_three,mul_comm]
end BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections

open UnitaryThree.OddTorusNormalizer
namespace BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A rank-one linear normalizer admits orthonormal reflection coordinates
for the original stored conjugation. -/
theorem exists_reflection_frame (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∃ z : F, J.conj z ≠ z) (q : ℕ)
    (hcard : Nat.card F = q^2) (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (S : GL (Fin 3) F)
    (hN : ∀ X : J.specialSubgroup, S * X.val * S⁻¹ ∈ J.specialSubgroup)
    (hr : finrank F (LinearMap.range (Matrix.toLin' S.val - LinearMap.id)) = 1)
    (hd : GeneralLinearGroup.det S ≠ 1) :
    ∃ P : OrthogonalFrame J,
      P.val⁻¹ * S * P.val = diagonalHom ![1,1,GeneralLinearGroup.det S] ∧
      GeneralLinearGroup.det S ∈ HermitianForm.EvenInner.normOne J := by
  classical
  let e := (GeneralLinearGroup.toLin S).toLinearEquiv
  have he : e.toLinearMap = Matrix.toLin' S.val := rfl
  have hde : e.det = GeneralLinearGroup.det S := by
    apply Units.ext
    rw [LinearEquiv.coe_det,he,LinearMap.det_toLin']
    rfl
  obtain ⟨b,hb⟩ := e.exists_rank_one_eigenbasis (he ▸ hr) (hde ▸ hd)
  let std := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F :=
    ⟨std.toMatrix b,b.toMatrix std,std.toMatrix_mul_toMatrix_flip b,b.toMatrix_mul_toMatrix_flip std⟩
  let d := diagonalHom ![1,1,GeneralLinearGroup.det S]
  have hP : P * d * P⁻¹ = S := by
    apply Units.ext
    change std.toMatrix b * d.val * b.toMatrix std = S.val
    have hdval : d.val = Matrix.diagonal ![1,1,(e.det : F)] := by
      rw [hde]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [d,diagonalHom]
    rw [hdval,←hb,basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,he]
    simp [std,LinearMap.toMatrix_eq_toMatrix']
  have hSP : S.val * P.val = P.val * d.val :=
    congrArg Units.val (by rw [←hP]; group : S * P = P * d)
  obtain ⟨c,hc⟩ := similitude J hJ hconj S hN
  let H := transportedForm J P
  have hH : H.conjTranspose d.val * H.form * d.val = c • H.form := by
    change J.conjTranspose d.val * (J.conjTranspose P.val * J.form * P.val) * d.val =
      c • (J.conjTranspose P.val * J.form * P.val)
    calc
      _ = J.conjTranspose (P.val*d.val) * J.form * (P.val*d.val) := by
        rw [transpose_mul]
        simp only [mul_assoc]
      _ = J.conjTranspose (S.val*P.val) * J.form * (S.val*P.val) := by rw [hSP]
      _ = J.conjTranspose P.val * (J.conjTranspose S.val * J.form * S.val) * P.val := by
        rw [transpose_mul]
        simp only [mul_assoc]
      _ = _ := by rw [hc,Matrix.mul_smul,Matrix.smul_mul]
  have hdval : d.val = Matrix.diagonal ![1,1,(GeneralLinearGroup.det S : F)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d,diagonalHom]
  rw [hdval] at hH
  obtain ⟨_,h02,h12,h20,h21,hnorm⟩ := diagonal_similitude H _ hd c hH
  obtain ⟨Q,hQ,hcomm⟩ := normalize_fixed_plane H q hcard hfixed
    (GeneralLinearGroup.det S) h02 h12 h20 h21
  have hcomm' : Q*d=d*Q := Units.ext (by simpa only [Units.val_mul,hdval] using hcomm)
  have hPQ : J.conjTranspose (P*Q).val * J.form * (P*Q).val = 1 := by
    change J.conjTranspose (P.val*Q.val) * J.form * (P.val*Q.val) = 1
    rw [transpose_mul]
    change J.conjTranspose Q.val * (J.conjTranspose P.val * J.form * P.val) * Q.val = 1 at hQ
    simpa only [mul_assoc] using hQ
  refine ⟨⟨P*Q,hPQ⟩,?_,?_⟩
  · change (P*Q)⁻¹ * S * (P*Q) = d
    rw [←hP]
    simp only [_root_.mul_inv_rev,mul_assoc,inv_mul_cancel_left]
    rw [←hcomm',inv_mul_cancel_left]
  · exact eq_inv_of_mul_eq_one_left hnorm
end BenderSuzuki.MatrixGroups.HermitianForm.LinearNormalizerReflections

