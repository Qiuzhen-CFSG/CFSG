module

public import Theory.SpecificGroups.SU3.FullCentralizer

/-!
# Geometry of three-dimensional unitary involutions

An involution preserving the identity Hermitian form is self-adjoint. Thus a
basis conjugating it to `diag(-1,-1,1)` has a block diagonal Gram matrix,
with nondegenerate two-dimensional and one-dimensional blocks. Normalizing
that Gram matrix by a change of basis commuting with the diagonal involution
produces a unitary conjugator.

The eigenbasis and the block normalization are separate inputs to the final
assembly lemma in this module. Neither is asserted to exist here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.3.21(a), printed p. 55 (PDF p. 66).
-/

public section

open Matrix
open scoped Matrix
open BenderSuzuki.MatrixGroups
namespace Matrix.SU3
variable {F : Type*} [Field F]

/-- The underlying matrix of an involution squares to the identity. -/
theorem involution_matrix_sq (J : HermitianForm 3 F)
    (A : J.specialSubgroup) (hA : orderOf A = 2) : A.val.val * A.val.val = 1 := by
  have hs : A ^ 2 = 1 := hA ▸ pow_orderOf_eq_one A
  have hv := congrArg (fun B : J.specialSubgroup => B.val.val) hs
  simpa only [pow_two, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
    Units.val_one] using hv

/-- An element of order two has a nonidentity underlying matrix. -/
theorem involution_matrix_ne_one (J : HermitianForm 3 F)
    (A : J.specialSubgroup) (hA : orderOf A = 2) : A.val.val ≠ 1 := by
  intro h
  have he : A = 1 := Subtype.ext (Units.ext h)
  simp [he] at hA

/-- The underlying matrix of a special unitary element has determinant one. -/
theorem special_matrix_det (J : HermitianForm 3 F)
    (A : J.specialSubgroup) : A.val.val.det = 1 := by
  have h := ((J.mem_specialSubgroup_iff A.val).mp A.property).2
  exact congrArg Units.val h

/-- An involution preserving the identity form is self-adjoint. -/
theorem involution_conjTranspose_eq (J : HermitianForm 3 F) (hJ : J.form = 1)
    (A : J.specialSubgroup) (hA : orderOf A = 2) :
    J.conjTranspose A.val.val = A.val.val := by
  have hu := ((J.mem_specialSubgroup_iff A.val).mp A.property).1
  rw [hJ, mul_one] at hu
  exact (Units.mul_left_inj A.val).mp
    (hu.trans (involution_matrix_sq J A hA).symm)

private theorem adjoint_mul (J : HermitianForm 3 F)
    (X Y : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (X * Y) = J.conjTranspose Y * J.conjTranspose X := by
  change ((J.conj : F →+* F).mapMatrix (X * Y)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

/-- The Gram matrix of an involution eigenbasis commutes with its diagonal representative. -/
theorem eigenbasis_gram_commutes (J : HermitianForm 3 F) (hJ : J.form = 1)
    (A : J.specialSubgroup) (hA : orderOf A = 2) (P : GL (Fin 3) F)
    (hP : P * (standardInvolution J hJ).val * P⁻¹ = A.val) :
    (J.conjTranspose P.val * P.val) * (standardInvolution J hJ).val.val =
      (standardInvolution J hJ).val.val * (J.conjTranspose P.val * P.val) := by
  have hi : A.val * P = P * (standardInvolution J hJ).val := by
    rw [← hP]
    group
  have him : A.val.val * P.val = P.val * (standardInvolution J hJ).val.val :=
    congrArg Units.val hi
  have hs : J.conjTranspose (standardInvolution J hJ).val.val =
      (standardInvolution J hJ).val.val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardInvolution_val, HermitianForm.conjTranspose]
  have ha := congrArg J.conjTranspose him
  rw [adjoint_mul, adjoint_mul, involution_conjTranspose_eq J hJ A hA, hs] at ha
  calc
    _ = J.conjTranspose P.val * (P.val * (standardInvolution J hJ).val.val) :=
      mul_assoc _ _ _
    _ = J.conjTranspose P.val * (A.val.val * P.val) := by rw [him]
    _ = (J.conjTranspose P.val * A.val.val) * P.val := (mul_assoc _ _ _).symm
    _ = _ := by rw [ha, mul_assoc]

/-- The positive and negative eigenspaces are orthogonal. -/
theorem eigenbasis_gram_offBlock (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (A : J.specialSubgroup) (hA : orderOf A = 2)
    (P : GL (Fin 3) F)
    (hP : P * (standardInvolution J hJ).val * P⁻¹ = A.val) :
    let G := J.conjTranspose P.val * P.val
    G 0 2 = 0 ∧ G 1 2 = 0 ∧ G 2 0 = 0 ∧ G 2 1 = 0 := by
  let G := J.conjTranspose P.val * P.val
  have hm := eigenbasis_gram_commutes J hJ A hA P hP
  change G * (standardInvolution J hJ).val.val =
    (standardInvolution J hJ).val.val * G at hm
  rw [standardInvolution_val] at hm
  have he (i j : Fin 3) := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hm
  have h02 := he 0 2
  have h12 := he 1 2
  have h20 := he 2 0
  have h21 := he 2 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h02 h12 h20 h21
  have hz (x : F) (hx : 2 * x = 0) : x = 0 := (mul_eq_zero.mp hx).resolve_left h2
  exact ⟨hz _ (by linear_combination h02), hz _ (by linear_combination h12),
    hz _ (by linear_combination -h20), hz _ (by linear_combination -h21)⟩

/-- A Gram matrix is Hermitian for the original stored conjugation. -/
theorem eigenbasis_gram_hermitian (J : HermitianForm 3 F) (P : GL (Fin 3) F)
    (i j : Fin 3) :
    J.conj ((J.conjTranspose P.val * P.val) j i) =
      (J.conjTranspose P.val * P.val) i j := by
  have hc (a : F) : J.conj (J.conj a) = a := J.conj_involutive a
  simp [Matrix.mul_apply, HermitianForm.conjTranspose, map_sum, map_mul, hc, mul_comm]

/-- An invertible change of basis has nondegenerate Gram matrix. -/
theorem eigenbasis_gram_nondegenerate (J : HermitianForm 3 F) (P : GL (Fin 3) F) :
    (J.conjTranspose P.val * P.val).det ≠ 0 := by
  have had : (J.conjTranspose P.val).det = J.conj P.val.det := by
    change ((P.val.map J.conj).transpose).det = _
    rw [Matrix.det_transpose]
    exact (J.conj.map_det P.val).symm
  rw [Matrix.det_mul, had]
  exact mul_ne_zero (by simpa using P.det_ne_zero) P.det_ne_zero

theorem eigenbasis_gram_blocks_nondegenerate
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (A : J.specialSubgroup) (hA : orderOf A = 2)
    (P : GL (Fin 3) F)
    (hP : P * (standardInvolution J hJ).val * P⁻¹ = A.val) :
    let G := J.conjTranspose P.val * P.val
    (!![G 0 0, G 0 1; G 1 0, G 1 1]).det ≠ 0 ∧ G 2 2 ≠ 0 := by
  let G := J.conjTranspose P.val * P.val
  obtain ⟨h02, h12, h20, h21⟩ := eigenbasis_gram_offBlock J hJ h2 A hA P hP
  have hd : G.det = (!![G 0 0, G 0 1; G 1 0, G 1 1]).det * G 2 2 := by
    change G 0 2 = 0 at h02
    change G 1 2 = 0 at h12
    change G 2 0 = 0 at h20
    change G 2 1 = 0 at h21
    simp [Matrix.det_fin_three, Matrix.det_fin_two, h02, h12, h20, h21]
    ring
  have hn := eigenbasis_gram_nondegenerate J P
  change G.det ≠ 0 at hn
  rw [hd] at hn
  exact mul_ne_zero_iff.mp hn


/-- The identity form transported to the supplied basis. -/
@[expose] def eigenbasisGramForm (J : HermitianForm 3 F) (P : GL (Fin 3) F) :
    HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := J.conjTranspose P.val * P.val
  form_hermitian := eigenbasis_gram_hermitian J P
  form_nondegenerate := eigenbasis_gram_nondegenerate J P

theorem unitary_conjugator_of_gram_normalizer
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (A : J.specialSubgroup) (P : GL (Fin 3) F)
    (hP : P * (standardInvolution J hJ).val * P⁻¹ = A.val)
    (Q : GL (Fin 3) F)
    (hQ : (eigenbasisGramForm J P).conjTranspose Q.val *
      (eigenbasisGramForm J P).form * Q.val = 1)
    (hcomm : Q * (standardInvolution J hJ).val =
      (standardInvolution J hJ).val * Q) :
    ∃ C : J.unitarySubgroup,
      C.val * (standardInvolution J hJ).val * C.val⁻¹ = A.val := by
  have hu : P * Q ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff, hJ, mul_one]
    change J.conjTranspose (P.val * Q.val) * (P.val * Q.val) = 1
    rw [adjoint_mul]
    change J.conjTranspose Q.val * (J.conjTranspose P.val * P.val) * Q.val = 1 at hQ
    simpa only [mul_assoc] using hQ
  refine ⟨⟨P * Q, hu⟩, ?_⟩
  change (P * Q) * (standardInvolution J hJ).val * (P * Q)⁻¹ = A.val
  calc
    _ = P * (Q * (standardInvolution J hJ).val) * Q⁻¹ * P⁻¹ := by
      simp only [_root_.mul_inv_rev, mul_assoc]
    _ = P * ((standardInvolution J hJ).val * Q) * Q⁻¹ * P⁻¹ := by rw [hcomm]
    _ = A.val := by simpa only [mul_assoc, mul_inv_cancel_left] using hP

end Matrix.SU3
end
