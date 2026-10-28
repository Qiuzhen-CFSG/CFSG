module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.StandardInvolution

/-!
# Normalizing a supplied two-plus-two unitary eigenbasis

A special unitary matrix linearly conjugate to `diag(-1,-1,1,1)` is an
involution and hence self-adjoint for the identity Hermitian form. The Gram
matrix of the supplied eigenbasis therefore has two orthogonal, nondegenerate
two-dimensional blocks. Normalize each block by Huppert II.10.4, retaining the
stored conjugation. Their block diagonal change of basis commutes with the
standard involution, so its product with the supplied basis is a unitary
conjugator.

This proves the normalization input to involution-centralizer transport; the
existence of the initial linear eigenbasis is a separate input.

Sources: Huppert II.10.4 for Hermitian normalization; Aschbacher–Smith,
*The Classification of Quasithin Groups*, condition E and Theorem 0.1.2(4),
printed pp. 3–4 and 481–482 of `refs/quasithin.pdf`, for the application.
The unitary and projective conventions are those of GLS3, chapter 2.
The Gram-matrix argument follows `SU3/InvolutionEigenbasisGeometry.lean`.
-/

open Matrix BenderSuzuki.MatrixGroups
open scoped Matrix

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

private def twoBlockMatrix {K : Type*} [Zero K]
    (B D : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![B 0 0, B 0 1, 0, 0;
     B 1 0, B 1 1, 0, 0;
     0, 0, D 0 0, D 0 1;
     0, 0, D 1 0, D 1 1]

private theorem twoBlockMatrix_det {K : Type*} [CommRing K]
    (B D : Matrix (Fin 2) (Fin 2) K) :
    (twoBlockMatrix B D).det = B.det * D.det := by
  have he : (twoBlockMatrix B D).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks B 0 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> rfl
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4), he,
    Matrix.det_fromBlocks_zero₂₁]

private theorem twoBlockMatrix_mul {K : Type*} [Semiring K]
    (B D E F : Matrix (Fin 2) (Fin 2) K) :
    twoBlockMatrix B D * twoBlockMatrix E F = twoBlockMatrix (B * E) (D * F) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [twoBlockMatrix, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

private theorem twoBlockMatrix_adjoint {K : Type*} [CommRing K]
    (σ : K ≃+* K) (B D : Matrix (Fin 2) (Fin 2) K) :
    ((twoBlockMatrix B D).map σ).transpose =
      twoBlockMatrix (B.map σ).transpose (D.map σ).transpose := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [twoBlockMatrix]

private theorem twoBlockMatrix_one {K : Type*} [Semiring K] :
    twoBlockMatrix (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [twoBlockMatrix]

private theorem twoBlockMatrix_commutes {K : Type*} [Ring K]
    (B D : Matrix (Fin 2) (Fin 2) K) :
    twoBlockMatrix B D * Matrix.diagonal ![-1, -1, 1, 1] =
      Matrix.diagonal ![-1, -1, 1, 1] * twoBlockMatrix B D := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [twoBlockMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem exists_twoBlock_normalizer
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (H : HermitianForm 4 K) (hc : ∀ x, H.conj x = x ^ p)
    (hcard : Nat.card K = p ^ 2)
    (hblock : H.form = twoBlockMatrix
      (H.form.submatrix ![0, 1] ![0, 1])
      (H.form.submatrix ![2, 3] ![2, 3])) :
    ∃ Q : GL (Fin 4) K,
      H.conjTranspose Q.val * H.form * Q.val = 1 ∧
      Q.val * Matrix.diagonal ![-1, -1, 1, 1] =
        Matrix.diagonal ![-1, -1, 1, 1] * Q.val := by
  classical
  let B := H.form.submatrix ![0, 1] ![0, 1]
  let D := H.form.submatrix ![2, 3] ![2, 3]
  have hn := H.form_nondegenerate
  rw [hblock, twoBlockMatrix_det] at hn
  obtain ⟨hB, hD⟩ := mul_ne_zero_iff.mp hn
  let HB : HermitianForm 2 K :=
    { conj := H.conj
      conj_involutive := H.conj_involutive
      form := B
      form_hermitian := fun i j => H.form_hermitian _ _
      form_nondegenerate := hB }
  let HD : HermitianForm 2 K :=
    { conj := H.conj
      conj_involutive := H.conj_involutive
      form := D
      form_hermitian := fun i j => H.form_hermitian _ _
      form_nondegenerate := hD }
  obtain ⟨R, hR⟩ := HB.exists_orthonormal_basis_of_prime_frobenius hc hcard
  obtain ⟨S, hS⟩ := HD.exists_orthonormal_basis_of_prime_frobenius hc hcard
  change (R.val.map H.conj).transpose * B * R.val = 1 at hR
  change (S.val.map H.conj).transpose * D * S.val = 1 at hS
  let M := twoBlockMatrix R.val S.val
  have hM : M.det ≠ 0 := by
    rw [twoBlockMatrix_det]
    exact mul_ne_zero R.det_ne_zero S.det_ne_zero
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hM, ?_, ?_⟩
  · change (M.map H.conj).transpose * H.form * M = 1
    change H.form = twoBlockMatrix B D at hblock
    rw [hblock]
    dsimp only [M]
    rw [twoBlockMatrix_adjoint, twoBlockMatrix_mul, twoBlockMatrix_mul,
      hR, hS, twoBlockMatrix_one]
  · exact twoBlockMatrix_commutes R.val S.val

private theorem eigenbasis_adjoint_mul (J : HermitianForm 4 FiniteField.Nine)
    (X Y : Matrix (Fin 4) (Fin 4) FiniteField.Nine) :
    J.conjTranspose (X * Y) = J.conjTranspose Y * J.conjTranspose X := by
  change ((J.conj : FiniteField.Nine →+* FiniteField.Nine).mapMatrix (X * Y)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem eigenbasis_self_adjoint (A : (form 4).specialSubgroup)
    (P : GL (Fin 4) FiniteField.Nine)
    (hP : P * standardInvolutionGL * P⁻¹ = A.val) :
    (form 4).conjTranspose A.val.val = A.val.val := by
  have hs : A.val ^ 2 = 1 := by
    rw [← hP]
    change (MulAut.conj P standardInvolutionGL) ^ 2 = 1
    rw [← map_pow, standardInvolutionGL_sq, map_one]
  have hsq : A.val.val * A.val.val = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val hs
  have hu := ((form 4).mem_specialSubgroup_iff A.val).mp A.property |>.1
  rw [form_gram, mul_one] at hu
  exact (Units.mul_left_inj A.val).mp (hu.trans hsq.symm)

private theorem eigenbasis_gram_commutes (A : (form 4).specialSubgroup)
    (P : GL (Fin 4) FiniteField.Nine)
    (hP : P * standardInvolutionGL * P⁻¹ = A.val) :
    ((form 4).conjTranspose P.val * P.val) * standardInvolutionMatrix =
      standardInvolutionMatrix * ((form 4).conjTranspose P.val * P.val) := by
  have hi : A.val * P = P * standardInvolutionGL := by rw [← hP]; group
  have him : A.val.val * P.val = P.val * standardInvolutionMatrix :=
    congrArg Units.val hi
  have hs : (form 4).conjTranspose standardInvolutionMatrix =
      standardInvolutionMatrix := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [standardInvolutionMatrix, HermitianForm.conjTranspose]
  have ha := congrArg (form 4).conjTranspose him
  rw [eigenbasis_adjoint_mul, eigenbasis_adjoint_mul, eigenbasis_self_adjoint A P hP,
    hs] at ha
  calc
    _ = (form 4).conjTranspose P.val * (P.val * standardInvolutionMatrix) :=
      mul_assoc _ _ _
    _ = (form 4).conjTranspose P.val * (A.val.val * P.val) := by rw [him]
    _ = ((form 4).conjTranspose P.val * A.val.val) * P.val := (mul_assoc _ _ _).symm
    _ = _ := by rw [ha, mul_assoc]

private theorem eigenbasis_gram_hermitian (P : GL (Fin 4) FiniteField.Nine)
    (i j : Fin 4) :
    (form 4).conj (((form 4).conjTranspose P.val * P.val) j i) =
      ((form 4).conjTranspose P.val * P.val) i j := by
  have hc (a : FiniteField.Nine) : (form 4).conj ((form 4).conj a) = a :=
    (form 4).conj_involutive a
  simp [Matrix.mul_apply, HermitianForm.conjTranspose, map_sum, map_mul, hc, mul_comm]

private theorem eigenbasis_gram_nondegenerate (P : GL (Fin 4) FiniteField.Nine) :
    ((form 4).conjTranspose P.val * P.val).det ≠ 0 := by
  have had : ((form 4).conjTranspose P.val).det = (form 4).conj P.val.det := by
    change ((P.val.map (form 4).conj).transpose).det = _
    rw [Matrix.det_transpose]
    exact ((form 4).conj.map_det P.val).symm
  rw [Matrix.det_mul, had]
  exact mul_ne_zero (by simpa using P.det_ne_zero) P.det_ne_zero

private def eigenbasisGramForm (P : GL (Fin 4) FiniteField.Nine) :
    HermitianForm 4 FiniteField.Nine where
  conj := (form 4).conj
  conj_involutive := (form 4).conj_involutive
  form := (form 4).conjTranspose P.val * P.val
  form_hermitian := eigenbasis_gram_hermitian P
  form_nondegenerate := eigenbasis_gram_nondegenerate P

private theorem eigenbasis_gram_block (A : (form 4).specialSubgroup)
    (P : GL (Fin 4) FiniteField.Nine)
    (hP : P * standardInvolutionGL * P⁻¹ = A.val) :
    (eigenbasisGramForm P).form = twoBlockMatrix
      ((eigenbasisGramForm P).form.submatrix ![0, 1] ![0, 1])
      ((eigenbasisGramForm P).form.submatrix ![2, 3] ![2, 3]) := by
  let G := (eigenbasisGramForm P).form
  have hm : G * standardInvolutionMatrix = standardInvolutionMatrix * G :=
    eigenbasis_gram_commutes A P hP
  have hz (x : FiniteField.Nine) (hx : 2 * x = 0) : x = 0 :=
    (mul_eq_zero.mp hx).resolve_left (by decide)
  change G = twoBlockMatrix (G.submatrix ![0, 1] ![0, 1])
    (G.submatrix ![2, 3] ![2, 3])
  apply Matrix.ext
  intro i j
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) FiniteField.Nine => M i j) hm
  fin_cases i <;> fin_cases j <;> simp [twoBlockMatrix]
  all_goals
    simp [standardInvolutionMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    first
    | exact hz _ (by linear_combination h)
    | exact hz _ (by linear_combination -h)

/-- A supplied linear conjugator for the two-plus-two involution can be
normalized to a unitary conjugator, for the original field-nine conjugation. -/
public theorem exists_unitary_conjugator_of_linear
    (A : (form 4).specialSubgroup) (P : GL (Fin 4) FiniteField.Nine)
    (hP : P * standardInvolutionGL * P⁻¹ = A.val) :
    ∃ C : (form 4).unitarySubgroup,
      C.val * standardInvolutionGL * C.val⁻¹ = A.val := by
  let : CharP FiniteField.Nine 3 :=
    charP_of_card_eq_prime_pow (p := 3) (f := 2) FiniteField.Nine.card
  obtain ⟨Q, hQ, hcomm⟩ := exists_twoBlock_normalizer (eigenbasisGramForm P)
    (form_conj_cube 4) FiniteField.Nine.natCard
    (eigenbasis_gram_block A P hP)
  have hu : P * Q ∈ (form 4).unitarySubgroup := by
    rw [HermitianForm.mem_unitarySubgroup_iff, form_gram, mul_one]
    change (form 4).conjTranspose (P.val * Q.val) * (P.val * Q.val) = 1
    rw [eigenbasis_adjoint_mul]
    change (form 4).conjTranspose Q.val *
      ((form 4).conjTranspose P.val * P.val) * Q.val = 1 at hQ
    simpa only [mul_assoc] using hQ
  have hcomm' : Q * standardInvolutionGL = standardInvolutionGL * Q :=
    Units.ext hcomm
  refine ⟨⟨P * Q, hu⟩, ?_⟩
  change (P * Q) * standardInvolutionGL * (P * Q)⁻¹ = A.val
  calc
    _ = P * (Q * standardInvolutionGL) * Q⁻¹ * P⁻¹ := by
      simp only [_root_.mul_inv_rev, mul_assoc]
    _ = P * (standardInvolutionGL * Q) * Q⁻¹ * P⁻¹ := by rw [hcomm']
    _ = A.val := by simpa only [mul_assoc, mul_inv_cancel_left] using hP

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
