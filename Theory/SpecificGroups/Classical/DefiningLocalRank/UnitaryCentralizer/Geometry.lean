module

public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Full SU₃ involution centralizers over arbitrary quadratic finite fields

The negative and positive eigenspaces of a determinant-one involution have
dimensions two and one. Normalize the Hermitian form on each block using
the actual fixed-field cardinality. The resulting unitary eigenbasis gives
a special-unitary conjugator and identifies the full centralizer with GU₂.
This extends the prime-field calculation without changing the stored form
or its conjugation.

Source: Aschbacher–Smith A.2.17, printed p.39, and A.3.21(a), printed p.55;
Hermitian normalization is Huppert II.10.4.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open scoped Matrix
namespace Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer
variable {F : Type*} [Field F] [Finite F]

/-- Normalize the two orthogonal blocks while preserving their eigenspaces. -/
theorem exists_twoOneBlock_normalizer (H : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // H.conj x = x} = q)
    (h02 : H.form 0 2 = 0) (h12 : H.form 1 2 = 0)
    (h20 : H.form 2 0 = 0) (h21 : H.form 2 1 = 0) :
    ∃ Q : GL (Fin 3) F,
      H.conjTranspose Q.val * H.form * Q.val = 1 ∧
      Q.val * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
        !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * Q.val := by
  classical
  let B : Matrix (Fin 2) (Fin 2) F :=
    !![H.form 0 0, H.form 0 1; H.form 1 0, H.form 1 1]
  have hd : H.form.det = B.det * H.form 2 2 := by
    simp [B, Matrix.det_fin_three, Matrix.det_fin_two, h02, h12, h20, h21]
    ring
  have hn := H.form_nondegenerate
  rw [hd] at hn
  obtain ⟨hB, ha⟩ := mul_ne_zero_iff.mp hn
  let H₂ : HermitianForm 2 F :=
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
  let M : Matrix (Fin 3) (Fin 3) F :=
    !![P.val 0 0, P.val 0 1, 0; P.val 1 0, P.val 1 1, 0; 0, 0, b]
  have hM : M.det ≠ 0 := by
    have he : M.det = P.val.det * b := by
      simp [M, Matrix.det_fin_three, Matrix.det_fin_two]
      ring
    rw [he]
    exact mul_ne_zero P.det_ne_zero hb
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hM, ?_, ?_⟩
  · change H.conjTranspose M * H.form * M = 1
    have he (i j : Fin 2) := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A i j) hP
    have h00 := he 0 0
    have h01 := he 0 1
    have h10 := he 1 0
    have h11 := he 1 1
    simp [HermitianForm.conjTranspose, H₂, B, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        h02, h12, h20, h21, h00, h01, h10, h11, hlast]
  · change M * _ = _ * M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_three]

/-- An actual unitary eigenbasis for every nontrivial involution. -/
theorem exists_unitary_involution_conjugator (J : HermitianForm 3 F)
    (hJ : J.form = 1) (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) (h2 : (2 : F) ≠ 0)
    (A : J.specialSubgroup) (hA : orderOf A = 2) :
    ∃ C : J.unitarySubgroup,
      C.val * (SU3.standardInvolution J hJ).val * C.val⁻¹ = A.val := by
  obtain ⟨P, hP⟩ := SL3.exists_involution_conjugator h2 A.val.val
    (SU3.involution_matrix_sq J A hA) (SU3.involution_matrix_ne_one J A hA)
    (SU3.special_matrix_det J A)
  have hP' : P * (SU3.standardInvolution J hJ).val * P⁻¹ = A.val := by
    apply Units.ext
    simpa only [Units.val_mul, SU3.standardInvolution_val, SL3.standardInvolution] using hP
  obtain ⟨h02, h12, h20, h21⟩ := SU3.eigenbasis_gram_offBlock J hJ h2 A hA P hP'
  obtain ⟨Q, hQ, hcomm⟩ := exists_twoOneBlock_normalizer
    (SU3.eigenbasisGramForm J P) q hcard hfixed h02 h12 h20 h21
  apply SU3.unitary_conjugator_of_gram_normalizer J hJ A P hP' Q hQ
  apply Units.ext
  simpa only [Units.val_mul, SU3.standardInvolution_val] using hcomm

/-- The full involution centralizer is the literal two-dimensional unitary group. -/
noncomputable def involutionCentralizerEquiv
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J3.conj x = x} = q) (hchar : (2 : F) ≠ 0)
    (A : J3.specialSubgroup) (hA : orderOf A = 2) :
    J2.unitarySubgroup ≃* Subgroup.centralizer ({A} : Set J3.specialSubgroup) := by
  let h := exists_unitary_involution_conjugator J3 h3 q hcard hfixed hchar A hA
  exact SU3.centralizerEquivOfIsConj J3 J2 h3 h2 hc hchar A
    (SU3.isConj_standard_of_unitary_conjugator J3 h3 A h.choose h.choose_spec)

end Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer
