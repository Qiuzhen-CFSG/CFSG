module

public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization

/-!
# Hermitian normalization preserving a two-plus-one decomposition

A nondegenerate three-dimensional Hermitian form with vanishing off-block
entries has nondegenerate two-dimensional and one-dimensional diagonal blocks.
Over a field of cardinality `p²` with prime Frobenius conjugation, normalize
the first block by an orthonormal basis and the last entry by norm surjectivity.
The combined block diagonal change of basis commutes with `diag(-1,-1,1)`.
No restriction on the prime is needed.

Sources: Huppert II.10.4; Aschbacher–Smith, *The Classification of Quasithin
Groups*, A.3.21(a), printed p. 55 (PDF p. 66).
-/

public section

open Matrix
open scoped Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]

/-- Normalize a Hermitian two-plus-one block decomposition by a change of basis
commuting with the diagonal matrix acting as minus one on the first block. -/
theorem exists_twoOneBlock_normalizer_of_prime_frobenius
    (H : HermitianForm 3 K) (hc : ∀ x, H.conj x = x ^ p)
    (hcard : Nat.card K = p ^ 2)
    (h02 : H.form 0 2 = 0) (h12 : H.form 1 2 = 0)
    (h20 : H.form 2 0 = 0) (h21 : H.form 2 1 = 0) :
    ∃ Q : GL (Fin 3) K,
      H.conjTranspose Q.val * H.form * Q.val = 1 ∧
      Q.val * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
        !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * Q.val := by
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
  obtain ⟨P, hP⟩ := H₂.exists_orthonormal_basis_of_prime_frobenius hc hcard
  obtain ⟨b, hb, hnorm⟩ := H.exists_norm_of_prime_frobenius hc hcard
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
      simp [M, Matrix.mul_apply, Fin.sum_univ_three]
end BenderSuzuki.MatrixGroups.HermitianForm
end
