module

public import Theory.SpecificGroups.SU3.FullCentralizer
public import Theory.SpecificGroups.SU3.InvolutionEigenbasisGeometry
public import Theory.SpecificGroups.SL3.InvolutionEigenbasis
public import Theory.LinearAlgebra.Hermitian.TwoOneBlockNormalization

/-!
# Unitary eigenbases for finite-field SU₃ involutions

In odd characteristic, a nonidentity determinant-one involution has negative
and positive eigenspaces of dimensions two and one. Its linear eigenbasis has
a Hermitian Gram matrix with orthogonal, nondegenerate diagonal blocks.
Finite-field Hermitian normalization within these blocks gives a unitary
eigenbasis without changing the diagonal action of the involution.

The argument includes characteristic three: the eigenspace dimensions follow
from the determinant and nontriviality, without division by three.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.3.21(a), printed p. 55 (PDF p. 66); Huppert II.10.4 for Hermitian
normalization over finite fields.
-/

public section

open Matrix
open scoped Matrix
open BenderSuzuki.MatrixGroups

namespace Matrix.SU3

variable {K : Type*} [Field K] [Finite K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Every SU₃ involution over the quadratic finite field admits a unitary
eigenbasis, with two negative eigenvectors and one positive eigenvector. -/
theorem exists_unitary_involution_conjugator
    (hp : p ≠ 2) (hcard : Nat.card K = p ^ 2)
    (J : HermitianForm 3 K) (hJ : J.form = 1)
    (hc : ∀ x, J.conj x = x ^ p)
    (A : J.specialSubgroup) (hA : orderOf A = 2) :
    ∃ C : J.unitarySubgroup,
      C.val * (standardInvolution J hJ).val * C.val⁻¹ = A.val := by
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hp
  obtain ⟨P, hP⟩ := SL3.exists_involution_conjugator h2 A.val.val
    (involution_matrix_sq J A hA) (involution_matrix_ne_one J A hA)
    (special_matrix_det J A)
  have hP' : P * (standardInvolution J hJ).val * P⁻¹ = A.val := by
    apply Units.ext
    simpa only [Units.val_mul, standardInvolution_val, SL3.standardInvolution] using hP
  obtain ⟨h02, h12, h20, h21⟩ := eigenbasis_gram_offBlock J hJ h2 A hA P hP'
  obtain ⟨Q, hQ, hcomm⟩ :=
    (eigenbasisGramForm J P).exists_twoOneBlock_normalizer_of_prime_frobenius
      hc hcard h02 h12 h20 h21
  apply unitary_conjugator_of_gram_normalizer J hJ A P hP' Q hQ
  apply Units.ext
  simpa only [Units.val_mul, standardInvolution_val] using hcomm

end Matrix.SU3

end
