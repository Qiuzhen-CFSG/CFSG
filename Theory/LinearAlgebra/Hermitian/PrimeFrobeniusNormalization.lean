module

public import BenderSuzuki.External.Huppert.II.theorem_10_4

/-!
# Hermitian normalization for prime Frobenius conjugation

The fixed elements of `x ↦ x^p` in characteristic `p` form the prime
subfield, of cardinality `p`. This identifies the fixed-field hypothesis in
Huppert II.10.4 and yields norm surjectivity and orthonormal bases over a
field of cardinality `p²`, with the original stored conjugation.

This is the normalization input for Aschbacher–Smith, *The Classification
of Quasithin Groups*, A.3.21(a), printed p. 55 (PDF p. 66).
-/

public section

namespace BenderSuzuki.MatrixGroups.HermitianForm

variable {K : Type*} [Field K] {p n : ℕ} [Fact p.Prime] [CharP K p]

/-- Prime Frobenius has exactly `p` fixed elements. -/
theorem card_fixed_of_prime_frobenius (J : HermitianForm n K)
    (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card {x : K // J.conj x = x} = p := by
  have he : {x : K | J.conj x = x} = (⊥ : Subfield K) := by
    ext x
    change J.conj x = x ↔ x ∈ (⊥ : Subfield K)
    rw [hc]
    exact (Subfield.mem_bot_iff_pow_eq_self K p).symm
  exact (Nat.card_congr (Equiv.setCongr he)).trans (Subfield.card_bot K p)

/-- Every nonzero fixed scalar is a Hermitian norm. -/
theorem exists_norm_of_prime_frobenius [Finite K] (J : HermitianForm n K)
    (hc : ∀ x, J.conj x = x ^ p) (hcard : Nat.card K = p ^ 2)
    (a : K) (ha : J.conj a = a) (ha0 : a ≠ 0) :
    ∃ b : K, b ≠ 0 ∧ b * J.conj b = a :=
  External.huppert_II_10_4_norm_surjective J p hcard
    (J.card_fixed_of_prime_frobenius hc) a ha ha0

/-- Every nondegenerate Hermitian form over the quadratic finite field has
an orthonormal basis for the specified prime Frobenius conjugation. -/
theorem exists_orthonormal_basis_of_prime_frobenius [Finite K]
    (J : HermitianForm n K) (hc : ∀ x, J.conj x = x ^ p)
    (hcard : Nat.card K = p ^ 2) :
    ∃ P : GL (Fin n) K,
      J.conjTranspose P.val * J.form * P.val = 1 :=
  External.huppert_II_10_4_a_orthonormal_basis n J p hcard
    (J.card_fixed_of_prime_frobenius hc)

end BenderSuzuki.MatrixGroups.HermitianForm
end
