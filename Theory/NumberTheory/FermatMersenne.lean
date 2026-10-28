module

public import Mathlib.NumberTheory.Fermat

/-!
# Equivalent presentations of Mersenne primes

For a prime `p`, the equation `p + 1 = 2 ^ k` is equivalent to saying that
`k` is prime and `p = 2 ^ k - 1`. Positivity of the power justifies natural
subtraction; primality of the exponent follows from the factorization of
`a ^ n - 1`, via Mathlib's `Nat.prime_of_pow_sub_one_prime`.

These conversions reconcile the prime parameters in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2 and Lemma I.4.1
(combined manuscript, 1 March 2004, printed pp. 4 and 415).
-/

namespace Nat.Prime

/-- The exponent in a binary Mersenne presentation of a prime is prime. -/
public theorem add_one_eq_two_pow_iff {p k : ℕ} (hp : p.Prime) :
    p + 1 = 2 ^ k ↔ k.Prime ∧ p = 2 ^ k - 1 := by
  constructor
  · intro h
    have hsub : p = 2 ^ k - 1 := by omega
    refine ⟨(Nat.prime_of_pow_sub_one_prime ?_ (hsub ▸ hp)).2, hsub⟩
    intro hk
    rw [hk] at h
    have := hp.two_le
    norm_num at h
    omega
  · rintro ⟨_, h⟩
    have := Nat.one_le_pow k 2 (by omega)
    omega

/-- Adding primality of the Mersenne exponent does not restrict prime parameters. -/
public theorem exists_add_one_eq_two_pow_iff {p : ℕ} (hp : p.Prime) :
    (∃ k : ℕ, p + 1 = 2 ^ k) ↔ ∃ k : ℕ, k.Prime ∧ p = 2 ^ k - 1 :=
  exists_congr fun _ => hp.add_one_eq_two_pow_iff

end Nat.Prime
