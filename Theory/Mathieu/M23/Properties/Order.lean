module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Theory.Mathieu.M23.Properties.Simplicity

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000

/-!
# Exact order of M23 from its M22 point stabilizer
-/

/-- The full automorphism group of the derived Witt design S(4,7,23) has order 10200960. -/
public theorem m23_order : Nat.card M23 = 10200960 := by
  have hmul := Subgroup.card_mul_index
    (MulAction.stabilizer M23 (9 : Fin 23))
  rw [m23PointStabilizerNine_card,
    MulAction.index_stabilizer_of_transitive M23 (9 : Fin 23),
    Nat.card_fin] at hmul
  omega

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- Prime-power factorization of the order of `M23`. -/
public theorem m23_order_factorization :
    Nat.card M23 = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23 := by
  rw [m23_order]
  norm_num

/-- The prime divisors of the order of `M23` are exactly `2`, `3`, `5`, `7`, `11`, and `23`. -/
public theorem m23_prime_dvd_order_iff (p : ℕ) [Fact (Nat.Prime p)] :
    p ∣ Nat.card M23 ↔
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  rw [m23_order,
    show 10200960 = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 5 * 7 * 11 * 23 by
      norm_num]
  have hp : Nat.Prime p := Fact.out
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 23)]
  aesop

/-- The prime spectrum of `M23`. -/
public theorem m23_prime_spectrum :
    Nat.primeFactors (Nat.card M23) = {2, 3, 5, 7, 11, 23} := by
  ext p
  rw [Nat.mem_primeFactors]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdiv, _⟩
    let : Fact (Nat.Prime p) := ⟨hp⟩
    exact (m23_prime_dvd_order_iff p).mp hdiv
  · intro h
    rw [m23_order]
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide +kernel, by norm_num, by norm_num⟩

end Sporadic.Mathieu
