module

public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.PointStabilizer

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000


/-- The full automorphism group of the Witt design S(5,6,12) has order 95040. -/
public theorem m12_order : Nat.card M12 = 95040 := by
  have hcard : Nat.card (MulAction.stabilizer M12 (12 : Fin 12)) = Nat.card M11 :=
    (Nat.card_congr m11EquivM12PointStabilizer).symm
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer M12 (12 : Fin 12))
  rw [hcard, MulAction.index_stabilizer_of_transitive M12 (12 : Fin 12), Nat.card_fin]
    at hmul
  calc
    Nat.card M12 = Nat.card M11 * 12 := hmul.symm
    _ = 95040 := by rw [m11_order]

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- Prime-power factorization of the order of `M12`. -/
public theorem m12_order_factorization :
    Nat.card M12 = 2 ^ 6 * 3 ^ 3 * 5 * 11 := by
  rw [m12_order]
  norm_num

/-- The prime divisors of the order of `M12` are exactly `2`, `3`, `5`, and `11`. -/
public theorem m12_prime_dvd_order_iff (p : ℕ) [Fact (Nat.Prime p)] :
    p ∣ Nat.card M12 ↔ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 11 := by
  rw [m12_order,
    show 95040 = 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 3 * 5 * 11 by norm_num]
  have hp : Nat.Prime p := Fact.out
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 11)]
  aesop

/-- The prime spectrum of `M12`. -/
public theorem m12_prime_spectrum :
    Nat.primeFactors (Nat.card M12) = {2, 3, 5, 11} := by
  ext p
  rw [Nat.mem_primeFactors]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdiv, _⟩
    let : Fact (Nat.Prime p) := ⟨hp⟩
    exact (m12_prime_dvd_order_iff p).mp hdiv
  · intro h
    rw [m12_order]
    rcases h with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide +kernel, by norm_num, by norm_num⟩

end Sporadic.Mathieu
