module

public import Theory.GroupTheory.SylowPrimeOrderCoverage
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.NormalGeneration
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.Words

/-!
# Sylow reduction of prime-order coverage for the O'Nan model

The hypothesized cardinality restricts prime element orders to
2, 3, 5, 7, 11, 19 and 31. Primes 5, 11, 19 and 31 occur only once, so
one certified element order suffices for each via Sylow conjugacy. The
order-11 word is already certified by the concrete generator relations.
For the other three primes, a subgroup of full prime-power order and local
conjugate-power coverage suffice. `LocalPrimeCoverage` records exactly these
finite certificates, independently of the ambient cardinality proof.

The fixed representatives come from the ATLAS straight-line program preserved
and attributed in `ProjectiveSimplicity/Words.lean`. No ATLAS class label or
coverage assertion is used as a mathematical premise. The final theorem here
is conditional on the remaining certificates; it does not assert they exist.
-/

namespace ONan.Simplicity

/-- The concrete data needed at a prime dividing the model order repeatedly. -/
@[expose] public def LocalPrimeCoverage (p n : ℕ) : Prop :=
  ∃ H : Subgroup Model, Nat.card H = p ^ n ∧
    ∀ y : H, orderOf y = p → ∃ i k g, primeRepresentative i = g * (y : Model) ^ k * g⁻¹

/-- Local coverage transfers when the subgroup has full prime-power order. -/
public theorem coverage_of_localPrimeCoverage {p n : ℕ} [Fact p.Prime]
    (h : LocalPrimeCoverage p n) (hcard : ¬ p ^ (n + 1) ∣ Nat.card Model)
    (x : Model) (hx : orderOf x = p) :
    ∃ i k g, primeRepresentative i = g * x ^ k * g⁻¹ := by
  obtain ⟨H, hH, hlocal⟩ := h
  exact H.conjugate_power_coverage_of_card primeRepresentative hH hcard hlocal hx

/-- Lagrange's theorem restricts prime orders to the seven prime divisors. -/
public theorem prime_order_cases_of_card (hcard : Nat.card Model = 460815505920)
    (x : Model) (hx : (orderOf x).Prime) :
    orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7 ∨
      orderOf x = 11 ∨ orderOf x = 19 ∨ orderOf x = 31 := by
  have hd : orderOf x ∣ 460815505920 := hcard ▸ orderOf_dvd_natCard x
  have hfactor : 460815505920 = 2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31 := by norm_num
  rw [hfactor] at hd
  simp only [hx.dvd_mul] at hd
  rcases hd with (((((h | h) | h) | h) | h) | h) | h
  · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hx (by decide) h)
  · exact Or.inr (Or.inl (Nat.prime_eq_prime_of_dvd_pow hx (by decide) h))
  · have := ((by decide : Nat.Prime 5).dvd_iff_eq hx.ne_one).mp h
    omega
  · have := Nat.prime_eq_prime_of_dvd_pow hx (by decide : Nat.Prime 7) h
    omega
  · have := ((by decide : Nat.Prime 11).dvd_iff_eq hx.ne_one).mp h
    omega
  · have := ((by decide : Nat.Prime 19).dvd_iff_eq hx.ne_one).mp h
    omega
  · have := ((by decide : Nat.Prime 31).dvd_iff_eq hx.ne_one).mp h
    omega

/-- The representative with source label 11A has order eleven. -/
public theorem orderOf_primeRepresentative_eleven : orderOf (primeRepresentative 5) = 11 := by
  change orderOf (generatorA * generatorB) = 11
  exact orderOf_generatorAB

/-- The order-eleven branch needs no further local matrix certificates. -/
public theorem prime_order_coverage_eleven (hcard : Nat.card Model = 460815505920)
    (x : Model) (hx : orderOf x = 11) :
    ∃ k g, primeRepresentative 5 = g * x ^ k * g⁻¹ := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hn : ¬ 11 ^ 2 ∣ Nat.card Model := by rw [hcard]; norm_num
  exact exists_conjugate_pow_of_orderOf_eq_prime hn orderOf_primeRepresentative_eleven hx

/-- Full coverage from the three local certificates and three remaining
prime-order computations. The order-11 branch is already unconditional apart
from the explicitly supplied ambient cardinality. -/
public theorem prime_order_coverage_of_certificates
    (hcard : Nat.card Model = 460815505920)
    (h2 : LocalPrimeCoverage 2 9) (h3 : LocalPrimeCoverage 3 4)
    (h7 : LocalPrimeCoverage 7 3)
    (h5 : orderOf (primeRepresentative 2) = 5)
    (h19 : orderOf (primeRepresentative 6) = 19)
    (h31 : orderOf (primeRepresentative 7) = 31)
    (x : Model) (hx : (orderOf x).Prime) :
    ∃ i k g, primeRepresentative i = g * x ^ k * g⁻¹ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  rcases prime_order_cases_of_card hcard x hx with hx | hx | hx | hx | hx | hx | hx
  · exact coverage_of_localPrimeCoverage h2 (by rw [hcard]; norm_num) x hx
  · exact coverage_of_localPrimeCoverage h3 (by rw [hcard]; norm_num) x hx
  · obtain ⟨k, g, hg⟩ := exists_conjugate_pow_of_orderOf_eq_prime
      (by rw [hcard]; norm_num : ¬ 5 ^ 2 ∣ Nat.card Model) h5 hx
    exact ⟨2, k, g, hg⟩
  · exact coverage_of_localPrimeCoverage h7 (by rw [hcard]; norm_num) x hx
  · obtain ⟨k, g, hg⟩ := prime_order_coverage_eleven hcard x hx
    exact ⟨5, k, g, hg⟩
  · obtain ⟨k, g, hg⟩ := exists_conjugate_pow_of_orderOf_eq_prime
      (by rw [hcard]; norm_num : ¬ 19 ^ 2 ∣ Nat.card Model) h19 hx
    exact ⟨6, k, g, hg⟩
  · obtain ⟨k, g, hg⟩ := exists_conjugate_pow_of_orderOf_eq_prime
      (by rw [hcard]; norm_num : ¬ 31 ^ 2 ∣ Nat.card Model) h31 hx
    exact ⟨7, k, g, hg⟩
end ONan.Simplicity
