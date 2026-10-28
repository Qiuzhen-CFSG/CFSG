module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.PrimeRepresentatives
public import Theory.SpecificGroups.Thompson.Model.Simplicity.Reduction
public import Theory.GroupTheory.PrimeCyclicCoverage
public import Mathlib.Tactic.FinCases

/-!
# Sylow reduction for Thompson prime-order cyclic coverage

The proposed order factors as `2^15 * 3^10 * 5^3 * 7^2 * 13 * 19 * 31`.
For 13, 19 and 31, Sylow conjugacy reduces coverage to the order of a single
word. For 2, 3, 5 and 7, actual local fusion certificates are still needed.
This module proves the reduction, not the missing concrete certificates.

The candidate order and words come from
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ . No assertion of class
completeness from that table is used.
-/

@[expose] public section

namespace Thompson.Simplicity

open PrimeCyclicCoverage

/-- The complete prime support of the proposed order. -/
theorem prime_dvd_model_order {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 90745943887872000) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 19 ∨ p = 31 := by
  have hf : 90745943887872000 = 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31 := by
    norm_num
  rw [hf] at hd
  simpa only [hp.dvd_mul,
    hp.prime.dvd_pow_iff_dvd (by decide : 15 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 10 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31), or_assoc] using hd

/-- Primes whose square does not divide the proposed model order. -/
def singlePrime : Fin 3 → ℕ := ![13, 19, 31]

/-- The corresponding indices in the fixed representative table. -/
def singlePrimeIndex : Fin 3 → Fin 9 := ![6, 7, 8]

theorem singlePrime_prime (j : Fin 3) : (singlePrime j).Prime := by
  fin_cases j <;> decide

theorem singlePrime_sq_not_dvd (j : Fin 3) :
    ¬ singlePrime j ^ 2 ∣ 90745943887872000 := by
  fin_cases j <;> decide

/-- The seven prime cases, with the three single-factor cases discharged by
Sylow conjugacy. The concrete order and local certificates remain explicit. -/
theorem prime_cyclic_coverage_of_local
    (hcard : Nat.card Model = 90745943887872000)
    (horders : ∀ j : Fin 3,
      orderOf (primeRepresentative (singlePrimeIndex j)) = singlePrime j)
    (h2 : CoversPrime primeRepresentative 2)
    (h3 : CoversPrime primeRepresentative 3)
    (h5 : CoversPrime primeRepresentative 5)
    (h7 : CoversPrime primeRepresentative 7) :
    ∀ x : Model, (orderOf x).Prime →
      ∃ (i : Fin 9) (k : ℕ) (g : Model),
        primeRepresentative i = g * x ^ k * g⁻¹ := by
  intro x hx
  have hd : orderOf x ∣ 90745943887872000 := hcard ▸ orderOf_dvd_natCard x
  have hs (j : Fin 3) (hj : orderOf x = singlePrime j) :
      ∃ (i : Fin 9) (k : ℕ) (g : Model),
        primeRepresentative i = g * x ^ k * g⁻¹ := by
    obtain ⟨k, g, heq⟩ := exists_conjugate_pow_of_prime_sq_not_dvd
      (singlePrime_prime j) (hcard ▸ singlePrime_sq_not_dvd j) hj (horders j)
    exact ⟨singlePrimeIndex j, k, g, heq⟩
  rcases prime_dvd_model_order hx hd with h | h | h | h | h | h | h
  · exact h2 x h
  · exact h3 x h
  · exact h5 x h
  · exact h7 x h
  · exact hs 0 h
  · exact hs 1 h
  · exact hs 2 h

/-- The first listed representative has order two, using the already certified
matrix relations and noncommutativity. -/
theorem orderOf_primeRepresentative_zero : orderOf (primeRepresentative 0) = 2 := by
  change orderOf generatorA = 2
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime generatorA_sq
  intro h
  exact generator_mul_ne (by simp [h])

/-- The second listed representative has order three. -/
theorem orderOf_primeRepresentative_one : orderOf (primeRepresentative 1) = 3 := by
  change orderOf generatorB = 3
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime generatorB_cube
  intro h
  exact generator_mul_ne (by simp [h])

end Thompson.Simplicity
