module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The arithmetic contradiction in Lyons's final step

Equation (4.1) and a fourth-power prime divisor of the centralizer index force
its twelfth power to divide the ambient order. No twelfth power of a prime
divides the bound supplied by Schur's theorem for a rational character of
degree twelve. This module proves only the arithmetic implication; the
character bound and the action-index divisibility remain separate inputs.

Source: Lyons, *A Characterization of the Group U₃(4)*, §5, p. 386.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- Schur’s numerical bound for a faithful rational-valued character of degree twelve. -/
@[expose] public def schurBound : ℕ := 2^6 * 3^8 * 5^3 * 7^2 * 11 * 13
public theorem prime_twelfth_not_dvd_schurBound (p : ℕ) (hp : p.Prime) : ¬ p^12 ∣ schurBound := by
  intro h
  have hd : p ∣ schurBound := (dvd_pow_self p (by decide : 12 ≠ 0)).trans h
  have hc : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    simp only [schurBound, hp.dvd_mul, or_assoc] at hd
    rcases hd with h2 | h3 | h5 | h7 | h11 | h13
    · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h2)
    · exact Or.inr (Or.inl (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h3))
    · exact Or.inr (Or.inr (Or.inl (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h5)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h7))))
    · have heq : p = 11 := (Nat.dvd_prime (by decide)).mp h11 |>.resolve_left hp.ne_one
      tauto
    · have heq : p = 13 := (Nat.dvd_prime (by decide)).mp h13 |>.resolve_left hp.ne_one
      tauto
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [schurBound] at h

/-- Cancel the centralizer square in the denominator of Lyons's order formula. -/
public theorem order_eq_of_centralizer_formula (g c d i : ℕ) (hd : 0 < d)
    (hindex : d * i = c) (hformula : g * d ^ 2 = 195 * c ^ 3) :
    g = 195 * d * i ^ 3 := by
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hd 2)
  calc
    g * d ^ 2 = 195 * c ^ 3 := hformula
    _ = (195 * d * i ^ 3) * d ^ 2 := by rw [← hindex]; ring

/-- A fourth-power divisor of the centralizer index contradicts Schur's bound. -/
public theorem no_prime_fourth_dvd_index (g c d i : ℕ) (hd : 0 < d)
    (hindex : d * i = c) (hformula : g * d ^ 2 = 195 * c ^ 3)
    (hbound : g ∣ schurBound) (p : ℕ) (hp : p.Prime) : ¬ p ^ 4 ∣ i := by
  intro hpi
  have hcube : p ^ 12 ∣ i ^ 3 := by
    simpa only [← pow_mul] using pow_dvd_pow_of_dvd hpi 3
  have hg : p ^ 12 ∣ g := by
    rw [order_eq_of_centralizer_formula g c d i hd hindex hformula]
    exact hcube.trans (dvd_mul_left _ _)
  exact prime_twelfth_not_dvd_schurBound p hp (hg.trans hbound)

end Stellmacher.Recognition.LyonsU3Four
