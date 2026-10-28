module
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Mersenne divisors of semilinear split-torus exponents

A primitive prime divisor of 2^c-1 is greater than c. If c>n, it divides
neither n nor 2^n-1. The exceptional exponent six is excluded directly.
Thus adjoining field automorphisms to a split torus cannot increase its
Mersenne exponent beyond the coefficient-field degree.

Source application: Aschbacher--Smith A.3.15(5), E.3.37 and 11.2.1,
printed pp.50--51,239,766--767.
-/

public section
namespace Theory.NumberTheory

/-- The field-degree factor cannot enlarge a Mersenne divisor of the split-torus exponent. -/
theorem binary_mersenne_exponent_le_of_semilinear_torus_dvd {c n : ℕ}
    (hn : 0 < n) (hd : 2 ^ c - 1 ∣ n * (2 ^ n - 1)) : c ≤ n := by
  by_contra hbad
  have hc : n < c := by omega
  have hc6 : c ≠ 6 := by
    intro he
    subst c
    interval_cases n <;> norm_num at hd
  obtain ⟨p,hp,ho⟩ := exists_prime_orderOf_two (by omega) hc6
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have hz : (2 : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff 2 2).mpr (dvd_refl 2)
    rw [hz, orderOf_zero] at ho
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact fun hz => hp2 ((Nat.dvd_prime Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz) |>.resolve_left hp.ne_one)
  have hpbig : c < p := by
    have h := ZMod.orderOf_dvd_card_sub_one h2
    rw [ho] at h
    have := Nat.le_of_dvd (by have := hp.two_le; omega : 0 < p - 1) h
    omega
  have hpc : p ∣ 2 ^ c - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      ← ho, pow_orderOf_eq_one (2 : ZMod p), sub_self]
  have hpn : ¬ p ∣ n := fun h => by
    have := Nat.le_of_dvd hn h
    omega
  have hq : p ∣ 2 ^ n - 1 := (hp.dvd_mul.mp (hpc.trans hd)).resolve_left hpn
  have he : (2 : ZMod p) ^ n = 1 := by
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hq
    rwa [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, sub_eq_zero] at hz
  have hv := orderOf_dvd_of_pow_eq_one he
  rw [ho] at hv
  exact hc.not_ge (Nat.le_of_dvd hn hv)
end Theory.NumberTheory
