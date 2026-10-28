module
public import Theory.NumberTheory.BinarySemilinearTorusDivisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Mersenne orders above powers of split tori

A primitive divisor of 2^c-1 excludes c>n when that Mersenne number divides
n times any power of 2^n-1. The exceptional exponent six is checked using
seven and nine. This permits index bounds to replace exact exponent
calculations for natural-module automizers.

Source application: Aschbacher--Smith A.3.15 and 11.2.1, printed
pp.50--51 and 766--767.
-/

public section
namespace Theory.NumberTheory

/-- Repeated split-torus factors do not increase the Mersenne exponent. -/
theorem binary_mersenne_exponent_le_of_torus_power_dvd {c n k : ℕ}
    (hn : 0 < n) (hd : 2 ^ c - 1 ∣ n * (2 ^ n - 1) ^ k) : c ≤ n := by
  by_contra hbad
  have hc : n < c := by omega
  have hc6 : c ≠ 6 := by
    intro he
    subst c
    interval_cases n
    · norm_num at hd
    · have h7 : 7 ∣ 2 * 3 ^ k := (show 7 ∣ 2 ^ 6 - 1 by decide).trans hd
      have := (Nat.prime_seven.dvd_mul.mp h7).resolve_left (by decide)
      have := Nat.prime_seven.dvd_of_dvd_pow this
      norm_num at this
    · have h9 : 9 ∣ 3 * 7 ^ k := (show 9 ∣ 2 ^ 6 - 1 by decide).trans hd
      have hcop : Nat.Coprime 9 (7 ^ k) := (by decide : Nat.Coprime 9 7).pow_right k
      have := hcop.dvd_of_dvd_mul_right h9
      norm_num at this
    · have h7 : 7 ∣ 4 * 15 ^ k := (show 7 ∣ 2 ^ 6 - 1 by decide).trans hd
      have := (Nat.prime_seven.dvd_mul.mp h7).resolve_left (by decide)
      have := Nat.prime_seven.dvd_of_dvd_pow this
      norm_num at this
    · have h7 : 7 ∣ 5 * 31 ^ k := (show 7 ∣ 2 ^ 6 - 1 by decide).trans hd
      have := (Nat.prime_seven.dvd_mul.mp h7).resolve_left (by decide)
      have := Nat.prime_seven.dvd_of_dvd_pow this
      norm_num at this
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
  have hq : p ∣ 2 ^ n - 1 := hp.dvd_of_dvd_pow
    ((hp.dvd_mul.mp (hpc.trans hd)).resolve_left hpn)
  have he : (2 : ZMod p) ^ n = 1 := by
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hq
    rwa [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, sub_eq_zero] at hz
  have hv := orderOf_dvd_of_pow_eq_one he
  rw [ho] at hv
  exact hc.not_ge (Nat.le_of_dvd hn hv)

end Theory.NumberTheory
