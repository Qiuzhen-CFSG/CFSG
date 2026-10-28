module
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Mersenne divisors of binary unitary order factors

A primitive prime divisor forces an exponent larger than 2s to be 6s.
Cancelling the cubic unitary factor then forces the cyclotomic factor
q²+q+1 to divide 6s, which its size excludes. The exceptional binary
Zsigmondy exponent six is checked directly.

This is the elementary arithmetic used for Cartan actors in PSU₃(2ˢ)
automorphism groups, in the endgame of Aschbacher--Smith 7.5.2.
-/
public section
namespace Theory.NumberTheory.BinaryUnitaryDivisors

private theorem six_mul_lt_quadratic (s : ℕ) (hs : 2 ≤ s) :
    6*s < (2^s)^2+2^s+1 := by
  have hh := Nat.two_mul_sq_add_one_le_two_pow_two_mul s
  rw [Nat.mul_comm 2 s, pow_mul] at hh
  by_cases he : s = 2
  · subst s; norm_num
  have hq : 1 ≤ 2^s := Nat.one_le_two_pow
  have hs3 : 3 ≤ s := by omega
  nlinarith

/-- The binary Mersenne divisors of the unitary semilinear exponent bound
have exponent at most twice the fixed-field degree. -/
theorem exponent_le_of_dvd {c s : ℕ} (hs : 2 ≤ s)
    (hd : 2^c-1 ∣ 6*s*((2^s)^3+1)*((2^s)^2-1)) : c ≤ 2*s := by
  by_contra hbad
  have hc : 2*s < c := by omega
  have hc6 : c ≠ 6 := by
    intro he
    have hs2 : s = 2 := by omega
    subst s; subst c
    norm_num at hd
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two (by omega) hc6
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
    have := Nat.le_of_dvd (by have := hp.two_le; omega : 0 < p-1) h
    omega
  have hpc : p ∣ 2^c-1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      ←ho, pow_orderOf_eq_one (2 : ZMod p), sub_self]
  have hpn : ¬ p ∣ 6*s := by
    intro hh
    rcases hp.dvd_mul.mp hh with h6 | hs'
    · rcases hp.dvd_mul.mp (show p ∣ 2*3 from h6) with hd2 | hd3
      · have hpEq := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2
        omega
      · have hpEq := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd3
        omega
    · have := Nat.le_of_dvd (by omega : 0 < s) hs'
      omega
  have hpq2 : ¬ p ∣ (2^s)^2-1 := by
    intro hh
    have he : (2 : ZMod p)^(2*s) = 1 := by
      have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hh
      rw [Nat.cast_sub (one_le_pow₀ Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one, sub_eq_zero] at hz
      simpa only [←pow_mul, Nat.mul_comm] using hz
    have hv := orderOf_dvd_of_pow_eq_one he
    rw [ho] at hv
    have := Nat.le_of_dvd (by omega : 0 < 2*s) hv
    omega
  have hpq3 : p ∣ (2^s)^3+1 := by
    have hh := hpc.trans hd
    exact (hp.dvd_mul.mp ((hp.dvd_mul.mp hh).resolve_right hpq2)).resolve_left hpn
  have hneg : (2 : ZMod p)^(3*s) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hpq3
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      add_eq_zero_iff_eq_neg] at hz
    simpa only [←pow_mul, Nat.mul_comm] using hz
  have h6 : c ∣ 6*s := by
    rw [←ho]
    apply orderOf_dvd_of_pow_eq_one
    rw [show 6*s = (3*s)*2 by omega, pow_mul, hneg]
    simp
  have he : c = 6*s := by
    obtain ⟨k,hk⟩ := h6
    have hkpos : 0 < k := by nlinarith
    have hkle : k ≤ 2 := by nlinarith
    interval_cases k
    · omega
    · have hc3 : c = 3*s := by omega
      have hpow : (2 : ZMod p)^c = 1 := by rw [←ho]; exact pow_orderOf_eq_one (2 : ZMod p)
      rw [hc3,hneg] at hpow
      have ht : (2 : ZMod p) = 0 := by linear_combination -hpow
      exact False.elim (h2 ht)
  rw [he] at hd
  let q := 2^s
  have hq : 2 ≤ q := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show 1 ≤ s by omega)
    simpa [q] using hh
  have hfactor : 2^(6*s)-1 = (q^3-1)*(q^3+1) := by
    rw [mul_comm (q^3-1), ←Nat.sq_sub_sq (q^3) 1]
    simp only [one_pow]
    rw [←pow_mul]
    dsimp [q]
    rw [← pow_mul]
    congr 2; omega
  rw [hfactor] at hd
  have hd' : q^3-1 ∣ 6*s*(q^2-1) := by
    apply (Nat.mul_dvd_mul_iff_right (by positivity : 0 < q^3+1)).mp
    convert hd using 1; ring
  have h3 : q^3-1 = (q-1)*(q^2+q+1) := by
    have he := Nat.sub_add_cancel (show 1 ≤ q by omega)
    have hh := Nat.sub_add_cancel (show 1 ≤ q^3 from one_le_pow₀ (by omega))
    nlinarith
  have hsq : q^2-1 = (q-1)*(q+1) := by simpa [mul_comm] using Nat.sq_sub_sq q 1
  rw [h3,hsq] at hd'
  have hf : q^2+q+1 ∣ 6*s*(q+1) := by
    apply (Nat.mul_dvd_mul_iff_left (by omega : 0 < q-1)).mp
    convert hd' using 1; ring
  have hcop : Nat.Coprime (q^2+q+1) (q+1) := by
    have he : q^2+q+1 = q*(q+1)+1 := by ring
    rw [he, Nat.add_comm, Nat.coprime_add_mul_right_left]
    simp
  have hle := Nat.le_of_dvd (by omega : 0 < 6*s) (hcop.dvd_of_dvd_mul_right hf)
  exact (six_mul_lt_quadratic s hs).not_ge hle
end Theory.NumberTheory.BinaryUnitaryDivisors
