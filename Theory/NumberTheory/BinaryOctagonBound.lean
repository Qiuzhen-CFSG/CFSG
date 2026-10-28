module
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Binary exponents from octagon multiplicity

For odd `a+b`, a divisor `2^(b-a)+1` cannot share a prime factor with
`2^(2*(a+b))+1`. The integral polygon multiplicity therefore forces
`b-a` to divide `a`, bounding `b` by `2*a`. The exponent divisibility
uses the gcd formula for binary Mersenne numbers. This includes `a=1`.

Source: Fong--Seitz I (1K), printed pp.6--7.
-/

public section

namespace Nat

private theorem binary_add_one_dvd_square_sub_one (d : ℕ) :
    2^d+1 ∣ 2^(2*d)-1 := by
  refine ⟨2^d-1, ?_⟩
  have hp : 1 ≤ (2:ℕ)^d := one_le_pow d 2 (by omega)
  rw [show 2*d=d*2 by omega, pow_mul, pow_two]
  apply (Nat.sub_eq_iff_eq_add (by nlinarith : 1≤2^d*2^d)).mpr
  nlinarith [Nat.sub_add_cancel hp]

private theorem exponent_dvd_of_binary_add_one_dvd {d n : ℕ} (hd : 0<d)
    (h : 2^d+1 ∣ 2^n+1) : d ∣ n := by
  have hdiv : 2^d+1 ∣ 2^(2*d.gcd n)-1 := by
    have hh := dvd_gcd (binary_add_one_dvd_square_sub_one d)
      (h.trans (binary_add_one_dvd_square_sub_one n))
    rwa [pow_sub_one_gcd_pow_sub_one, gcd_mul_left] at hh
  have hg : 0 < d.gcd n := gcd_pos_of_pos_left n hd
  have hg0 : 0 < 2^(2*d.gcd n)-1 := by
    have hh : 1 < (2:ℕ)^(2*d.gcd n) := one_lt_pow (by omega) (by omega)
    omega
  have hlt : d < 2*d.gcd n := by
    have hh := le_of_dvd hg0 hdiv
    by_contra hle
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega : 2*d.gcd n ≤ d)
    omega
  obtain ⟨k,hk⟩ := gcd_dvd_left d n
  have hk1 : k=1 := by
    have hk0 : 0<k := by nlinarith [hk]
    by_contra hh
    have hk2 : 2≤k := by omega
    nlinarith [hk]
  rw [hk1,mul_one] at hk
  exact hk.symm ▸ gcd_dvd_right d n

private theorem binary_add_one_coprime_even_exponent {d n : ℕ} (hd : Odd d) :
    Coprime (2^d+1) (2^(2*n)+1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpn
  have hd0 : 0<d := hd.pos
  have htwo : ¬2 ∣ 2^d+1 := by
    have he : 2∣2^d := dvd_pow_self 2 (by omega : d ≠ 0)
    intro hh
    have hh' : 2∣1 := (Nat.dvd_add_iff_right he).mpr hh
    norm_num at hh'
  have hpd' : (2:ZMod p)^d = -1 := by
    have hh := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
    push_cast at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hpn' : (2:ZMod p)^(2*n) = -1 := by
    have hh := (ZMod.natCast_eq_zero_iff _ _).mpr hpn
    push_cast at hh
    exact eq_neg_of_add_eq_zero_left hh
  have he : (1:ZMod p) = -1 := by
    calc
      1 = ((2:ZMod p)^d)^(2*n) := by rw [hpd', pow_mul, neg_one_sq, one_pow]
      _ = ((2:ZMod p)^(2*n))^d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = -1 := by rw [hpn', hd.neg_one_pow]
  have hp2 : p∣2 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    norm_num only [Nat.cast_ofNat]
    linear_combination he
  have hpeq : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  exact htwo (hpeq ▸ hpd)

/-- The binary octagon multiplicity and square condition bound either exponent. -/
theorem binary_octagon_degree_le_twice {a b e : ℕ} (ha : 0<a)
    (hodd : Odd (a+b))
    (hdiv : 2^a+2^b ∣
      2^e*(2^(a+b)+1)*(2^(2*(a+b))+1)) : b ≤ 2*a := by
  by_cases hba : b≤a
  · omega
  have hab : a<b := by omega
  let d := b-a
  have hd : 0<d := by dsimp [d]; omega
  have hdodd : Odd d := by
    apply odd_iff.mpr
    have ho := odd_iff.mp hodd
    dsimp [d]
    omega
  have hfactor : 2^a+2^b = 2^a*(2^d+1) := by
    rw [mul_add, mul_one, ← pow_add]
    have hb : a+d=b := by dsimp [d]; omega
    rw [hb,add_comm]
  have hD : 2^d+1 ∣ 2^(a+b)+1 := by
    have hh : 2^d+1 ∣ 2^e*(2^(a+b)+1)*(2^(2*(a+b))+1) := by
      have hf : 2^d+1 ∣ 2^a+2^b := by rw [hfactor]; exact dvd_mul_left _ _
      exact hf.trans hdiv
    have hc : Coprime (2^d+1) 2 := by
      apply coprime_two_right.mpr
      have he : Even (2^d) := Even.pow_of_ne_zero (by decide : Even (2:ℕ)) (by omega : d ≠ 0)
      exact he.add_one
    have hh' := (hc.pow_right e).dvd_mul_left.mp (by simpa only [mul_assoc] using hh)
    exact (binary_add_one_coprime_even_exponent hdodd).dvd_mul_right.mp hh'
  have hdn : d∣a+b := exponent_dvd_of_binary_add_one_dvd hd hD
  have hda : d∣a := by
    have hdd : d∣d := dvd_refl _
    have he : a+b = 2*a+d := by dsimp [d]; omega
    rw [he] at hdn
    have hh := (Nat.dvd_add_iff_left hdd).mpr hdn
    exact hdodd.coprime_two_right.dvd_mul_left.mp hh
  have hle := le_of_dvd ha hda
  dsimp [d] at hle
  omega
end Nat
