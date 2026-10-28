module
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic
/-!
# Orbit arithmetic for defining-prime unitary Sylow products

An odd-prime PSU₃ order has two-part bounded by `3*p²`. A power of two
in this bound which is one modulo `p²` must be one. The bounds follow by
cancelling the odd factors from `(p-1)*(p+1)^2` and comparing modulo eight.
This is the numerical step of the isotropic-point exclusion for the actual
A.3.15 defining-unitary branch; it assumes no local subgroup classification.
-/
public section
namespace UnitaryDefining

private theorem odd_powers_coprime (n k : ℕ) (hn : Odd n) : Nat.Coprime (2^k) n := by
  exact (Nat.coprime_two_left.mpr hn).pow_left _

/-- The two-part of the degree-three unitary order is smaller than three
squares of the defining prime. -/
theorem two_power_bound {p k : ℕ} (hp : 3 < p) (ho : Odd p)
    (hd : 2^k ∣ (p-1)*(p+1)^2) : 2^k < 3*p^2 := by
  have hpmod := (Nat.odd_iff.mp ho)
  have hm : p%4=1 ∨ p%4=3 := by omega
  rcases hm with hm | hm
  · have he : p+1=2*((p+1)/2) := by omega
    have hod : Odd ((p+1)/2) := Nat.odd_iff.mpr (by omega)
    have hd' : 2^k ∣ 4*(p-1) := by
      apply (odd_powers_coprime (((p+1)/2)^2) k hod.pow).dvd_of_dvd_mul_right
      convert hd using 1
      conv_rhs => rw [he]
      ring
    have hb := Nat.le_of_dvd (by omega : 0<4*(p-1)) hd'
    have hp1 : p-1+1=p := by omega
    nlinarith [sq_nonneg (p-2)]
  · have he : p-1=2*((p-1)/2) := by omega
    have hod : Odd ((p-1)/2) := Nat.odd_iff.mpr (by omega)
    have hd' : 2^k ∣ 2*(p+1)^2 := by
      apply (odd_powers_coprime ((p-1)/2) k hod).dvd_of_dvd_mul_left
      convert hd using 1
      conv_rhs => rw [he]
      ring
    have hb := Nat.le_of_dvd (by positivity : 0<2*(p+1)^2) hd'
    have h5 : 5≤p := by omega
    nlinarith [sq_nonneg (p-3)]

/-- A two-power occurring as an orbit and congruent to one modulo p² is one. -/
theorem orbit_eq_one {p k : ℕ} (hp : 3 < p) (ho : Odd p)
    (hb : 2^k < 3*p^2) (hd : p^2 ∣ 2^k-1) : 2^k=1 := by
  have hpos : 0<2^k := by positivity
  obtain ⟨a,ha⟩ := hd
  have he : 2^k = p^2*a+1 := by omega
  have ha3 : a<3 := by nlinarith [sq_pos_of_pos (show 0<p by omega)]
  interval_cases a
  · simpa using he
  · have he' : 2^k = p^2+1 := by simpa using he
    have hbig : 8≤2^k := by rw [he']; nlinarith
    have hk : 3≤k := by by_contra! hn; interval_cases k <;> norm_num at hbig
    have h8 : 8∣2^k := by exact (pow_dvd_pow 2 hk)
    have hp8 : p^2%8=1 := by
      rw [Nat.pow_mod]
      have hm : p%8=1 ∨ p%8=3 ∨ p%8=5 ∨ p%8=7 := by have hh:=(Nat.odd_iff.mp ho); omega
      rcases hm with hm | hm | hm | hm <;> norm_num [hm]
    omega
  · have he' : 2^k=2*p^2+1 := by nlinarith [he]
    have hk : 1≤k := by
      by_contra! hn
      have hk0 : k=0 := by omega
      rw [hk0,pow_zero] at he'
      nlinarith [sq_pos_of_pos (show 0<p by omega)]
    have h2 : 2∣2^k := pow_dvd_pow 2 hk
    omega
end UnitaryDefining

namespace UnitaryDefining
/-- Cancel all odd factors from the actual projective-unitary order. -/
theorem unitary_order_two_power_bound {p k : ℕ} (hp : 3<p) (ho : Odd p)
    (hd : 2^k ∣ (p^3+1)*p^3*(p^2-1)) : 2^k < 3*p^2 := by
  have hpp : p≤p^2 := by nlinarith
  have hsub : p^2-p+p=p^2 := Nat.sub_add_cancel hpp
  have hsub1 : p-1+1=p := by omega
  have hsub2 : p^2-1+1=p^2 := by omega
  have hf : (p^3+1)*p^3*(p^2-1) =
      (p^3*(p^2-p+1))*((p-1)*(p+1)^2) := by
    have h1 : p^3+1=(p+1)*(p^2-p+1) := by nlinarith
    have h2 : p^2-1=(p-1)*(p+1) := by nlinarith
    rw [h1,h2]
    ring
  have hod : Odd (p^2-p+1) := Nat.odd_iff.mpr (by
    have hh:=(Nat.odd_iff.mp ho)
    have hh2 : p^2%2=1 := by rw [Nat.pow_mod,hh]
    omega)
  rw [hf] at hd
  exact two_power_bound hp ho ((odd_powers_coprime _ k (ho.pow.mul hod)).dvd_of_dvd_mul_left hd)
end UnitaryDefining
