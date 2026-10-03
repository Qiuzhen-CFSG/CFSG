module

public import BenderSuzuki.External.Huppert.XI.theorem_3_3
import Mathlib.Data.Nat.GCD.Basic

/-!
# Parameters of Suzuki subgroups

Divisibility of the orders of two positive-parameter Suzuki groups forces
divisibility of their odd field degrees. Indeed, the odd factor `2^d - 1`
of the smaller order divides `(2^(2n) + 1) * (2^n - 1)`, hence `2^(4n) - 1`.
The gcd identity for powers minus one gives `d ∣ 4*n`; oddness gives `d ∣ n`.
At prime ambient degree, every embedding from a positive-parameter Suzuki
group is consequently surjective.

This supplies the arithmetic exclusion of the nonsolvable Suzuki alternatives
in the subgroup theorem recorded in Huppert--Blackburn III, XI.3.12(e).
The order formula is XI.3.3. The subgroup classification itself is a separate
structural input.
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII

private theorem exponent_dvd_of_pow_sub_one_dvd
    {p d n : ℕ} (hp : 2 ≤ p) (h : p ^ d - 1 ∣ p ^ n - 1) : d ∣ n := by
  have hgcd := Nat.gcd_eq_left_iff_dvd.mpr h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hgcd
  have hleft : 1 ≤ p ^ Nat.gcd d n := one_le_pow₀ (by omega)
  have hright : 1 ≤ p ^ d := one_le_pow₀ (by omega)
  have hpow : p ^ Nat.gcd d n = p ^ d := by omega
  have heq := Nat.pow_right_injective hp hpow
  rw [← heq]
  exact Nat.gcd_dvd_right d n

private theorem degree_dvd_of_order_dvd {d n : ℕ} (hd : Odd d) (hdpos : 0 < d)
    (h : ((2 ^ d) ^ 2 + 1) * (2 ^ d) ^ 2 * (2 ^ d - 1) ∣
      ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1)) : d ∣ n := by
  have hdodd : Odd (2 ^ d - 1) := by
    have heven : Even (2 ^ d) := even_two.pow_of_ne_zero (by omega)
    obtain ⟨t, ht⟩ := heven
    have hp : 0 < (2 : ℕ) ^ d := by positivity
    refine ⟨t - 1, ?_⟩
    omega
  have hcop : Nat.Coprime (2 ^ d - 1) ((2 ^ n) ^ 2) :=
    (hdodd.coprime_two_right.pow_right n).pow_right 2
  have hdiv : 2 ^ d - 1 ∣ (2 ^ n) ^ 2 * (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)) := by
    have ht := dvd_trans
      (dvd_mul_left (2 ^ d - 1) (((2 ^ d) ^ 2 + 1) * (2 ^ d) ^ 2)) h
    simpa only [mul_assoc, mul_left_comm] using ht
  have hdiv' := hcop.dvd_of_dvd_mul_left hdiv
  have hn : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow n 2 (by omega)
  have hprod : (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)) * (2 ^ n + 1) =
      (2 ^ n) ^ 4 - 1 := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hn
    rw [hr, Nat.add_sub_cancel_left]
    apply Nat.eq_sub_of_add_eq
    ring
  have hdiv4 : 2 ^ d - 1 ∣ 2 ^ (4 * n) - 1 := by
    have hmul := dvd_mul_of_dvd_left hdiv' (2 ^ n + 1)
    rw [hprod, ← pow_mul, Nat.mul_comm n 4] at hmul
    exact hmul
  have hdn := exponent_dvd_of_pow_sub_one_dvd (by omega : 2 ≤ 2) hdiv4
  have hdcop : Nat.Coprime d 4 := by
    simpa using hd.coprime_two_right.pow_right 2
  exact hdcop.dvd_of_dvd_mul_left hdn

/-- The order formula without an explicit choice of the Tits automorphism. -/
public theorem suzukiMatrixGroup_card (m : ℕ) (hm : 0 < m) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) :=
    iterateFrobeniusEquiv_def K 2 (m + 1)
  exact (External.huppert_blackburn_XI_3_3 m hm pi hpi).2.2.2.2.2.2.1

/-- Order divisibility forces divisibility of the odd field degrees. -/
public theorem suzukiMatrixGroup_degree_dvd_of_card_dvd
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (h : Nat.card (SuzukiMatrixGroup k) ∣ Nat.card (SuzukiMatrixGroup m)) :
    2 * k + 1 ∣ 2 * m + 1 := by
  rw [suzukiMatrixGroup_card k hk, suzukiMatrixGroup_card m hm] at h
  exact degree_dvd_of_order_dvd ⟨k, rfl⟩ (by omega) h

/-- At prime field degree, order divisibility determines the Suzuki parameter. -/
public theorem suzukiMatrixGroup_parameter_eq_of_card_dvd_of_prime
    {k m : ℕ} (hk : 0 < k) (hm : Nat.Prime (2 * m + 1))
    (h : Nat.card (SuzukiMatrixGroup k) ∣ Nat.card (SuzukiMatrixGroup m)) :
    k = m := by
  have hmpos : 0 < m := by have := hm.two_le; omega
  have hdiv := suzukiMatrixGroup_degree_dvd_of_card_dvd hk hmpos h
  rcases (Nat.dvd_prime hm).mp hdiv with hsmall | heq <;> omega

/-- There is no proper embedding of a positive-parameter Suzuki group into a
Suzuki group of prime field degree. -/
public theorem suzukiMatrixGroup_surjective_of_injective_of_prime
    {k m : ℕ} (hk : 0 < k) (hm : Nat.Prime (2 * m + 1))
    (f : SuzukiMatrixGroup k →* SuzukiMatrixGroup m) (hf : Function.Injective f) :
    Function.Surjective f := by
  have hkm := suzukiMatrixGroup_parameter_eq_of_card_dvd_of_prime hk hm
    (Subgroup.card_dvd_of_injective f hf)
  subst k
  exact Finite.surjective_of_injective hf

/-- A proper subgroup at prime field degree cannot be a positive-parameter
Suzuki group. -/
public theorem suzukiMatrixGroup_proper_subgroup_not_equiv
    {m : ℕ} (hm : Nat.Prime (2 * m + 1))
    (H : Subgroup (SuzukiMatrixGroup m)) (hH : H ≠ ⊤)
    {k : ℕ} (hk : 0 < k) : ¬ Nonempty (H ≃* SuzukiMatrixGroup k) := by
  rintro ⟨e⟩
  have hcard := Nat.card_congr e.toEquiv
  have hdiv : Nat.card (SuzukiMatrixGroup k) ∣ Nat.card (SuzukiMatrixGroup m) := by
    rw [← hcard]
    exact H.card_subgroup_dvd_card
  have hkm := suzukiMatrixGroup_parameter_eq_of_card_dvd_of_prime hk hm hdiv
  subst k
  exact hH (H.eq_top_of_card_eq hcard)

end BenderSuzuki.MatrixGroups
