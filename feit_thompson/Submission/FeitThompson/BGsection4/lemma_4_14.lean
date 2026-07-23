module

import Mathlib.Data.Nat.Choose.Dvd
public import FeitThompson.BGsection4.lemma_4_13

/-! # Lemma 4.14 from BG Section 4 -/

section Main

private theorem dvd_half_of_odd_prime_dvd_even
    {q n : ℕ} [Fact q.Prime] (hqodd : q ≠ 2) (hn_even : 2 ∣ n) (hqn : q ∣ n) :
    q ∣ n / 2 := by
  have hq_coprime_two : Nat.Coprime q 2 :=
    (Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime q) hqodd).coprime_two_right
  have htwoq : 2 * q ∣ n :=
    hq_coprime_two.symm.mul_dvd_of_dvd_of_dvd hn_even hqn
  rwa [Nat.dvd_div_iff_mul_dvd hn_even]

private theorem two_dvd_one_of_two_prime_dvd_half
    {n : ℕ} (h2n : 2 ∣ n) (h2half : 2 ∣ n / 2) : 4 ∣ n := by
  have hn_even : Even n := by simpa [even_iff_two_dvd] using h2n
  have hmul : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hn_even
  have hfour : 4 ∣ 2 * (n / 2) := by
    simpa [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_dvd_mul_left 2 h2half
  rwa [hmul] at hfour

private theorem two_dvd_half_prime_add_or_sub_one
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) :
    2 ∣ (p + 1) / 2 ∨ 2 ∣ (p - 1) / 2 := by
  have hp_odd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : Nat.Prime p)).2 hpodd
  rcases (Nat.odd_mod_four_iff.mp hp_odd) with hpmod | hpmod
  · right
    have h4 : 4 ∣ p - 1 := by
      refine ⟨p / 4, ?_⟩
      have hdecomp : p % 4 + 4 * (p / 4) = p := Nat.mod_add_div p 4
      rw [hpmod] at hdecomp
      omega
    have h2 : 2 ∣ p - 1 := dvd_trans (by decide : 2 ∣ 4) h4
    rw [Nat.dvd_div_iff_mul_dvd h2]
    simpa [pow_two] using h4
  · left
    have h4 : 4 ∣ p + 1 := by
      refine ⟨p / 4 + 1, ?_⟩
      have hdecomp : p % 4 + 4 * (p / 4) = p := Nat.mod_add_div p 4
      rw [hpmod] at hdecomp
      omega
    have h2 : 2 ∣ p + 1 := dvd_trans (by decide : 2 ∣ 4) h4
    rw [Nat.dvd_div_iff_mul_dvd h2]
    simpa [pow_two] using h4

public theorem lemma_4_14 {R : Type*} [Group R] [Finite R] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅)
    (hqAut : q ∣ Nat.card (MulAut R)) (hq_ne : q ≠ p) :
    q ∣ ((p + 1) / 2) ∨ q ∣ ((p - 1) / 2) := by
  obtain ⟨hq_sq_sub, hq_lt⟩ := lemma_4_13 (R := R) (p := p) (q := q) hpodd hA3 hqAut hq_ne
  have hfac : q ∣ (p - 1) * (p + 1) := by
    have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      simpa [pow_two, Nat.mul_comm] using (Nat.pow_two_sub_pow_two p 1)
    simpa [hsq] using hq_sq_sub
  rcases (Fact.out : Nat.Prime q).dvd_mul.mp hfac with hq_pminus | hq_pplus
  · by_cases hqtwo : q = 2
    · subst hqtwo
      exact two_dvd_half_prime_add_or_sub_one (p := p) hpodd
    · have hhalf : q ∣ (p - 1) / 2 := by
        have h_even : 2 ∣ p - 1 := by
          simpa [even_iff_two_dvd] using (Nat.Prime.even_sub_one (Fact.out : Nat.Prime p) hpodd)
        exact dvd_half_of_odd_prime_dvd_even (q := q) hqtwo
          h_even
          hq_pminus
      exact Or.inr hhalf
  · by_cases hqtwo : q = 2
    · subst hqtwo
      exact two_dvd_half_prime_add_or_sub_one (p := p) hpodd
    · have hhalf : q ∣ (p + 1) / 2 := by
        have hpodd' : Odd p := (Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime p) hpodd)
        have h_even : 2 ∣ p + 1 := by
          simpa [even_iff_two_dvd] using hpodd'.add_one
        exact dvd_half_of_odd_prime_dvd_even (q := q) hqtwo
          h_even
          hq_pplus
      exact Or.inl hhalf
