module
public import Theory.NumberTheory.BinaryPrimitiveDivisor.SixMultiple
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# The cyclotomic obstruction for the Suzuki case

A binary prime of order `6*n` divides `q²-q+1`, where `q=2^n`, but
avoids the Suzuki normalizer bound `(q-1)|Sz(q)|n`. If `n` is odd, three
also divides `q²-q+1`. A nontrivial divisor congruent to one modulo
`q-1` must equal the entire cyclotomic factor, so a power of a prime
other than three cannot have that congruence.

The proofs use the existing binary primitive-prime theorem, elementary
factorization over `ZMod p`, and a bound on the complementary divisor.
The source consumer is the Sylow-prime obstruction in GLS4, Chapter 2,
(14D)–(14E) and Lemma 14.4(a), `refs/KGroup/GLS4/Chapter2.tex`.
-/

public section
namespace Theory.NumberTheory.BinarySuzukiCyclotomic

/-- A primitive prime avoiding the Suzuki normalizer order bound. -/
theorem primitive_prime_data {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≠ 3 ∧
      orderOf (2 : ZMod p) = 6 * n ∧
      p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 ∧
      ¬ p ∣ (2 ^ n - 1) * (((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1)) * n := by
  obtain ⟨p, hp, ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_six_mul hn
  let : Fact p.Prime := ⟨hp⟩
  have hpmin := hp.two_le
  have hp2 : p ≠ 2 := by
    rintro rfl
    change orderOf (0 : ZMod 2) = 6 * n at ho
    rw [orderOf_zero] at ho
    omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hh
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one)
  have horder := ZMod.orderOf_dvd_card_sub_one htwo
  rw [ho] at horder
  have hbound := Nat.le_of_dvd (by omega : 0 < p - 1) horder
  have hnp : n < p := by omega
  have hp3 : p ≠ 3 := by omega
  have hsmall : ∀ k : ℕ, 0 < k → k < 6 * n → (2 : ZMod p) ^ k ≠ 1 := by
    intro k hk hk6 hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ho] at hd
    exact (Nat.le_of_dvd hk hd).not_gt hk6
  have hcube : ((2 : ZMod p) ^ n) ^ 3 = -1 := by
    apply (sq_eq_one_iff.mp ?_).resolve_left
    · rw [← pow_mul]
      exact hsmall (n * 3) (by omega) (by omega)
    · rw [← pow_mul, ← pow_mul, show n * (3 * 2) = 6 * n by omega, ← ho]
      exact pow_orderOf_eq_one _
  have hplus : (2 : ZMod p) ^ n + 1 ≠ 0 := by
    intro hh
    have he : (2 : ZMod p) ^ n = -1 := eq_neg_of_add_eq_zero_left hh
    have hs : (2 : ZMod p) ^ (n * 2) = 1 := by rw [pow_mul, he]; norm_num
    exact hsmall (n * 2) (by omega) (by omega) hs
  have hfactor : ((2 : ZMod p) ^ n) ^ 2 - (2 : ZMod p) ^ n + 1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hplus
    calc
      ((2 : ZMod p) ^ n + 1) * (((2 : ZMod p) ^ n) ^ 2 - (2 : ZMod p) ^ n + 1) =
          ((2 : ZMod p) ^ n) ^ 3 + 1 := by ring
      _ = 0 := by rw [hcube]; ring
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hq2 : 2 ^ n ≤ (2 ^ n) ^ 2 := by nlinarith
  have hd : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_add, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one] using hfactor
  have hminus : ¬ p ∣ 2 ^ n - 1 := by
    intro hd
    have hh := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    rw [Nat.cast_sub hq, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero] at hh
    exact hsmall n (by omega) (by omega) hh
  have hquad : ¬ p ∣ (2 ^ n) ^ 2 + 1 := by
    intro hd
    have hh := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hh
    have he := eq_neg_of_add_eq_zero_left hh
    have hs : (2 : ZMod p) ^ (n * 4) = 1 := by
      calc
        _ = (((2 : ZMod p) ^ n) ^ 2) ^ 2 := by simp only [← pow_mul]; congr 1; omega
        _ = 1 := by rw [he]; norm_num
    exact hsmall (n * 4) (by omega) (by omega) hs
  have hqp : ¬ p ∣ (2 ^ n) ^ 2 := by
    intro hd
    have hh := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    have hz : ((2 : ZMod p) ^ n) ^ 2 = 0 := by simpa using hh
    exact (pow_ne_zero _ (pow_ne_zero _ htwo)) hz
  have hpn : ¬ p ∣ n := fun hd => (Nat.le_of_dvd (by omega) hd).not_gt hnp
  refine ⟨p, hp, hnp, hp3, ho, hd, ?_⟩
  simp only [hp.dvd_mul]
  tauto

/-- A nontrivial divisor with the split-torus congruence exhausts the factor. -/
theorem divisor_eq_cyclotomic_of_congruence {q c : ℕ} (hq : 3 ≤ q) (hc : 1 < c)
    (hd : c ∣ q ^ 2 - q + 1) (hcong : q - 1 ∣ c - 1) :
    c = q ^ 2 - q + 1 := by
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hfactor : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
    zify [hq2, show 1 ≤ q by omega]
    ring
  obtain ⟨k, hk⟩ := hcong
  have hck : c = (q - 1) * k + 1 := by omega
  have hkpos : 0 < k := by nlinarith
  have hqc : q ≤ c := by nlinarith
  obtain ⟨b, hb⟩ := hd
  have hbpos : 0 < b := by rw [hfactor] at hb; nlinarith
  have hbq : b < q := by
    rw [hfactor] at hb
    by_contra hnot
    have : q ≤ b := by omega
    nlinarith
  have hcmod : c % (q - 1) = 1 := by
    rw [hck]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega : 1 < q - 1)
  have hamod : (q ^ 2 - q + 1) % (q - 1) = 1 := by
    rw [hfactor]
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega : 1 < q - 1)
  have hbmod : b % (q - 1) = 1 := by
    rw [hb, Nat.mul_mod, hcmod, Nat.one_mul, Nat.mod_mod] at hamod
    exact hamod
  have hbstrict : b < q - 1 := by
    by_contra hn
    have he : b = q - 1 := by omega
    rw [he, Nat.mod_self] at hbmod
    contradiction
  rw [Nat.mod_eq_of_lt hbstrict] at hbmod
  simpa [hbmod] using hb.symm

/-- Odd binary degree supplies the second prime, three. -/
theorem three_dvd_cyclotomic_odd_binary {n : ℕ} (hn : Odd n) :
    3 ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := by
  have hq : 2 ^ n ≤ (2 ^ n) ^ 2 := by have := Nat.one_le_two_pow (n := n); nlinarith
  apply (ZMod.natCast_eq_zero_iff _ 3).mp
  simp only [Nat.cast_add, Nat.cast_sub hq, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hpow : (2 : ZMod 3) ^ n = -1 := by
    rw [show (2 : ZMod 3) = -1 by decide, hn.neg_one_pow]
  rw [hpow]
  decide

/-- A nontrivial prime power cannot have the free split-torus orbit congruence. -/
theorem prime_power_not_congruent {n p k : ℕ} (hn : 3 ≤ n) (hnodd : Odd n)
    (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k)
    (hd : p ^ k ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) :
    ¬ (2 ^ n - 1) ∣ (p ^ k - 1) := by
  intro hcong
  have hq : 3 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    norm_num at this
    omega
  have hpk : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have he := divisor_eq_cyclotomic_of_congruence hq hpk hd hcong
  have hthree : 3 ∣ p ^ k := he ▸ three_dvd_cyclotomic_odd_binary hnodd
  have htp : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow hthree
  exact hp3 (((Nat.dvd_prime hp).mp htp).resolve_left (by decide)).symm

end Theory.NumberTheory.BinarySuzukiCyclotomic
