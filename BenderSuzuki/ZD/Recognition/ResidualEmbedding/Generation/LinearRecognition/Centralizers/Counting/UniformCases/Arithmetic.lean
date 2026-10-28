module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Arithmetic excluding the noncentral field action

In Lemma 12.9, the three possible local exponents fail for different reasons.
Exponent one exhausts the proper local orbit. For exponent two, the odd
binary field exponent makes the cross-multiplied degree formula impossible
modulo three. For exponent three, cancel the factor `q+1` before reducing at
a prime divisor of `q+1`: the degree is six modulo that prime, whereas the
earlier action theorem gives two. That prime would divide four and also the
odd number `q+1`.

The final injectivity lemma makes the local exponent independent of the
chosen involution once centralization has been proved. All divisions in the
source are replaced by exact identities in the natural numbers.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.8–12.10.
-/

namespace BenderSuzuki.ZD.ResidualCentralizerArithmetic

private theorem noncentral_one {q d : ℕ} (hq : 1 ≤ q)
    (he : (q + 1) * d = (q + 1) * (q * (q - 1) + q + 1)) : d = q ^ 2 + 1 := by
  have he' := Nat.mul_left_cancel (by omega : 0 < q + 1) he
  have hs : q - 1 + 1 = q := Nat.sub_add_cancel hq
  nlinarith

private theorem noncentral_two {k d : ℕ} (ho : Odd k)
    (he : (2 ^ k + 1) * d = ((2 ^ k) ^ 2 + 1) *
      ((2 ^ k) ^ 2 * (2 ^ k - 1) + 2 ^ k + 1)) : False := by
  have hq : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have hm : (2 : ZMod 3) ^ k = -1 := by
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2, ho.neg_one_pow]
  have hs : ((2 ^ k - 1 : ℕ) : ZMod 3) = -2 := by
    rw [Nat.cast_sub hq, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hm]
    ring
  have hh := congrArg (fun a : ℕ => (a : ZMod 3)) he
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hm, hs] at hh
  exact (by decide : (4 : ZMod 3) ≠ 0) hh

private theorem noncentral_three {k d : ℕ} (hk : 2 ≤ k)
    (he : (2 ^ k + 1) * d = ((2 ^ k) ^ 3 + 1) *
      ((2 ^ k) ^ 3 * (2 ^ k - 1) + 2 ^ k + 1))
    (hc : ∀ p : ℕ, p.Prime → p ∣ (2 ^ k) ^ 2 - 1 → Nat.ModEq p d 2) : False := by
  let q := 2 ^ k
  have hq : 1 ≤ q := Nat.one_le_pow k 2 (by decide)
  have hsq : q ≤ q ^ 2 := by nlinarith
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show q + 1 ≠ 1 by omega)
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have hs := Nat.sub_add_cancel hq
    have hs2 := Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)
    nlinarith
  have hcong := hc p hp (by rw [hfac]; exact dvd_mul_of_dvd_left hpd _)
  have hcube : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    have hs := Nat.sub_add_cancel hsq
    nlinarith
  have he' : d = (q ^ 2 - q + 1) * (q ^ 3 * (q - 1) + q + 1) := by
    apply Nat.mul_left_cancel (by omega : 0 < q + 1)
    change (q + 1) * d = _ at he
    rw [hcube, Nat.mul_assoc] at he
    exact he
  have hqm : (q : ZMod p) = -1 := by
    have hh := (ZMod.natCast_eq_zero_iff (q + 1) p).mpr hpd
    push_cast at hh
    exact add_eq_zero_iff_eq_neg.mp hh
  have hcast : (d : ZMod p) = 6 := by
    rw [he']
    push_cast [Nat.cast_sub hq, Nat.cast_sub hsq]
    rw [hqm]
    ring
  have hc2 : (d : ZMod p) = 2 := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcong
  have h4 : (4 : ZMod p) = 0 := by linear_combination hc2 - hcast
  have hpd4 : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h4
  have hp2 : p = 2 := by
    have hd : p ∣ 2 ^ 2 := hpd4
    exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow hd)).antisymm hp.two_le
  subst p
  have h2q : 2 ∣ q := dvd_pow_self 2 (by omega : k ≠ 0)
  obtain ⟨a, ha⟩ := h2q
  obtain ⟨b, hb⟩ := hpd
  omega

/-- The noncentral alternative of Lemma 12.8 contradicts the local orbit
bound and the earlier prime-divisor congruence. -/
public theorem noncentral_impossible {k i d : ℕ} (hk : 2 ≤ k) (hi : i = 1 ∨ i = 2 ∨ i = 3)
    (ho : i = 2 → Odd k) (hlarge : (2 ^ k) ^ 2 + 1 < d)
    (he : (2 ^ k + 1) * d = ((2 ^ k) ^ i + 1) *
      ((2 ^ k) ^ i * (2 ^ k - 1) + 2 ^ k + 1))
    (hc : ∀ p : ℕ, p.Prime → p ∣ (2 ^ k) ^ 2 - 1 → Nat.ModEq p d 2) : False := by
  rcases hi with rfl | rfl | rfl
  · simp only [pow_one] at he
    have hh := noncentral_one (Nat.one_le_pow k 2 (by decide)) he
    omega
  · exact noncentral_two (ho rfl) he
  · exact noncentral_three hk he hc

/-- The degree formula determines the local exponent uniquely. -/
public theorem central_degree_injective {q i j : ℕ} (hq : 2 ≤ q)
    (he : (q ^ i + 1) * (q ^ i * (q - 1) + 1) =
      (q ^ j + 1) * (q ^ j * (q - 1) + 1)) : i = j := by
  have hf : StrictMono (fun x : ℕ => (x + 1) * (x * (q - 1) + 1)) := by
    intro a b hab
    calc
      (a + 1) * (a * (q - 1) + 1) < (b + 1) * (a * (q - 1) + 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ (b + 1) * (b * (q - 1) + 1) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ hab.le) 1)
  exact Nat.pow_right_injective hq (hf.injective he)

end BenderSuzuki.ZD.ResidualCentralizerArithmetic
