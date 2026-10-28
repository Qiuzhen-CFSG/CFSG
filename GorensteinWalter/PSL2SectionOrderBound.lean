module
public import GorensteinWalter.PSL2CoreModelFacts

/-!
# Field-order bounds for PSL2 sections

If a subgroup of PSL2(F) surjects onto PSL2(E), for odd finite fields,
then the order of E is at most the order of F. This concerns arbitrary
quotient kernels, not only central quotients, and includes order three.
No simplicity hypothesis is needed.

The quotient order divides the subgroup order and is therefore bounded
by the ambient order. The exact PSL2 order formula q(q^2-1)/2 is strictly
increasing for q at least three; its numerator is even. This proves the
comparison-of-orders step in ABG II.3 Lemma2, article p24.
-/

namespace GorensteinWalter

private theorem psl2_order_parameter_le {q r : ℕ} (hq : 3 ≤ q) (_hr : 3 ≤ r)
    (hqodd : Odd q) (hrodd : Odd r)
    (h : r * (r ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / 2) : r ≤ q := by
  have hqdvd : 2 ∣ q * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right (Nat.Odd.sub_odd hqodd.pow odd_one).two_dvd q
  have hrdvd : 2 ∣ r * (r ^ 2 - 1) :=
    dvd_mul_of_dvd_right (Nat.Odd.sub_odd hrodd.pow odd_one).two_dvd r
  have hmul := Nat.mul_le_mul_right 2 h
  rw [Nat.div_mul_cancel hqdvd, Nat.div_mul_cancel hrdvd] at hmul
  by_contra hnot
  have hqr : q < r := by omega
  have hs : q ^ 2 < r ^ 2 := Nat.pow_lt_pow_left hqr (by decide)
  have hqpos : 0 < q ^ 2 := pow_pos (by omega) _
  have hprod : q * (q ^ 2 - 1) < r * (r ^ 2 - 1) :=
    (Nat.mul_lt_mul_of_pos_left (by omega : q ^ 2 - 1 < r ^ 2 - 1)
      (by omega : 0 < q)).trans_le (Nat.mul_le_mul_right _ hqr.le)
  omega

public theorem psl2_section_field_card_le
    (F E : Type*) [Field F] [Finite F] [Field E] [Finite E]
    (hF : IsOddPrimePower (Nat.card F)) (hE : IsOddPrimePower (Nat.card E))
    (U : Subgroup (PSL2 F)) (f : U →* PSL2 E) (hf : Function.Surjective f) :
    Nat.card E ≤ Nat.card F := by
  have hcard : Nat.card (PSL2 E) ≤ Nat.card (PSL2 F) :=
    Nat.le_of_dvd Nat.card_pos
      ((Subgroup.card_dvd_of_surjective f hf).trans U.card_subgroup_dvd_card)
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _, hp, _, hFn⟩ := hF
    rw [hFn]
    exact hp.pow
  have hEodd : Odd (Nat.card E) := by
    obtain ⟨p, n, _, hp, _, hEn⟩ := hE
    rw [hEn]
    exact hp.pow
  rw [psl2_card_formula F hF, psl2_card_formula E hE] at hcard
  exact psl2_order_parameter_le (odd_prime_power_three_le _ hF)
    (odd_prime_power_three_le _ hE) hFodd hEodd hcard

end GorensteinWalter
