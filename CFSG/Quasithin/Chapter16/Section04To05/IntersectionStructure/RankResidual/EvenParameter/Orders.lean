module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SU3.BinarySylowOrder

/-!
# Orders of the signed projective-three exception

The finite field witness makes the supplied parameter a positive prime power,
including in the unitary case, where the coefficient field has order q².
The source congruence makes the scalar divisor exactly three. The resulting
order formula lies between q³(q³−1)(q²−1) and q³(q³+1)(q²−1), giving explicit
integer gaps that exclude fixed group orders.

The last theorem is an explicitly conditional assembly: an elementary abelian
two-subgroup of order greater than four contradicts an odd-field rank bound;
the five small orders left by the proposed E2 comparison are excluded directly.
The model subgroup constructions and the odd-field bound are separate premises.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.18(2),
pp.51–52, and the proof of 16.4.5, p.1184. Matrix orders are reused from the
attributed ATLAS port and Huppert II.10.12; see LICENSES/ATLAS.txt.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.EvenParameter
open Chapter1.Section02.LocalModels
open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
open scoped MatrixGroups

variable {S : Type*} [Group S] {unitary : Bool} {q : ℕ}

/-- The original fixed-field parameter is a positive prime power. -/
theorem parameter_prime_power (h : IsPSLSign S unitary 3 q) : IsPrimePow q := by
  cases unitary with
  | false =>
    obtain ⟨F, _, _, hF, _⟩ := h
    let _ : Fintype F := Fintype.ofFinite F
    simpa only [← Nat.card_eq_fintype_card, hF] using FiniteField.isPrimePow_card F
  | true =>
    obtain ⟨F, _, _, J, hF, _, _⟩ := h
    let _ : Fintype F := Fintype.ofFinite F
    have hpow : IsPrimePow (q ^ 2) := by
      simpa only [← Nat.card_eq_fintype_card, hF] using FiniteField.isPrimePow_card F
    exact hpow.dvd (dvd_pow_self q (by decide : 2 ≠ 0)) (by
      intro hq
      exact hpow.ne_one (by simp only [hq, one_pow]))

/-- The source congruence determines the scalar divisor exactly. -/
theorem signed_order (h : IsPSLSign S unitary 3 q)
    (hc : q % 3 = if unitary then 2 else 1) :
    Nat.card S * 3 = q ^ 3 * (if unitary then q ^ 3 + 1 else q ^ 3 - 1) *
      (q ^ 2 - 1) := by
  have hq : 2 ≤ q := (parameter_prime_power h).two_le
  cases unitary with
  | false =>
    change q % 3 = 1 at hc
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    have ho := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
    rw [← Nat.card_congr e.toEquiv, hF] at ho
    have hd : Nat.gcd 3 (q - 1) = 3 := Nat.gcd_eq_left_iff_dvd.mpr (by omega)
    simpa only [hd, Bool.false_eq_true, ↓reduceIte] using ho
  | true =>
    change q % 3 = 2 at hc
    have hpq := parameter_prime_power h
    obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hpq
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    let _ : Fact p.Prime := ⟨hp⟩
    have hf : Nat.card {x : F // J.conj x = x} = q := by
      rw [← hpn]
      exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn
        (by simpa only [hpn] using hF) (by simpa only [hpn] using hconj)
    obtain ⟨eJ⟩ := FormTransport.exists_projectiveEquiv J q hF hf
    obtain ⟨_, _, _, _, _, _, _, _, ho, _⟩ :=
      BenderSuzuki.External.huppert_II_10_12 (FormTransport.standardForm J) q hF hf rfl
    rw [← Nat.card_congr (e.trans eJ).toEquiv] at ho
    have hd : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left_iff_dvd.mpr (by omega)
    have hdiv : 3 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
      apply dvd_mul_of_dvd_right
      have hf : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq q 1
      rw [hf]
      exact dvd_mul_of_dvd_right (show 3 ∣ q + 1 by omega) _
    simp only [↓reduceIte]
    rw [ho, hd, Nat.div_mul_cancel hdiv]
    ring

private theorem lower_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 3 * (a ^ 3 - 1) * (a ^ 2 - 1) ≤
      b ^ 3 * (b ^ 3 - 1) * (b ^ 2 - 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h 3)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

private theorem upper_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 3 * (a ^ 3 + 1) * (a ^ 2 - 1) ≤
      b ^ 3 * (b ^ 3 + 1) * (b ^ 2 - 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h 3)
    (Nat.add_le_add_right (Nat.pow_le_pow_left h 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

/-- Both signs lie between the two displayed order polynomials. -/
theorem order_bounds (h : IsPSLSign S unitary 3 q)
    (hc : q % 3 = if unitary then 2 else 1) :
    q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) ≤ Nat.card S * 3 ∧
    Nat.card S * 3 ≤ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) := by
  rw [signed_order h hc]
  cases unitary <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals constructor
  all_goals first | exact le_rfl | exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

/-- An integer gap between consecutive parameter bounds excludes a group order. -/
theorem not_card_in_gap (h : IsPSLSign S unitary 3 q)
    (hc : q % 3 = if unitary then 2 else 1) {c N : ℕ}
    (hlo : N ^ 3 * (N ^ 3 + 1) * (N ^ 2 - 1) < c * 3)
    (hhi : c * 3 < (N + 1) ^ 3 * ((N + 1) ^ 3 - 1) * ((N + 1) ^ 2 - 1)) :
    Nat.card S ≠ c := by
  intro heq
  obtain ⟨hl, hu⟩ := order_bounds h hc
  rw [heq] at hl hu
  by_cases hq : q ≤ N
  · exact (not_lt_of_ge (hu.trans (upper_mono hq))) hlo
  · exact (not_lt_of_ge ((lower_mono (show N + 1 ≤ q by omega)).trans hl)) hhi

/-- The order bound needed for the E2 alternative PSL₃(3). -/
theorem parameter_eq_two_of_small_card (h : IsPSLSign S unitary 3 q)
    (hc : q % 3 = if unitary then 2 else 1) (hcard : Nat.card S ≤ 5616) : q = 2 := by
  have hq := (parameter_prime_power h).two_le
  have hl := (order_bounds h hc).1
  have hq4 : q < 4 := by
    by_contra hbad
    have hb := lower_mono (show 4 ≤ q by omega)
    norm_num at hb
    omega
  cases unitary <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc <;> omega

end CFSG.Quasithin.Chapter16.Intersections.EvenParameter

namespace CFSG.Quasithin.Chapter16.Intersections.EvenParameter
open Chapter1.Section02.LocalModels
variable {S : Type*} [Group S] {unitary : Bool} {q : ℕ}

/-- Only an odd-field parameter can obstruct the desired characteristic-two conclusion. -/
public theorem parameter_two_power_or_odd (h : IsPSLSign S unitary 3 q) :
    (∃ n : ℕ, 0 < n ∧ q = 2 ^ n) ∨ Odd q := by
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp (parameter_prime_power h)
  by_cases hp2 : p = 2
  · exact Or.inl ⟨n, hn, by simpa only [hp2] using hpn.symm⟩
  · exact Or.inr (hpn ▸ (hp.odd_of_ne_two hp2).pow)

/-- Conditional assembly from the odd-field bound and actual E2 model invariants. -/
public theorem parameter_two_power_of_elementary_alternatives
    (h : IsPSLSign S unitary 3 q) (hc : q % 3 = if unitary then 2 else 1)
    (hodd : Odd q → ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 4)
    (halternatives : (∃ E : Subgroup S, IsElementaryAbelian 2 E ∧ 4 < Nat.card E) ∨
      Nat.card S = 60 ∨ Nat.card S = 168 ∨ Nat.card S = 360 ∨
        Nat.card S = 6048 ∨ Nat.card S = 62400) :
    ∃ n : ℕ, 0 < n ∧ q = 2 ^ n := by
  rcases parameter_two_power_or_odd h with hq | hq
  · exact hq
  exfalso
  rcases halternatives with ⟨E, hE, hcard⟩ | hcard | hcard | hcard | hcard | hcard
  · exact (not_lt_of_ge (hodd hq E hE)) hcard
  · have heq := parameter_eq_two_of_small_card h hc (by omega)
    exact (by decide : ¬ Odd (2 : ℕ)) (heq ▸ hq)
  · exact not_card_in_gap h hc (N := 2) (by norm_num) (by norm_num) hcard
  · exact not_card_in_gap h hc (N := 2) (by norm_num) (by norm_num) hcard
  · exact not_card_in_gap h hc (N := 3) (by norm_num) (by norm_num) hcard
  · exact not_card_in_gap h hc (N := 4) (by norm_num) (by norm_num) hcard

end CFSG.Quasithin.Chapter16.Intersections.EvenParameter
