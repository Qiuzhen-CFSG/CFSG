module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.LocalArithmetic

/-!
# Arithmetic in the fourth-induction argument

The three possible branches of the norm-five, nonunit pattern have different
arithmetic obstructions. The first forces 27 to divide the ambient order; the
second, combined with E16 restriction, forces 256 to divide it. The last gives
a quadratic with no integer root modulo nine. These computations preserve the
signed degrees in every denominator. Their explicit Suzuki-equation premises
must still be obtained from the character patterns in Lemma 11.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 11, p.13.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.SignedAnalysis
open LocalModelDichotomy

/-- In the first fourth-induction branch, the second Suzuki equation forces
an extra factor of three in the ambient order. Here y and v are the signed
degree and signed involution value of the double constituent. -/
public theorem fourth_first_suzuki_elimination (g y v : ℂ) (hy : y ≠ 0)
    (h : g / 147456 * (v ^ 2 / y - (32 - 2 * v) ^ 2 / (-2 * y) +
      (32 - 3 * v) ^ 2 / (-3 * y)) = -1) : g = -864 * y := by
  field_simp at h
  linear_combination (1 / 1024 : ℂ) * h

/-- In the second branch, the double constituent has signed value sixteen. -/
public theorem fourth_second_suzuki_elimination (g y : ℂ) (hy : y ≠ 0)
    (h : g / 147456 * (2 * 16 ^ 2 / y) = 25 / 6) : g = 1200 * y := by
  field_simp at h
  linear_combination (1 / 3072 : ℂ) * h

/-- The last branch leaves a quadratic equation in the signed degree.
The fractions keep the signs of all three degrees. -/
public theorem fourth_last_suzuki_elimination (g y : ℂ)
    (hy : y ≠ 0) (hu : -1 - 3 * y ≠ 0)
    (h4 : g / 147456 * (4 ^ 2 / (-2 * y) + 2 * 14 ^ 2 / y) = 25 / 6)
    (h3 : g / 147456 * (1 + 14 ^ 2 / y - 4 ^ 2 / (-2 * y) +
      5 ^ 2 / (-1 - 3 * y)) = 91 / 12) :
    25 * y ^ 2 - 12572 * y - 4124 = 0 := by
  have hg : g = 1600 * y := by
    field_simp at h4
    linear_combination (1 / 4608 : ℂ) * h4
  rw [hg] at h3
  field_simp [hu, show -1 - y * 3 ≠ 0 by simpa [mul_comm] using hu] at h3
  linear_combination (-1 / 4608 : ℂ) * h3

/-- The final quadratic has no integer root: each residue modulo nine fails. -/
public theorem fourth_last_quadratic_impossible (y : ℤ)
    (h : 25 * y ^ 2 - 12572 * y - 4124 = 0) : False := by
  have hm : (25 * (y % 9) ^ 2 - 12572 * (y % 9) - 4124) % 9 = 0 := by
    simpa only [Int.sub_emod, Int.mul_emod, pow_two, Int.emod_emod, Int.zero_emod] using
      congrArg (fun a : ℤ => a % 9) h
  have h0 : 0 ≤ y % 9 := Int.emod_nonneg _ (by norm_num)
  have h9 : y % 9 < 9 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hres : y % 9 <;> norm_num at hm

public theorem fourth_first_order_impossible {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (y : ℤ) (hg : (Nat.card G : ℤ) = -864 * y) : False := by
  apply not_twenty_seven_dvd_order D k L
  have hd : (27 : ℤ) ∣ (Nat.card G : ℤ) := ⟨-32 * y, by rw [hg]; ring⟩
  exact_mod_cast hd

/-- An involution value sixteen forces the signed degree to be divisible by
sixteen; the order equation would then exceed the actual Sylow two-order. -/
public theorem fourth_second_order_impossible {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (s : ℤ) (hs : s = 1 ∨ s = -1) (ht : (s : ℂ) * χ D.z = 16)
    (hg : (Nat.card G : ℤ) = 1200 * (s * (hχ.degree : ℤ))) : False := by
  have hc := signed_degree_congruence D k L hχ s 16 hs (by simpa using ht)
  obtain ⟨r, hr⟩ := hc
  have hd : (256 : ℤ) ∣ (Nat.card G : ℤ) := by
    refine ⟨75 * (r - 15), ?_⟩
    rw [hg]
    linear_combination 1200 * hr
  apply not_two_fifty_six_dvd_order D
  exact_mod_cast hd

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.SignedAnalysis
