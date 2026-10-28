module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# Arithmetic for selecting the character in Theorem 4.1(i)

A weighted column identity with total mass at most M selects a positive
integral coefficient whose character degree is at most that coefficient
times M. Integral column coefficients with square at most 1 + z² are at
least -z. The resulting lower degree bound forces the principal multiplicity
to vanish.

These are the numerical steps (4.4), (4.6), and (4.7) of Glauberman,
*A Characterization of the Suzuki Groups* (1968), pp. 89–90, stored in
`refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open scoped BigOperators

namespace Glauberman.SuzukiCharacterization.CharacterSelection

/-- The weighted column identity selects a positive coefficient with small degree. -/
public theorem exists_degree_le_coefficient_mul {ι : Type*} (s : Finset ι) (c : ι → ℤ) (w d : ι → ℝ)
    (M : ℝ) (hM : 0 < M)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hd : ∀ i ∈ s, 0 < d i)
    (hsum : ∑ i ∈ s, (c i : ℝ) * w i / d i = 1)
    (hbound : ∑ i ∈ s, w i ≤ M) :
    ∃ i ∈ s, 1 ≤ c i ∧ d i ≤ (c i : ℝ) * M := by
  classical
  by_contra! hn
  have hlt (i : ι) (hi : i ∈ s) : (c i : ℝ) * M < d i := by
    by_cases hc : 1 ≤ c i
    · exact hn i hi hc
    · have hc' : (c i : ℝ) ≤ 0 := by exact_mod_cast (show c i ≤ 0 by omega)
      exact (mul_nonpos_of_nonpos_of_nonneg hc' hM.le).trans_lt (hd i hi)
  have hle (i : ι) (hi : i ∈ s) :
      (c i : ℝ) * w i / d i ≤ w i / M := by
    apply (div_le_div_iff₀ (hd i hi) hM).mpr
    nlinarith [mul_le_mul_of_nonneg_right (hlt i hi).le (hw i hi)]
  have hex : ∃ i ∈ s, 0 < w i := by
    by_contra! hz
    have hzero : ∑ i ∈ s, (c i : ℝ) * w i / d i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [le_antisymm (hz i hi) (hw i hi)]
      simp
    linarith
  obtain ⟨i, hi, hwi⟩ := hex
  have hstrict : (c i : ℝ) * w i / d i < w i / M := by
    apply (div_lt_div_iff₀ (hd i hi) hM).mpr
    nlinarith [mul_lt_mul_of_pos_right (hlt i hi) hwi]
  have hsumlt := Finset.sum_lt_sum hle ⟨i, hi, hstrict⟩
  rw [hsum, ← Finset.sum_div] at hsumlt
  have hsumle : (∑ i ∈ s, w i) / M ≤ 1 := (div_le_one hM).mpr hbound
  linarith

/-- The upper and lower degree bounds force zero principal multiplicity. -/
public theorem principal_multiplicity_eq_zero (c₀ c₁ : ℕ) (q M d : ℝ)
    (hq : 0 < q) (hM : 0 ≤ M)
    (hdegree_lower : (c₀ : ℝ) + q + ((c₁ : ℝ) - 1) * M ≤ d)
    (hdegree_upper : d ≤ ((c₁ : ℝ) - c₀) * M) : c₀ = 0 := by
  by_contra hn
  have hc : (1 : ℝ) ≤ c₀ := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hM]

/-- Integrality sharpens the column norm bound to the lower coefficient bound. -/
public theorem neg_degree_le_coefficient_of_sq_le (a : ℤ) (z : ℕ) (hz : 0 < z)
    (hbound : a ^ 2 ≤ 1 + (z : ℤ) ^ 2) : -(z : ℤ) ≤ a := by
  by_contra! hn
  have hz' : (1 : ℤ) ≤ z := by exact_mod_cast hz
  have ha : a ≤ -(z : ℤ) - 1 := by omega
  nlinarith

/-- Equation (4.6), summed over the nonprincipal normalizer orbits. -/
public theorem degree_lower_of_column_sq_bounds {ι : Type*} [DecidableEq ι] (s : Finset ι) (j₁ : ι) (hj₁ : j₁ ∈ s)
    (z c : ι → ℕ) (c₀ : ℕ) (q M d : ℝ)
    (hq : 0 ≤ q) (hz : ∀ j ∈ s, 0 < z j) (hz₁ : z j₁ = 1)
    (hdegree : d = c₀ + q * ∑ j ∈ s, (c j : ℝ) * z j)
    (hmass : M = q * ∑ j ∈ s, (z j : ℝ) ^ 2)
    (hcolumn : ∀ j ∈ s, j ≠ j₁ →
      ((c j : ℤ) - (z j : ℤ) * c j₁) ^ 2 ≤ 1 + (z j : ℤ) ^ 2) :
    (c₀ : ℝ) + q + ((c j₁ : ℝ) - 1) * M ≤ d := by
  have hcoeff (j : ι) (hj : j ∈ s.erase j₁) :
      ((c j₁ : ℝ) - 1) * (z j : ℝ) ^ 2 ≤ (c j : ℝ) * z j := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hj
    have hb := neg_degree_le_coefficient_of_sq_le
      ((c j : ℤ) - (z j : ℤ) * c j₁) (z j) (hz j hmem) (hcolumn j hmem hne)
    have hb' : -(z j : ℝ) ≤ (c j : ℝ) - (z j : ℝ) * c j₁ := by exact_mod_cast hb
    have hmul := mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg (z j) : (0 : ℝ) ≤ z j)
    nlinarith
  have hsum := Finset.sum_le_sum hcoeff
  rw [← Finset.mul_sum] at hsum
  have hsum' : 1 + ((c j₁ : ℝ) - 1) * (∑ j ∈ s, (z j : ℝ) ^ 2) ≤
      ∑ j ∈ s, (c j : ℝ) * z j := by
    rw [← Finset.sum_erase_add _ _ hj₁, ← Finset.sum_erase_add _ _ hj₁]
    simp only [hz₁, Nat.cast_one, one_pow, mul_one]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum' hq
  rw [hdegree, hmass]
  nlinarith

end Glauberman.SuzukiCharacterization.CharacterSelection
