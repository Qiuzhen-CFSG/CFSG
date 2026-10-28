module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.LocalArithmetic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The eight arithmetic exclusions in Janko's Lemma 12

Coprimality of the two odd signed degrees extracts the integer quotient by
`128 y (1 + 2y)`. The E16 congruence reduces the remaining square equation to
a square divisor of nine, retaining both signs. For each involution value,
-5 and 3, all four differences 16, -16, 48, -48 contradict the actual local
order factors. The last theorem applies this calculation to actual signed
irreducible degrees. Its degree relation and Suzuki equation remain explicit
premises to be derived from the rejected character decomposition.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 12, p.14.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.SignedAnalysis

/-- The square divisors of nine, retaining both signs. -/
public theorem square_factor_nine (d q : ℤ) (h : q * d ^ 2 = 9) :
    d = 1 ∨ d = -1 ∨ d = 3 ∨ d = -3 := by
  have hd : d ^ 2 ≠ 0 := by intro hd; simp [hd] at h
  have hdpos : 0 < d ^ 2 := lt_of_le_of_ne (sq_nonneg d) (Ne.symm hd)
  have hqpos : 0 < q := by nlinarith
  have hbound : d ^ 2 ≤ 9 := by nlinarith
  have hlo : -3 ≤ d := by
    by_contra hn
    have : d ≤ -4 := by omega
    nlinarith
  have hhi : d ≤ 3 := by
    by_contra hn
    have : 4 ≤ d := by omega
    nlinarith
  interval_cases d <;> norm_num at h <;> omega

/-- All four differences in the rejected Lemma 12 case are forced by the
actual degree divisibilities and the E16 restriction congruence. -/
public theorem rejected_case_differences (g y t : ℤ)
    (hg : 128 ∣ g) (hy : y ∣ g) (hx : 1 + 2 * y ∣ g)
    (hc : 16 ∣ y + 15 * t) (ht : t = -5 ∨ t = 3)
    (he : g * (y - t) ^ 2 = 294912 * y * (1 + 2 * y)) :
    y - t = 16 ∨ y - t = -16 ∨ y - t = 48 ∨ y - t = -48 := by
  obtain ⟨s, hs⟩ := hc
  have hodd : ∃ a : ℤ, y = 2 * a + 1 := by
    rcases ht with ht | ht
    · refine ⟨8 * s + 37, ?_⟩
      omega
    · refine ⟨8 * s - 23, ?_⟩
      omega
  obtain ⟨a, ha⟩ := hodd
  have hxy : IsCoprime y (1 + 2 * y) := ⟨-2, 1, by ring⟩
  have h2y : IsCoprime (2 : ℤ) y := ⟨-a, 1, by rw [ha]; ring⟩
  have h2x : IsCoprime (2 : ℤ) (1 + 2 * y) := ⟨-y, 1, by ring⟩
  have h128 : IsCoprime (128 : ℤ) (y * (1 + 2 * y)) := by
    convert (h2y.mul_right h2x).pow_left (m := 7) using 1
    norm_num
  obtain ⟨q, hq⟩ := h128.mul_dvd hg (hxy.mul_dvd hy hx)
  have hy0 : y ≠ 0 := by omega
  have hx0 : 1 + 2 * y ≠ 0 := by omega
  have hcancel : q * (y - t) ^ 2 = 2304 := by
    have hh : (y * (1 + 2 * y)) * (128 * (q * (y - t) ^ 2 - 2304)) = 0 := by
      rw [hq] at he
      linear_combination he
    have hz := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hy0 hx0)
    linarith
  have hd : y - t = 16 * (s - t) := by omega
  have hn : q * (s - t) ^ 2 = 9 := by
    rw [hd] at hcancel
    nlinarith [hcancel]
  rcases square_factor_nine (s - t) q hn with h | h | h | h <;> omega

/-- The three Suzuki equations in the rejected decomposition eliminate the
other three degree fractions. The remaining variables are signed degree and value. -/
public theorem rejected_case_suzuki_elimination (g y t a b c : ℂ)
    (hy : y ≠ 0) (hx : 1 + 2 * y ≠ 0)
    (h1 : g / 147456 * (a + b + (1 + 2 * t) ^ 2 / (1 + 2 * y)) = 31 / 12)
    (h2 : g / 147456 * (a + t ^ 2 / y + c) = -1)
    (h3 : g / 147456 * (1 + b + t ^ 2 / y - c) = 91 / 12) :
    g * (y - t) ^ 2 = 294912 * y * (1 + 2 * y) := by
  have hc : g / 147456 * ((1 + 2 * t) ^ 2 / (1 + 2 * y) - 2 * t ^ 2 / y - 1) = -4 := by
    linear_combination h1 - h2 - h3
  field_simp at hc
  linear_combination (-1 / 2 : ℂ) * hc

/-- Both involution values, and each of the four possible differences,
contradict one of the actual factors 5, 9, 7 of the group order. -/
public theorem rejected_case_arithmetic (g y t : ℤ)
    (hg : 128 ∣ g) (h5 : 5 ∣ g) (h9 : 9 ∣ g) (h7 : 7 ∣ g)
    (hy : y ∣ g) (hx : 1 + 2 * y ∣ g)
    (hc : 16 ∣ y + 15 * t) (ht : t = -5 ∨ t = 3)
    (he : g * (y - t) ^ 2 = 294912 * y * (1 + 2 * y)) : False := by
  have hd := rejected_case_differences g y t hg hy hx hc ht he
  rcases ht with ht | ht <;> rcases hd with hd | hd | hd | hd
  all_goals
    have hyval : y = t + (y - t) := by ring
    rw [hd, ht] at hyval
    norm_num at hyval
    rw [hyval, ht] at he
    norm_num at he
    clear hg hy hx hc ht hd hyval y t
    omega


open LocalModelDichotomy

/-- The rejected arithmetic branch cannot arise from actual signed irreducible
degrees and the actual local subgroups. The remaining premise is the equation
obtained by eliminating the three Suzuki identities. -/
public theorem rejected_case_of_actual_degrees {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ η : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hη : IsIrreducibleCharacter η)
    (s r t : ℤ) (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ht : (s : ℂ) * χ D.z = (t : ℂ)) (htcases : t = -5 ∨ t = 3)
    (hdegree : r * (hη.degree : ℤ) = 1 + 2 * (s * (hχ.degree : ℤ)))
    (he : (Nat.card G : ℤ) * (s * (hχ.degree : ℤ) - t) ^ 2 =
      294912 * (s * (hχ.degree : ℤ)) * (1 + 2 * (s * (hχ.degree : ℤ)))) : False := by
  obtain ⟨h128, h5, h9, h7⟩ := local_order_factors D k L
  have hy := signed_degree_dvd_order hχ s hs
  have hx := signed_degree_dvd_order hη r hr
  rw [hdegree] at hx
  exact rejected_case_arithmetic (Nat.card G) (s * (hχ.degree : ℤ)) t
    (by exact_mod_cast h128) (by exact_mod_cast h5) (by exact_mod_cast h9)
    (by exact_mod_cast h7) hy hx (signed_degree_congruence D k L hχ s t hs ht) htcases he


end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.SignedAnalysis
