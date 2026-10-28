module

public import Mathlib.Tactic

/-!
# Arithmetic of the characteristic-three character bounds

The local degree-four bound gives `ab ∣ 15`. The two global degree bounds,
the order formulas, and the Sylow normalizer congruences then give the
precise numerical inputs for eliminating `b ≠ 1`.

All character-theoretic inputs remain hypotheses here. In particular the
exact three-part in the degree-thirteen case is a separate input, supplied
in the source by the cyclic-defect calculation and Brauer--Tuan.

Source: Alperin--Brauer--Gorenstein, III.8 Proposition 5, article p.117.
-/

namespace ABG

private theorem divisors_fifteen {n : ℕ} (h : n ∣ 15) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
  have hn := Nat.le_of_dvd (by decide : 0 < 15) h
  interval_cases n <;> norm_num at *

/-- Cancel the known order of the local quotient from the degree-four bound. -/
public theorem threeCharacter_local_bound {a b : ℕ}
    (h : 48 * (a * b) ∣ 720) : a * b ∣ 15 := by
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 48) h

/-- The order formula removes the extraneous prime seven in the Schur bound. -/
public theorem threeCharacter_case_one_bound {a b : ℕ}
    (hab : a * b ∣ 15)
    (h : 7920 * (a * b ^ 3) ∣ 16 * 3^6 * 5^2 * 7 * 11) :
    a * b ^ 3 ∣ 3^4 * 5 := by
  have ha := divisors_fifteen ((dvd_mul_right a b).trans hab)
  have hb := divisors_fifteen ((dvd_mul_left b a).trans hab)
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> norm_num at *

/-- The corresponding preliminary bound in the degree-thirteen case. -/
public theorem threeCharacter_case_two_bound {a b : ℕ}
    (hab : a * b ∣ 15)
    (h : 5616 * (a * b ^ 3) ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) :
    a * b ^ 3 ∣ 3^5 * 5^3 := by
  have ha := divisors_fifteen ((dvd_mul_right a b).trans hab)
  have hb := divisors_fifteen ((dvd_mul_left b a).trans hab)
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> norm_num at *

/-- The normalizer congruence at eleven in the first order formula. -/
public theorem threeCharacter_case_one_congruence {n : ℕ}
    (h : (7920 * n / 11) % 11 = 5) : n % 11 = 1 := by
  omega

/-- The normalizer congruence at thirteen in the second order formula. -/
public theorem threeCharacter_case_two_congruence {n : ℕ}
    (h : (5616 * n / 13) % 13 = 3) : n % 13 = 1 := by
  omega

/-- Exact three-part `27` excludes three from both local parameters. -/
public theorem threeCharacter_case_two_coprime {a b : ℕ}
    (hab : a * b ∣ 15) (h : ¬ 81 ∣ 5616 * (a * b ^ 3)) :
    Nat.Coprime (a * b) 3 := by
  have ha := divisors_fifteen ((dvd_mul_right a b).trans hab)
  have hb := divisors_fifteen ((dvd_mul_left b a).trans hab)
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> norm_num at *

/-- Assembly from group-order bounds and Sylow normalizer congruences. -/
public theorem threeCharacter_bounds_of_order_data {g a b : ℕ}
    (hlocal : 48 * (a * b) ∣ 720)
    (hcases :
      (g = 7920 * (a * b^3) ∧ g ∣ 16 * 3^6 * 5^2 * 7 * 11 ∧
        (g / 11) % 11 = 5) ∨
      (g = 5616 * (a * b^3) ∧ ¬ 81 ∣ g ∧ (g / 13) % 13 = 3)) :
    a * b ∣ 15 ∧
      ((a * b^3 ∣ 3^4 * 5 ∧ a * b^3 % 11 = 1) ∨
        (Nat.Coprime (a * b) 3 ∧ a * b^3 % 13 = 1)) := by
  have hab := threeCharacter_local_bound hlocal
  refine ⟨hab, ?_⟩
  rcases hcases with ⟨rfl, hbound, hmod⟩ | ⟨rfl, hthree, hmod⟩
  · exact Or.inl ⟨threeCharacter_case_one_bound hab hbound,
      threeCharacter_case_one_congruence hmod⟩
  · exact Or.inr ⟨threeCharacter_case_two_coprime hab hthree,
      threeCharacter_case_two_congruence hmod⟩

end ABG
