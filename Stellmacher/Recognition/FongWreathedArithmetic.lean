module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push

/-!
# Contribution bounds and Sylow restriction in Fong's calculation

The contribution quadratic form bounds the rational character values at the
central involution and at the two inverse classes of order four by five.
The Sylow restriction congruence then excludes the extra degree-35 candidate
left by the numerical conditions explicitly listed in Fong's calculation.
For the surviving degrees it determines the values on those order-four classes.

The quadratic-form argument first bounds the odd integer `u` by one, then
bounds `u + 2v`. The restriction argument is integer arithmetic: the Sylow
class counts are 1, 7, 6, 10, and 8, and their weighted sum is divisible
by the Sylow order 32.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), 65–76, pp. 69–74,
DOI 10.1016/0021-8693(67)90014-2. The restriction filter completes the
omitted calculation; see `refs/original/n-group-global/sylow32-source-audit/
fong-degree-calculation-audit.md`. These results are arithmetic implications;
the character-theoretic premises and the full degree enumeration are separate.
-/

namespace Stellmacher.Recognition

/-- Equation (9) bounds at least one of the two negative-constituent degrees.
No upper bound on the other degree is assumed. -/
public theorem fong_one_degree_le_fifty
    (d s t a b c : ℚ) (hd : 0 < d) (hs : 0 < s) (ht : 0 < t)
    (hb : b ^ 2 ≤ 25) (hc : c ^ 2 ≤ 25)
    (he : 1 + a ^ 2 / d = b ^ 2 / s + c ^ 2 / t) : s ≤ 50 ∨ t ≤ 50 := by
  by_contra h
  push Not at h
  have hb' : b ^ 2 / s < 1 / 2 := (div_lt_iff₀ hs).mpr (by nlinarith)
  have hc' : c ^ 2 / t < 1 / 2 := (div_lt_iff₀ ht).mpr (by nlinarith)
  have ha := div_nonneg (sq_nonneg a) hd.le
  linarith

/-- The order possibilities from a self-centralizing element of order seven
and the Sylow congruence are a finite arithmetic consequence. -/
public theorem fong_order_possibilities
    (n r : ℕ) (hl : 6048 ∣ n) (hu : n ∣ 90720)
    (hr : r = 2 ∨ r = 3 ∨ r = 6)
    (hcong : n / (7 * r) % 7 = 1) :
    (n = 6048 ∧ r = 3) ∨ (n = 18144 ∧ r = 2) ∨ (n = 90720 ∧ r = 3) := by
  obtain ⟨k, rfl⟩ := hl
  have hk : k ≤ 15 := by
    have h := Nat.le_of_dvd (by decide : 0 < 90720) hu
    omega
  rcases hr with rfl | rfl | rfl <;> interval_cases k <;> norm_num at *

/-- Fong's contribution bound applies to either rational order-four class
as well as to the involution class. -/
public theorem fong_abs_value_le_five_of_contribution
    (u v : ℤ) (hu : Odd u)
    (hq : 2 * u ^ 2 + (u - 2 * v) ^ 2 ≤ 15) : |u + 2 * v| ≤ 5 := by
  have hu2 : u ^ 2 ≤ 7 := by nlinarith [sq_nonneg (u - 2 * v)]
  have hub : -2 ≤ u ∧ u ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (u + 2), sq_nonneg (u - 2)]
  have hum : u % 2 = 1 := Int.odd_iff.mp hu
  have he : u = -1 ∨ u = 1 := by omega
  rcases he with rfl | rfl
  · have hv : -2 ≤ v ∧ v ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (v + 2), sq_nonneg (v - 1)]
    rw [abs_le]
    omega
  · have hv : -1 ≤ v ∧ v ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg (v + 1), sq_nonneg (v - 2)]
    rw [abs_le]
    omega

/-- The degree-35 candidate cannot restrict to an integral Sylow character
with the contribution bound at `F²`. -/
public theorem fong_degree35_restriction_impossible
    (c : ℤ) (hc : |c| ≤ 5) :
    ¬ (32 : ℤ) ∣ 35 + 7 * 3 + 6 * c + 10 * (-1) + 8 := by
  rw [abs_le] at hc
  omega

/-- The degree-27 character has value three at `F²`. -/
public theorem fong_degree27_restriction_value
    (c : ℤ) (hc : |c| ≤ 5)
    (hi : (32 : ℤ) ∣ 27 + 7 * 3 + 6 * c + 10 * (-1) + 8) : c = 3 := by
  rw [abs_le] at hc
  omega

/-- The degree-21 character has value one at `F²`. -/
public theorem fong_degree21_restriction_value
    (c : ℤ) (hc : |c| ≤ 5)
    (hi : (32 : ℤ) ∣ 21 + 7 * 5 + 6 * c + 10 * 1 + 8 * (-1)) : c = 1 := by
  rw [abs_le] at hc
  omega

/-- The degree-seven character has value three at `F²`. -/
public theorem fong_degree7_restriction_value
    (c : ℤ) (hc : |c| ≤ 5)
    (hi : (32 : ℤ) ∣ 7 + 7 * (-1) + 6 * c + 10 * (-1) + 8 * (-1)) : c = 3 := by
  rw [abs_le] at hc
  omega

end Stellmacher.Recognition
