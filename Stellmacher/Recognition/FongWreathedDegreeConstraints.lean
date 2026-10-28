module

public import Stellmacher.Recognition.FongWreathedArithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Numerical premises for Fong's four rational characters

The three nonprincipal rows record the degree and the values at `J`, `XF²`,
and `F²`. The conditions below are arithmetic consequences that must be proved
for actual characters; their definition does not assert character existence.
The value at `F` is one for the second character and minus one for the other
two. In addition to Fong's printed conditions, we retain the contribution
bound at `F²` and integrality of restriction to the Sylow subgroup.

Equation (9) bounds one of the last two degrees by fifty. Clearing its
denominators gives a quadratic equation for the other degree. Once the two
coarse candidates are known, restriction excludes degree 35 and determines
all three values at `F²`. This separates the finite enumeration from the
character theory needed to justify its premises.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), pp. 69–74; and the completion of the omitted
calculation in `refs/original/n-group-global/sylow32-source-audit/
fong-degree-calculation-audit.md`.
-/

namespace Stellmacher.Recognition

/-- The degree and the values at `J`, `XF²`, and `F²`, respectively. -/
public structure FongCharacterRow where
  d : ℤ
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

/-- Conditions for one row, with prescribed value `f` at `F`. -/
public structure FongRowConditions (r : FongCharacterRow) (f : ℤ) : Prop where
  degree_gt : |r.a| < r.d
  involution_odd : Odd r.a
  involution_bound : |r.a| ≤ 5
  degree_congr : r.d % 8 = r.a % 8
  orderFour_congr : r.a % 4 = r.b % 4
  restriction_congr : (r.d - 2 * r.a + 7 * r.b + 2 * f) % 8 = 0
  centralFour_bound : |r.c| ≤ 5
  sylow_restriction : (32 : ℤ) ∣ r.d + 7 * r.a + 6 * r.c + 10 * r.b + 8 * f

/-- Necessary numerical conditions, including the corrected Sylow restriction
filter. The square bound is an inequality, since the full block can contain
more than these four characters. -/
public structure FongDegreeConditions (r₂ r₃ r₄ : FongCharacterRow) : Prop where
  row₂ : FongRowConditions r₂ 1
  row₃ : FongRowConditions r₃ (-1)
  row₄ : FongRowConditions r₄ (-1)
  degree_sum : 1 + r₂.d - r₃.d - r₄.d = 0
  involution_sum : 1 + r₂.a - r₃.a - r₄.a = 0
  orderFour_sum : 1 + r₂.b - r₃.b - r₄.b = 0
  centralFour_sum : 1 + r₂.c - r₃.c - r₄.c = 0
  involution_identity :
    1 + (r₂.a : ℚ) ^ 2 / r₂.d = (r₃.a : ℚ) ^ 2 / r₃.d + (r₄.a : ℚ) ^ 2 / r₄.d
  orderFour_square_bound : 1 + r₂.b ^ 2 + r₃.b ^ 2 + r₄.b ^ 2 ≤ 16

/-- All degrees in the numerical interface are positive. -/
public theorem FongRowConditions.degree_pos {r : FongCharacterRow} {f : ℤ}
    (h : FongRowConditions r f) : 0 < r.d :=
  lt_of_le_of_lt (abs_nonneg r.a) h.degree_gt

/-- The equations are invariant under exchange of the two negative constituents. -/
public theorem FongDegreeConditions.swap {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) : FongDegreeConditions r₂ r₄ r₃ where
  row₂ := h.row₂
  row₃ := h.row₄
  row₄ := h.row₃
  degree_sum := by linarith [h.degree_sum]
  involution_sum := by linarith [h.involution_sum]
  orderFour_sum := by linarith [h.orderFour_sum]
  centralFour_sum := by linarith [h.centralFour_sum]
  involution_identity := by rw [add_comm ((r₄.a : ℚ) ^ 2 / r₄.d)]; exact h.involution_identity
  orderFour_square_bound := by linarith [h.orderFour_square_bound]

/-- At least one degree is bounded, without assuming a bound on the other. -/
public theorem FongDegreeConditions.small_degree {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) : r₃.d ≤ 50 ∨ r₄.d ≤ 50 := by
  have square_bound (r : FongCharacterRow) (hr : |r.a| ≤ 5) : (r.a : ℚ) ^ 2 ≤ 25 := by
    rw [abs_le] at hr
    have hlo : (-5 : ℚ) ≤ r.a := by exact_mod_cast hr.1
    have hhi : (r.a : ℚ) ≤ 5 := by exact_mod_cast hr.2
    nlinarith
  have hh := fong_one_degree_le_fifty r₂.d r₃.d r₄.d r₂.a r₃.a r₄.a
    (by exact_mod_cast h.row₂.degree_pos) (by exact_mod_cast h.row₃.degree_pos)
    (by exact_mod_cast h.row₄.degree_pos)
    (square_bound r₃ h.row₃.involution_bound) (square_bound r₄ h.row₄.involution_bound)
    h.involution_identity
  exact_mod_cast hh

/-- The exact quadratic used to enumerate the unbounded degree. -/
public theorem FongDegreeConditions.quadratic {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) :
    (r₃.d - r₃.a ^ 2) * r₄.d ^ 2 +
      (r₃.d * (r₃.d - 1) + r₂.a ^ 2 * r₃.d - r₃.a ^ 2 * (r₃.d - 1) -
        r₄.a ^ 2 * r₃.d) * r₄.d - r₄.a ^ 2 * r₃.d * (r₃.d - 1) = 0 := by
  have h₂ : (r₂.d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt h.row₂.degree_pos)
  have h₃ : (r₃.d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt h.row₃.degree_pos)
  have h₄ : (r₄.d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt h.row₄.degree_pos)
  have he := h.involution_identity
  field_simp at he
  have hs : (r₂.d : ℚ) = r₃.d + r₄.d - 1 := by exact_mod_cast (by linarith [h.degree_sum] : r₂.d = r₃.d + r₄.d - 1)
  rw [hs] at he
  have result :
      ((r₃.d : ℚ) - r₃.a ^ 2) * r₄.d ^ 2 +
        (r₃.d * (r₃.d - 1) + r₂.a ^ 2 * r₃.d - r₃.a ^ 2 * (r₃.d - 1) -
          r₄.a ^ 2 * r₃.d) * r₄.d - r₄.a ^ 2 * r₃.d * (r₃.d - 1) = 0 := by
    linear_combination he
  exact_mod_cast result

private theorem row_ext (r : FongCharacterRow) (d a b c : ℤ)
    (h : (r.d, r.a, r.b) = (d, a, b)) (hc : r.c = c) : r = ⟨d, a, b, c⟩ := by
  cases r
  simp_all

/-- Restriction completes the degree-27 candidate. -/
public theorem FongDegreeConditions.rows_of_candidate27 {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄)
    (h₂ : (r₂.d, r₂.a, r₂.b) = (27, 3, -1))
    (h₃ : (r₃.d, r₃.a, r₃.b) = (21, 5, 1))
    (h₄ : (r₄.d, r₄.a, r₄.b) = (7, -1, -1)) :
    r₂ = ⟨27, 3, -1, 3⟩ ∧ r₃ = ⟨21, 5, 1, 1⟩ ∧ r₄ = ⟨7, -1, -1, 3⟩ := by
  have h₂' := h₂
  have h₃' := h₃
  have h₄' := h₄
  simp only [Prod.mk.injEq] at h₂' h₃' h₄'
  refine ⟨row_ext _ _ _ _ _ h₂ ?_, row_ext _ _ _ _ _ h₃ ?_, row_ext _ _ _ _ _ h₄ ?_⟩
  · apply fong_degree27_restriction_value _ h.row₂.centralFour_bound
    simpa only [h₂'.1, h₂'.2.1, h₂'.2.2, mul_one] using h.row₂.sylow_restriction
  · apply fong_degree21_restriction_value _ h.row₃.centralFour_bound
    simpa only [h₃'.1, h₃'.2.1, h₃'.2.2] using h.row₃.sylow_restriction
  · apply fong_degree7_restriction_value _ h.row₄.centralFour_bound
    simpa only [h₄'.1, h₄'.2.1, h₄'.2.2] using h.row₄.sylow_restriction

/-- The extra candidate allowed by the printed congruences is impossible. -/
public theorem FongDegreeConditions.not_candidate35 {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) : (r₂.d, r₂.a, r₂.b) ≠ (35, 3, -1) := by
  intro he
  simp only [Prod.mk.injEq] at he
  apply fong_degree35_restriction_impossible _ h.row₂.centralFour_bound
  simpa only [he.1, he.2.1, he.2.2, mul_one] using h.row₂.sylow_restriction

/-- The Sylow order and the two character degrees give the lower group-order
divisibility used in the order-seven argument. -/
public theorem fong_order_lower_of_degrees (n : ℕ)
    (h₂ : 32 ∣ n) (h₂₇ : 27 ∣ n) (h₂₁ : 21 ∣ n) : 6048 ∣ n := by
  exact Nat.lcm_dvd h₂ (Nat.lcm_dvd h₂₇ h₂₁)

end Stellmacher.Recognition
