module

public import Stellmacher.Recognition.LyonsU3Four.TableIDegreeData
import Mathlib.Tactic.FieldSimp

/-!
# The common final calculation in cases U and V

The middle term is `200 / x₅` in case U and the sum of four terms
`25 / x₅⁽ⁱ⁾` in case V. Once the other signed degrees have been determined,
equations (U1) and (U2) give this middle term and the degree twelve row.
Substitution into Lemma 4(c) then gives the coefficient 195 in (4.1).

This module proves the common final algebra, not the earlier inequalities
that force those degrees or the rationality of the degree twelve character.
Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 386,
cases (U) and (V); local PDF in `refs/original/n-group-global/odd-core-rank-two-source/`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four

/-- In either survivor, (U1) determines the combined middle contribution. -/
theorem tableI_survivor_middle (middle : ℚ)
    (hU1 : 1 - 36 / (-13 : ℚ) + 4 / 65 - 98 / 39 + middle + 1 / 65 = 0) :
    middle = -4 / 3 := by
  linarith

/-- Equation (U2) determines the last signed degree, common to U and V. -/
theorem tableI_survivor_last_degree (x : ℚ)
    (hU2 : 1 + 18 / (-13 : ℚ) + 16 / 52 - 1 / 65 - 49 / 39 + 1 / 65 -
      16 / x = 0) : x = -12 := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx] at hU2
    norm_num at hU2
  field_simp at hU2
  linarith

/-- The column in Lemma 4(c), divided by the group order, is `128 / 195`. -/
theorem tableI_survivor_weight (middle : ℚ)
    (hU1 : 1 - 36 / (-13 : ℚ) + 4 / 65 - 98 / 39 + middle + 1 / 65 = 0) :
    1 + 36 / (-13 : ℚ) + 64 / 52 + 98 / 39 + middle + 1 / 65 = 128 / 195 := by
  rw [tableI_survivor_middle middle hU1]
  norm_num

/-- Integer degree and natural-number order versions of the common final
calculation. The caller supplies the forced degrees and the genuine Lemma 4
identity, rather than assuming the desired order formula. -/
theorem tableI_survivor_degree_and_order (x : ℤ) (g c e : ℕ) (middle : ℚ)
    (hU1 : 1 - 36 / (-13 : ℚ) + 4 / 65 - 98 / 39 + middle + 1 / 65 = 0)
    (hU2 : 1 + 18 / (-13 : ℚ) + 16 / 52 - 1 / 65 - 49 / 39 + 1 / 65 -
      16 / (x : ℚ) = 0)
    (hL : (g : ℚ) * e ^ 2 *
      (1 + 36 / (-13 : ℚ) + 64 / 52 + 98 / 39 + middle + 1 / 65) =
        128 * c ^ 3) :
    x = -12 ∧ g * e ^ 2 = 195 * c ^ 3 := by
  constructor
  · exact_mod_cast tableI_survivor_last_degree (x : ℚ) hU2
  · rw [tableI_survivor_weight middle hU1] at hL
    have he : (g : ℚ) * e ^ 2 = 195 * c ^ 3 := by linarith
    exact_mod_cast he

end Stellmacher.Recognition.LyonsU3Four
