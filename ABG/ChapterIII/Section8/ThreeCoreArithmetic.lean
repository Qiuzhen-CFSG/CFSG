module

public import Mathlib.Tactic

/-!
# The numerical odd-core elimination at characteristic three

Write `a` for the order of the part of an involution-centralizer odd core
centralizing a four-group, and `b` for its index in that odd core. ABG's
character estimates and cyclic-defect congruences force `b = 1` in both
character-degree cases. This module proves only that arithmetic implication;
the character estimates and the subsequent normalizer argument are separate.

Since `ab` divides fifteen, each of `a` and `b` belongs to {1,3,5,15}.
In Case I, the bound on `ab³` and its residue modulo eleven exclude `b ≠ 1`.
In Case II, coprimality to three and the residue modulo thirteen do so.

Source: Alperin--Brauer--Gorenstein, III.8 Proposition 5, article p.117,
`refs/original/n-group-global/semidihedral-source/abg-iii7-8.pdf`.
-/

namespace ABG

private theorem divisors_fifteen {n : ℕ} (h : n ∣ 15) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
  have hn := Nat.le_of_dvd (by decide : 0 < 15) h
  interval_cases n <;> norm_num at *

/-- The degree-eleven case of ABG III.8 Proposition 5. -/
public theorem threeCore_index_eq_one_case_one {a b : ℕ}
    (hab : a * b ∣ 15) (hbound : a * b ^ 3 ∣ 3 ^ 4 * 5)
    (hmod : a * b ^ 3 % 11 = 1) : b = 1 := by
  have ha := divisors_fifteen ((dvd_mul_right a b).trans hab)
  have hb := divisors_fifteen ((dvd_mul_left b a).trans hab)
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> norm_num at *

/-- The degree-thirteen case, after the exact three-part calculation. -/
public theorem threeCore_index_eq_one_case_two {a b : ℕ}
    (hab : a * b ∣ 15) (hcop : Nat.Coprime (a * b) 3)
    (hmod : a * b ^ 3 % 13 = 1) : b = 1 := by
  have ha := divisors_fifteen ((dvd_mul_right a b).trans hab)
  have hb := divisors_fifteen ((dvd_mul_left b a).trans hab)
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> norm_num at *

/-- Only the case `b ≠ 1` needs the character estimates in the source proof. -/
public theorem threeCore_index_eq_one_of_bounds {a b : ℕ}
    (hbounds : b ≠ 1 → a * b ∣ 15 ∧
      ((a * b ^ 3 ∣ 3 ^ 4 * 5 ∧ a * b ^ 3 % 11 = 1) ∨
        (Nat.Coprime (a * b) 3 ∧ a * b ^ 3 % 13 = 1))) : b = 1 := by
  by_contra hb
  obtain ⟨hab, h | h⟩ := hbounds hb
  · exact hb (threeCore_index_eq_one_case_one hab h.1 h.2)
  · exact hb (threeCore_index_eq_one_case_two hab h.1 h.2)

end ABG
