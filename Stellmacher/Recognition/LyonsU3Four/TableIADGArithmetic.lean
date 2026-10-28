module

public import Stellmacher.Recognition.LyonsU3Four.TableIEarlyBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The common arithmetic elimination for Table I cases A, D and G

Reciprocal bounds and the residue classes force x = -77 and z = 105,
provided the degree-13 branch obeys Schur's bound. The resulting sum and
product of the two remaining degrees have negative discriminant.
Source: R. Lyons, A Characterization of the Group U₃(4), 1972, p. 382.
The inequalities were checked against the page image, not the OCR.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
local macro "ratlin" : tactic => `(tactic| (simp only [div_eq_mul_inv, one_mul] at *; linarith))

private theorem recip_bounds (n : ℤ) (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hn : (n : ℚ) ≤ -a ∨ b ≤ n) : -1/a ≤ 1/(n:ℚ) ∧ 1/(n:ℚ) ≤ 1/b := by
  rcases hn with hn | hn
  · have hn0 : (n:ℚ) < 0 := by linarith
    constructor
    · apply (le_div_iff_of_neg hn0).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ ha).2
      linarith
    · exact (div_nonpos_of_nonneg_of_nonpos (by norm_num) hn0.le).trans (by positivity)
  · constructor
    · exact (div_nonpos_of_nonpos_of_nonneg (by norm_num) ha.le).trans
        (div_nonneg (by norm_num) (by linarith))
    · exact div_le_div_of_nonneg_left (by norm_num) hb hn

/-- The common numerical system has no solution after the Schur exclusion. -/
theorem tableI_ADG_arithmetic (x y₁ y₂ z : ℤ)
    (hx : x ≤ -13 ∨ 51 ≤ x) (hy₁ : y₁ ≤ -63 ∨ 65 ≤ y₁)
    (hy₂ : y₂ ≤ -63 ∨ 65 ≤ y₂) (hz : z ≤ -87 ∨ 41 ≤ z)
    (hxm : (x-51)%64=0) (hzm : (z-41)%64=0)
    (hsmall : x = -13 → z < 0 → z ≤ -343)
    (h1 : 1+18/(x:ℚ)+1/(y₁:ℚ)+1/(y₂:ℚ)-81/(z:ℚ)=0)
    (h2 : 1+2*x+y₁+y₂-z=0) : False := by
  obtain ⟨b₁l,b₁u⟩ := recip_bounds y₁ 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hy₁)
  obtain ⟨b₂l,b₂u⟩ := recip_bounds y₂ 63 65 (by norm_num) (by norm_num) (by exact_mod_cast hy₂)
  obtain ⟨bxl,bxu⟩ := recip_bounds x 13 51 (by norm_num) (by norm_num) (by exact_mod_cast hx)
  have zx (hl : -(18:ℚ)/141 ≤ 18/(x:ℚ)) : False := by
    have zl : 0 < (81:ℚ)/(z:ℚ) := by ratlin
    have zp : (0:ℚ) < z := ((div_pos_iff.mp zl).resolve_right (by norm_num)).2
    have zlt : (z:ℚ) < 105 := by
      have hh : (81:ℚ)/105 < 81/(z:ℚ) := by ratlin
      have := (lt_div_iff₀ zp).mp hh
      ratlin
    have ze : z = 41 := by
      have : (0:ℤ) < z := by exact_mod_cast zp
      have : z < 105 := by exact_mod_cast zlt
      omega
    rw [ze] at h1
    norm_num at h1
    ratlin
  have xc : x = -13 ∨ x = -77 := by
    by_contra hh
    have xx : x ≤ -141 ∨ 51 ≤ x := by omega
    obtain ⟨hl,_⟩ := recip_bounds x 141 51 (by norm_num) (by norm_num) (by exact_mod_cast xx)
    apply zx
    ratlin
  have xe : x = -77 := by
    rcases xc with xx | xx
    · subst x
      norm_num at h1
      have zn : (z:ℚ) < 0 := by
        have hn : (81:ℚ)/(z:ℚ) < 0 := by ratlin
        exact ((div_neg_iff.mp hn).resolve_right (by norm_num)).2
      have zz := hsmall rfl (by exact_mod_cast zn)
      obtain ⟨bl,_⟩ := recip_bounds z 343 41 (by norm_num) (by norm_num)
        (Or.inl (by exact_mod_cast zz))
      ratlin
    · exact xx
  subst x
  norm_num at h1
  have zp : (0:ℚ) < z := by
    have hh : 0 < (81:ℚ)/(z:ℚ) := by ratlin
    exact ((div_pos_iff.mp hh).resolve_right (by norm_num)).2
  have zlo : (41:ℚ) < z := by
    have hh : (81:ℚ)/(z:ℚ) < 81/41 := by ratlin
    have := (div_lt_iff₀ zp).mp hh
    ratlin
  have zhi : (z:ℚ) < 169 := by
    have hh : (81:ℚ)/169 < 81/(z:ℚ) := by ratlin
    have := (lt_div_iff₀ zp).mp hh
    ratlin
  have ze : z = 105 := by
    have : 41 < z := by exact_mod_cast zlo
    have : z < 169 := by exact_mod_cast zhi
    omega
  subst z
  have hsum : y₁+y₂=258 := by omega
  have hrec : 1/(y₁:ℚ)+1/(y₂:ℚ)=2/385 := by norm_num at h1; ratlin
  have yn₁ : (y₁:ℚ) ≠ 0 := by exact_mod_cast (show y₁ ≠ 0 by omega)
  have yn₂ : (y₂:ℚ) ≠ 0 := by exact_mod_cast (show y₂ ≠ 0 by omega)
  have hp : 385*(y₁+y₂)=2*y₁*y₂ := by
    have hh : (385:ℚ)*(y₁+y₂)=2*y₁*y₂ := by
      field_simp at hrec
      nlinarith [hrec]
    exact_mod_cast hh
  nlinarith [sq_nonneg (y₁-y₂)]
end Stellmacher.Recognition.LyonsU3Four
