module
public import Stellmacher.Recognition.LyonsU3Four.TableILateMatrices
import Mathlib.Tactic
/-!
# Signed degree bounds for the late Table I cases

The congruence modulo 64 and the sign of the restriction multiplicity give
a gap about zero. Taking reciprocals turns each gap into a closed rational
interval; these intervals drive Lyons's estimates on pp. 384–385. In
particular, the bounds for offsets −90, 87, 75, −165, −114 and 138 use
multiplicity nonnegativity, not merely the congruence.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Lemma 5 and
eliminations (M)–(T), pp. 382–385.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four

def lateInv (x : ℤ) : ℚ := (x : ℚ)⁻¹

namespace LateSignedDegree

theorem nonzero {x b : ℤ} (h : LateSignedDegree x b) : x ≠ 0 := by
  have := h.lower
  intro hx
  simp [hx] at this

theorem gap63 {x : ℤ} (h : LateSignedDegree x 63) : x ≤ -63 ∨ 65 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + 63) % 64 = 0 % 64 at hm
  omega

theorem gap12 {x : ℤ} (h : LateSignedDegree x 12) : x ≤ -12 ∨ 52 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + 12) % 64 = 0 % 64 at hm
  omega

theorem gap_neg90 {x : ℤ} (h : LateSignedDegree x (-90)) : x ≤ -38 ∨ 90 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + -90) % 64 = 0 % 64 at hm
  rcases mul_nonneg_iff.mp h.nonneg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

theorem gap87 {x : ℤ} (h : LateSignedDegree x 87) : x ≤ -87 ∨ 41 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + 87) % 64 = 0 % 64 at hm
  rcases mul_nonneg_iff.mp h.nonneg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

theorem gap75 {x : ℤ} (h : LateSignedDegree x 75) : x ≤ -75 ∨ 53 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + 75) % 64 = 0 % 64 at hm
  rcases mul_nonneg_iff.mp h.nonneg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

theorem gap_neg165 {x : ℤ} (h : LateSignedDegree x (-165)) : x ≤ -27 ∨ 165 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + -165) % 64 = 0 % 64 at hm
  rcases mul_nonneg_iff.mp h.nonneg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

theorem gap_neg51 {x : ℤ} (h : LateSignedDegree x (-51)) : x ≤ -13 ∨ 51 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + -51) % 64 = 0 % 64 at hm
  omega

theorem gap_neg114 {x : ℤ} (h : LateSignedDegree x (-114)) : x ≤ -14 ∨ 114 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + -114) % 64 = 0 % 64 at hm
  rcases mul_nonneg_iff.mp h.nonneg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

theorem gap_neg39 {x : ℤ} (h : LateSignedDegree x (-39)) : x ≤ -25 ∨ 39 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + -39) % 64 = 0 % 64 at hm
  omega

theorem gap138 {x : ℤ} (h : LateSignedDegree x 138) : x ≤ -138 ∨ 54 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + 138) % 64 = 0 % 64 at hm
  rcases mul_nonneg_iff.mp h.nonneg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

end LateSignedDegree

/-- Bounds on reciprocals across a gap containing zero. -/
theorem lateInv_bounds {x : ℤ} {a b : ℤ} (ha : a < 0) (hb : 0 < b)
    (h : x ≤ a ∨ b ≤ x) : lateInv a ≤ lateInv x ∧ lateInv x ≤ lateInv b := by
  have ha' : (a : ℚ) < 0 := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  rcases h with h | h
  · have hx : (x : ℚ) ≤ a := by exact_mod_cast h
    have hn := hx.trans_lt ha'
    exact ⟨(inv_le_inv_of_neg ha' hn).mpr hx,
      (le_of_lt (inv_neg''.mpr hn)).trans (le_of_lt (inv_pos.mpr hb'))⟩
  · have hx : (b : ℚ) ≤ x := by exact_mod_cast h
    have hp := hb'.trans_le hx
    exact ⟨(le_of_lt (inv_neg''.mpr ha')).trans (le_of_lt (inv_pos.mpr hp)),
      (inv_le_inv₀ hp hb').mpr hx⟩

theorem LateSignedDegree.invBounds63 {x : ℤ} (h : LateSignedDegree x (63)) :
    -1 / 63 ≤ lateInv x ∧ lateInv x ≤ 1 / 65 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-63 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 65) h.gap63

theorem LateSignedDegree.invBounds12 {x : ℤ} (h : LateSignedDegree x (12)) :
    -1 / 12 ≤ lateInv x ∧ lateInv x ≤ 1 / 52 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-12 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 52) h.gap12

theorem LateSignedDegree.invBoundsneg90 {x : ℤ} (h : LateSignedDegree x (-90)) :
    -1 / 38 ≤ lateInv x ∧ lateInv x ≤ 1 / 90 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-38 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 90) h.gap_neg90

theorem LateSignedDegree.invBounds87 {x : ℤ} (h : LateSignedDegree x (87)) :
    -1 / 87 ≤ lateInv x ∧ lateInv x ≤ 1 / 41 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-87 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 41) h.gap87

theorem LateSignedDegree.invBounds75 {x : ℤ} (h : LateSignedDegree x (75)) :
    -1 / 75 ≤ lateInv x ∧ lateInv x ≤ 1 / 53 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-75 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 53) h.gap75

theorem LateSignedDegree.invBoundsneg165 {x : ℤ} (h : LateSignedDegree x (-165)) :
    -1 / 27 ≤ lateInv x ∧ lateInv x ≤ 1 / 165 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-27 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 165) h.gap_neg165

theorem LateSignedDegree.invBoundsneg51 {x : ℤ} (h : LateSignedDegree x (-51)) :
    -1 / 13 ≤ lateInv x ∧ lateInv x ≤ 1 / 51 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-13 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 51) h.gap_neg51

theorem LateSignedDegree.invBoundsneg114 {x : ℤ} (h : LateSignedDegree x (-114)) :
    -1 / 14 ≤ lateInv x ∧ lateInv x ≤ 1 / 114 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-14 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 114) h.gap_neg114

theorem LateSignedDegree.invBoundsneg39 {x : ℤ} (h : LateSignedDegree x (-39)) :
    -1 / 25 ≤ lateInv x ∧ lateInv x ≤ 1 / 39 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-25 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 39) h.gap_neg39

theorem LateSignedDegree.invBounds138 {x : ℤ} (h : LateSignedDegree x (138)) :
    -1 / 138 ≤ lateInv x ∧ lateInv x ≤ 1 / 54 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-138 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 54) h.gap138

theorem LateSignedDegree.gap12_ne {x : ℤ} (h : LateSignedDegree x 12)
    (hne : x ≠ -12) : x ≤ -76 ∨ 52 ≤ x := by
  have hm := h.integral
  have hl := h.lower
  change (x + 12) % 64 = 0 % 64 at hm
  omega

theorem LateSignedDegree.invBounds12_ne {x : ℤ} (h : LateSignedDegree x 12)
    (hne : x ≠ -12) : -1 / 76 ≤ lateInv x ∧ lateInv x ≤ 1 / 52 := by
  simpa [lateInv, div_eq_mul_inv] using lateInv_bounds (by norm_num : (-76 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 52) (h.gap12_ne hne)

end Stellmacher.Recognition.LyonsU3Four
