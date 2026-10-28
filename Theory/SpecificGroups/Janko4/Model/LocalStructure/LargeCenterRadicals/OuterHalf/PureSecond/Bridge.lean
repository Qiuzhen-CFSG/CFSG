module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.MixedPairs
import Mathlib.Tactic.LinearCombination

/-!
# Comparison through three first-class involutions

If z, xz and yz are first-class involutions commuting with x and y, the
already established mixed comparisons and six row-linearity identities give
symmetry for x,y. This is the algebraic bridge consumed by the certified
pure-second-class calculation. Source: Kleidman--Wilson (1988), p.487,
Corollary 1.1.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem first_order (x : Model) (h : IsConj Janko4.a x) : orderOf x = 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq Janko4.a).trans Janko4.orderOf_a

private theorem first_value_symm (x y : Model) (hx : IsConj Janko4.a x)
    (hy : orderOf y = 2) (hc : Commute x y) : outerValue x y = outerValue y x := by
  have hx1 : x ≠ 1 := by intro he; simpa [he] using first_order x hx
  have hy1 : y ≠ 1 := by intro he; simp [he] at hy
  have hr := innerRelated_symm_of_first x y hx hy hc
  unfold outerValue
  by_cases hxy : InnerRelated x y
  · rw [if_pos (Or.inr hxy), if_pos (Or.inr (hr.mp hxy))]
  · rw [if_neg (not_or.mpr ⟨hx1, hxy⟩),
      if_neg (not_or.mpr ⟨hy1, fun h => hxy (hr.mpr h)⟩)]

/-- A commuting first-class bridge compares the two remaining rows. -/
theorem innerRelated_symm_of_first_bridge (x y z : Model)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : Commute x y)
    (hxz : Commute x z) (hyz : Commute y z)
    (hz : IsConj Janko4.a z) (hxp : IsConj Janko4.a (x * z))
    (hyp : IsConj Janko4.a (y * z)) :
    InnerRelated x y ↔ InnerRelated y x := by
  have hoz := first_order z hz
  have hoxp := first_order (x * z) hxp
  have hoyp := first_order (y * z) hyp
  have hcx : Commute (y * z) x := hxy.symm.mul_left hxz.symm
  have hcy : Commute (x * z) y := hxy.mul_left hyz.symm
  have hczx : Commute (x * z) z := hxz.mul_left (Commute.refl z)
  have hczy : Commute (y * z) z := hyz.mul_left (Commute.refl z)
  have hcp : Commute (y * z) (x * z) := hcx.mul_right hczy
  have he := first_value_symm (y * z) (x * z) hyp hoxp hcp
  rw [outerValue_mul_right (y * z) hoyp x z hcx hczy,
    outerValue_mul_right (x * z) hoxp y z hcy hczx,
    first_value_symm (y * z) x hyp hx hcx,
    first_value_symm (y * z) z hyp hoz hczy,
    first_value_symm (x * z) y hxp hy hcy,
    first_value_symm (x * z) z hxp hoz hczx,
    outerValue_mul_right x hx y z hxy hxz,
    outerValue_mul_right z hoz y z hyz.symm (Commute.refl z),
    outerValue_mul_right y hy x z hxy.symm hyz,
    outerValue_mul_right z hoz x z hxz.symm (Commute.refl z),
    first_value_symm z y hz hy hyz.symm,
    first_value_symm z x hz hx hxz.symm] at he
  have hv : outerValue x y = outerValue y x := by linear_combination he
  have hx1 : x ≠ 1 := by intro hh; simp [hh] at hx
  have hy1 : y ≠ 1 := by intro hh; simp [hh] at hy
  rw [← outerValue_eq_zero_iff x y hx1, ← outerValue_eq_zero_iff y x hy1, hv]

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
