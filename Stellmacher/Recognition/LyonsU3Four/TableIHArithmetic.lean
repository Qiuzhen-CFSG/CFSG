module

public import Stellmacher.Recognition.LyonsU3Four.TableIEarlyBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
/-!
# The arithmetic contradiction in Table I case H

Lyons's equations (H1) and (H2), together with the bounds furnished by signed
multiplicity and the degree congruences, force `x = -75` or `x = -139`.
Clearing denominators then gives impossible quadratic equations. The first
has negative discriminant; the second has no root in the allowed residue
class modulo 64.

Source: Lyons (1972), p. 383; the owning elimination module derives these
inputs from the displayed matrix.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four

private theorem upper_bound (n : ℤ) (a b C : ℚ) (hb : 0 < b) (hC : 0 ≤ C)
    (hn : (n : ℚ) ≤ -a ∨ b ≤ n) (ha : 0 < a) : C / n ≤ C / b := by
  rcases hn with hn | hn
  · have hneg : C / (n : ℚ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hC (by linarith)
    exact hneg.trans (by positivity)
  · exact div_le_div_of_nonneg_left hC hb hn

/-- The numerical system (H1)–(H2) has no signed integral solution. -/
theorem tableI_H_arithmetic (x y z : ℤ) (hx : x ≤ -75 ∨ 53 ≤ x)
    (hy : y ≤ -13 ∨ 51 ≤ y) (hz : z ≤ -27 ∨ 165 ≤ z)
    (hxm : (x+75)%64=0) (hzm : (z-165)%64=0)
    (h1 : 1+100/(x:ℚ)-18/(y:ℚ)-75/(z:ℚ)=0)
    (h2 : 1+4*x-2*y-3*z=0) : False := by
  have byy : (18:ℚ)/y ≤ 18/51 :=
    upper_bound y 13 51 18 (by norm_num) (by norm_num) (by exact_mod_cast hy) (by norm_num)
  have bzz : (75:ℚ)/z ≤ 75/165 :=
    upper_bound z 27 165 75 (by norm_num) (by norm_num) (by exact_mod_cast hz) (by norm_num)
  have xn : x ≤ -75 := by
    rcases hx with hx | hx
    · exact hx
    · have xp : (0:ℚ) ≤ 100/(x:ℚ) := div_nonneg (by norm_num) (by exact_mod_cast (show 0 ≤ x by omega))
      linarith
  have yz : y < 0 ∨ z < 0 := by omega
  have bx : (100:ℚ)/x ≤ -(1-75/165) := by
    rcases yz with yy | zz
    · have yn : (18:ℚ)/y ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by exact_mod_cast (show y ≤ 0 by omega))
      linarith
    · have zn : (75:ℚ)/z ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by exact_mod_cast (show z ≤ 0 by omega))
      linarith
  have xnq : (x:ℚ) < 0 := by exact_mod_cast (show x < 0 by omega)
  have xx : -(184:ℚ) < x := by
    have := (div_le_iff_of_neg xnq).mp bx
    linarith
  have xc : x = -75 ∨ x = -139 := by
    have : -184 < x := by exact_mod_cast xx
    omega
  have x0 : (x:ℚ) ≠ 0 := ne_of_lt xnq
  have y0 : (y:ℚ) ≠ 0 := by
    have : y ≠ 0 := by omega
    exact_mod_cast this
  have z0 : (z:ℚ) ≠ 0 := by
    have : z ≠ 0 := by omega
    exact_mod_cast this
  have hp : x*y*z+100*y*z-18*x*z-75*x*y=0 := by
    have hh : (x:ℚ)*y*z+100*y*z-18*x*z-75*x*y=0 := by
      field_simp at h1
      nlinarith [h1]
    exact_mod_cast hh
  have h2z := congrArg (fun n : ℤ => n*z) h2
  rcases xc with rfl | rfl
  · nlinarith [sq_nonneg (3*z+433)]
  · have hzpoly : 13*z^2-514*z-642875=0 := by nlinarith [hp, h2]
    have zl : -300 ≤ z := by nlinarith [sq_nonneg (z+300)]
    have zu : z ≤ 300 := by nlinarith [sq_nonneg (z-300)]
    have zz : z = -283 ∨ z = -219 ∨ z = -155 ∨ z = -91 ∨ z = -27 ∨
        z = 37 ∨ z = 101 ∨ z = 165 ∨ z = 229 ∨ z = 293 := by omega
    rcases zz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hzpoly

end Stellmacher.Recognition.LyonsU3Four
