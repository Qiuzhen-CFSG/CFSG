module
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The numerical reduction in Wong's characteristic-three argument

Write `x = ε f₁` and `y = ε₂ f₆` for the signed degrees. Wong's quadratic
equation factors into the two alternatives in his equation (10). Integrality
excludes the first factor, using `x ≡ 2 mod 8` and `x ≠ 2`. The second gives
`x - 8 ∣ 72`, hence `x = 10` or `x = 26`. Equation (9), with the odd normal
subgroup trivial, then gives the group orders 7920 and 5616.

This module proves only these integer implications, including the small
sum-of-squares calculations in Table 2. The character construction must supply
the equations and congruence; they are explicit hypotheses here. In particular
this module does not assert the existence of any character or recognize a group.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2, J. Austral. Math. Soc. 4 (1964), pp. 99–101,
equations (6)–(10), DOI:10.1017/S1446788700022771.
-/

namespace ABG

/-- The first row of Wong's generalized decomposition numbers is forced. -/
public theorem three_first_decomposition_parameters (b d : ℤ)
    (h : 1 + b^2 + (b+1)^2 + b^2 + b^2 + (d-b)^2 + (3-d)^2 + d^2 ≤ 8) :
    b = 0 ∧ d = 1 := by
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (d-b), sq_nonneg (3-d), sq_nonneg d]
  have hd : 0 ≤ d ∧ d ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (b+1), sq_nonneg b, sq_nonneg (d-b)]
  rcases hb with ⟨hbl, hbu⟩
  rcases hd with ⟨hdl, hdu⟩
  interval_cases b <;> interval_cases d <;> norm_num at *

/-- Even the weaker printed bound eight in equation (7) forces the second row.
The resulting sum is six, the Cartan invariant in equation (5). -/
public theorem three_second_decomposition_parameters (c e : ℤ)
    (h : c^2 + c^2 + (c-2)^2 + (c-2)^2 + (e-c)^2 + (2-e)^2 + e^2 ≤ 8) :
    c = 1 ∧ e = 1 := by
  have hc : 0 ≤ c ∧ c ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (e-c), sq_nonneg (2-e), sq_nonneg e]
  have he : 0 ≤ e ∧ e ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg c, sq_nonneg (c-2), sq_nonneg (e-c)]
  rcases hc with ⟨hcl, hcu⟩
  rcases he with ⟨hel, heu⟩
  interval_cases c <;> interval_cases e <;> norm_num at *

/-- The divisibility and congruence on the signed first degree have two solutions. -/
public theorem three_signed_degree_cases (x : ℤ)
    (hcong : 8 ∣ x - 2) (hdiv : x - 8 ∣ 72) (hne : x ≠ 2) :
    x = 10 ∨ x = 26 := by
  have hbound := Int.natAbs_le_of_dvd_ne_zero hdiv (by norm_num : (72 : ℤ) ≠ 0)
  norm_num at hbound
  have hlo : -64 ≤ x := by omega
  have hhi : x ≤ 80 := by omega
  interval_cases x <;> norm_num at *

/-- The first factor in Wong (10) is impossible for an integral signed degree. -/
public theorem three_degree_quadratic_reduction (x y : ℤ)
    (hcong : 8 ∣ x - 2) (hne : x ≠ 2)
    (hquad : y^2 * (2*x-1) * (x-8) + 2*y*(x+1)*(x^2-16*x+4) -
      16*x*(x+1)^2 = 0) :
    (x-8)*y = 8*(x+1) := by
  have hfac : ((2*x-1)*y + 2*x*(x+1)) * ((x-8)*y - 8*(x+1)) = 0 := by
    nlinarith only [hquad]
  rcases mul_eq_zero.mp hfac with hbad | hgood
  · have hdiv : 2*x-1 ∣ 3 := by
      refine ⟨-2*(y+x+1)-1, ?_⟩
      nlinarith only [hbad]
    have hb := Int.natAbs_le_of_dvd_ne_zero hdiv (by norm_num : (3 : ℤ) ≠ 0)
    norm_num at hb
    have hlo : -1 ≤ x := by omega
    have hhi : x ≤ 2 := by omega
    interval_cases x <;> norm_num at *
  · linear_combination hgood

/-- Equations (9) and (10) give both signed degrees and the group order.
The order equation here is equation (9) with `a = a₁ = 1`. -/
public theorem three_degree_order_alternatives (g : ℕ) (x y : ℤ)
    (hcong : 8 ∣ x - 2) (hne : x ≠ 2)
    (hquad : y^2 * (2*x-1) * (x-8) + 2*y*(x+1)*(x^2-16*x+4) -
      16*x*(x+1)^2 = 0)
    (horder : (g : ℤ) * (x-2)^2 = 4608*x*(x+1)) :
    (x = 10 ∧ y = 44 ∧ g = 7920) ∨ (x = 26 ∧ y = 12 ∧ g = 5616) := by
  have hlinear := three_degree_quadratic_reduction x y hcong hne hquad
  have hdiv : x-8 ∣ 72 := by
    refine ⟨y-8, ?_⟩
    nlinarith only [hlinear]
  rcases three_signed_degree_cases x hcong hdiv hne with rfl | rfl
  · left
    norm_num at hlinear horder ⊢
    omega
  · right
    norm_num at hlinear horder ⊢
    omega

/-- Evaluating the five induced-character identities at the identity determines
all seven signed degrees. The fifth character has negative sign in both cases. -/
public theorem three_seven_signed_degree_alternatives (g : ℕ) (z : Fin 7 → ℤ)
    (h₁ : 1 + z 0 - z 1 = 0) (h₂ : z 0 - z 2 = 0) (h₃ : z 2 - z 3 = 0)
    (h₄ : z 1 + z 4 + z 5 = 0) (h₅ : z 0 + z 4 + z 6 = 0)
    (hcong : 8 ∣ z 0 - 2)
    (hquad : (z 5)^2 * (2*z 0-1) * (z 0-8) +
      2*z 5*(z 0+1)*((z 0)^2-16*z 0+4) - 16*z 0*(z 0+1)^2 = 0)
    (horder : (g : ℤ) * (z 0-2)^2 = 4608*z 0*(z 0+1)) :
    (z = ![10,11,10,10,-55,44,45] ∧ g = 7920) ∨
      (z = ![26,27,26,26,-39,12,13] ∧ g = 5616) := by
  have hne : z 0 ≠ 2 := by
    intro h
    norm_num [h] at horder
  rcases three_degree_order_alternatives g (z 0) (z 5) hcong hne hquad horder with
    ⟨hx, hy, hg⟩ | ⟨hx, hy, hg⟩
  · left
    refine ⟨?_, hg⟩
    ext i
    fin_cases i <;> simp <;> omega
  · right
    refine ⟨?_, hg⟩
    ext i
    fin_cases i <;> simp <;> omega

end ABG
