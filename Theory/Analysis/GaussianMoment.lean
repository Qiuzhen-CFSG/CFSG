module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.Ring

/-!
# A balanced quadratic Gaussian moment on the real line

For a positive Gaussian coefficient, the quadratic expression
`(2 * b * x² - 1) * exp (-b * x²)` is integrable and has integral zero.
It is the derivative of `-x * exp (-b * x²)`. Both this primitive and its
derivative are integrable, so the whole-line fundamental theorem of calculus
applies. This supplies the one-coordinate identity used in the Euclidean
Gaussian entropy calculation (Perelman I, §3).
-/

namespace MeasureTheory

open Real
public theorem integrable_gaussian_quadratic_balance {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (2 * b * x ^ 2 - 1) * exp (-b * x ^ 2)) := by
  have h2 : Integrable (fun x : ℝ => x ^ 2 * exp (-b * x ^ 2)) := by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (show (-1 : ℝ) < 2 by norm_num))
  convert (h2.const_mul (2 * b)).sub (integrable_exp_neg_mul_sq hb) using 1
  ext x
  simp only [Pi.sub_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
public theorem integral_gaussian_quadratic_balance {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, (2 * b * x ^ 2 - 1) * exp (-b * x ^ 2) = 0 := by
  refine integral_eq_zero_of_hasDerivAt_of_integrable
    (f := fun x : ℝ => -x * exp (-b * x ^ 2)) ?_
    (integrable_gaussian_quadratic_balance hb) ?_
  · intro x
    convert! ((hasDerivAt_id x).neg.mul
      (((hasDerivAt_id x).pow 2).const_mul (-b)).exp) using 1
    simp only [Pi.pow_apply, Pi.neg_apply, id_eq]
    ring
  · convert! (integrable_mul_exp_neg_mul_sq hb).neg using 1
    funext x
    change -x * exp (-b * x ^ 2) = -(x * exp (-b * x ^ 2))
    ring
end MeasureTheory
