module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Integrating the reciprocal square root

The reciprocal of the real square root is integrable on every bounded
interval. Its integral from zero to `τ` is `2 * sqrt τ`; the convention that
`sqrt` is zero on negative inputs makes this valid for all real endpoints.
Rewrite the integrand as the real power with exponent `-1/2` and use the
power integrability and integration formulas.

These elementary facts control the time-zero singularity in the weighted
energy appearing in Perelman's reduced length (Paper I, §7).
-/

namespace intervalIntegral
open Real MeasureTheory
private theorem inv_sqrt_eq (x : ℝ) : (√x)⁻¹ = x ^ (-1 / 2 : ℝ) := by
  rw [← sqrt_inv, sqrt_eq_rpow, ← rpow_neg_eq_inv_rpow]
  congr 1
  ring
public theorem intervalIntegrable_inv_sqrt (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => (√s)⁻¹) volume a b := by
  simp_rw [inv_sqrt_eq]
  exact intervalIntegrable_rpow' (by norm_num)
public theorem integral_inv_sqrt (τ : ℝ) :
    ∫ s in (0 : ℝ)..τ, (√s)⁻¹ = 2 * √τ := by
  simp_rw [inv_sqrt_eq]
  rw [integral_rpow (Or.inl (show (-1 : ℝ) < -1 / 2 by norm_num))]
  norm_num [sqrt_eq_rpow]
  ring
end intervalIntegral
