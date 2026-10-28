module

public import Theory.Analysis.GaussianMoment
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A balanced radial Gaussian moment in Euclidean space

For a positive Gaussian coefficient, the integral of
`(2 * b * ‖x‖² - dim) * exp (-b * ‖x‖²)` vanishes in any finite dimension.
The volume-preserving map from product coordinates to Euclidean space reduces
this to Fubini's theorem. Expand the quadratic factor into a sum over
coordinates; each summand is a product with one balanced one-dimensional
factor, whose integral is zero by `integral_gaussian_quadratic_balance`.
All product factors are integrable, justifying the finite-sum interchange.

This is the moment cancellation in the Gaussian model for Perelman's
W-functional (Perelman I, §3); it does not require entropy monotonicity.
-/

namespace MeasureTheory

open Real
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

public theorem integral_gaussian_norm_balance {b : ℝ} (hb : 0 < b) :
    ∫ x : EuclideanSpace ℝ ι,
      (2 * b * ‖x‖ ^ 2 - (Fintype.card ι : ℝ)) * exp (-b * ‖x‖ ^ 2) = 0 := by
  classical
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [EuclideanSpace.real_norm_sq_eq]
  let f (i j : ι) (x : ℝ) := (if j = i then 2 * b * x ^ 2 - 1 else 1) * exp (-b * x ^ 2)
  have hf (i j : ι) : Integrable (f i j) := by
    by_cases h : j = i
    · simpa [f, h] using integrable_gaussian_quadratic_balance hb
    · simpa [f, h] using integrable_exp_neg_mul_sq hb
  have hprod (i : ι) (x : ι → ℝ) :
      (∏ j, f i j (x j)) = (2 * b * x i ^ 2 - 1) * exp (-b * ∑ j, x j ^ 2) := by
    simp only [f, Finset.prod_mul_distrib]
    simp [← Real.exp_sum, Finset.mul_sum]
  have hsum (x : ι → ℝ) :
      (2 * b * (∑ i, x i ^ 2) - (Fintype.card ι : ℝ)) * exp (-b * ∑ i, x i ^ 2) =
        ∑ i, ∏ j, f i j (x j) := by
    simp_rw [hprod]
    rw [← Finset.sum_mul]
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [hsum]
  rw [integral_finsetSum _ (fun i _ => by
    simpa only [volume_pi] using Integrable.fintype_prod (hf i))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_fintype_prod_volume_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [f] using integral_gaussian_quadratic_balance hb

end
end MeasureTheory
