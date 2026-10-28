module
public import Theory.Analysis.InverseSqrtIntegral

/-!
# A sharp square-root weighted energy bound

For a continuous velocity on `[0, τ]`, the squared norm of its integral is
at most `2 * sqrt τ` times its square-root weighted kinetic energy. This is
the lower-bound ingredient for the Euclidean reduced-distance infimum in
Perelman's first paper, §7 (the L-length definition on p. 14).

Integrate `2 a ‖v‖ ≤ sqrt s ‖v‖² + a² / sqrt s` away from the null endpoint
zero, use the reciprocal-square-root integral, and optimize the constant `a`.
The norm inequality for the Bochner integral then gives the vector-valued
result. Only a real normed space is needed; no curvature or flow assumptions
enter this reusable estimate.
-/

open Real MeasureTheory Set
namespace intervalIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

public theorem norm_integral_sq_le_sqrt_energy {τ : ℝ} (hτ : 0 < τ)
    {v : ℝ → E} (hv : ContinuousOn v (Icc 0 τ)) :
    ‖∫ s in (0 : ℝ)..τ, v s‖ ^ 2 ≤
      (2 * √τ) * ∫ s in (0 : ℝ)..τ, √s * ‖v s‖ ^ 2 := by
  have hn : IntervalIntegrable (fun s => ‖v s‖) volume 0 τ := hv.norm.intervalIntegrable_of_Icc hτ.le
  have he : IntervalIntegrable (fun s => √s * ‖v s‖ ^ 2) volume 0 τ := (continuous_sqrt.continuousOn.mul (hv.norm.pow 2)).intervalIntegrable_of_Icc hτ.le
  let A := ∫ s in (0 : ℝ)..τ, ‖v s‖
  let B := ∫ s in (0 : ℝ)..τ, √s * ‖v s‖ ^ 2
  let C := 2 * √τ
  have hC : 0 < C := by dsimp [C]; positivity
  have hquad (a : ℝ) : 2 * a * A ≤ B + a ^ 2 * C := by
    have hi := integral_mono_on_of_le_Ioo hτ.le (hn.const_mul (2 * a))
      (he.add ((intervalIntegrable_inv_sqrt 0 τ).const_mul (a ^ 2)))
      (fun s hs => show 2 * a * ‖v s‖ ≤ √s * ‖v s‖ ^ 2 + a ^ 2 * (√s)⁻¹ from by
        have hsqrt : 0 < √s := sqrt_pos.2 hs.1
        have hsq := sq_nonneg (√s * ‖v s‖ - a)
        apply (mul_le_mul_iff_right₀ hsqrt).mp
        field_simp
        nlinarith)
    simpa only [integral_const_mul, integral_add he
      ((intervalIntegrable_inv_sqrt 0 τ).const_mul (a ^ 2)), integral_inv_sqrt,
      A, B, C] using hi
  have hbound : A ^ 2 ≤ C * B := by
    have h := hquad (A / C)
    have hc0 := ne_of_gt hC
    field_simp at h
    nlinarith
  have hnle : ‖∫ s in (0 : ℝ)..τ, v s‖ ≤ A := norm_integral_le_integral_norm hτ.le
  have hn0 := norm_nonneg (∫ s in (0 : ℝ)..τ, v s)
  change _ ≤ C * B
  nlinarith
end intervalIntegral
