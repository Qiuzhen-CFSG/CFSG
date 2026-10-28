module
public import Theory.Analysis.InverseSqrtIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth approximations to square-root-time paths

For `τ > 0`, globally smooth real paths with values zero at time zero and
one at time `τ` approach weighted energy `1 / (2 * sqrt τ)`. This supplies
the upper-bound half of the Euclidean reduced-distance calculation in
Perelman's first paper, §7, while respecting global smoothness of the paths.
The limiting square-root-time path itself has a singular derivative at zero.

Use the profile `(s² + δ)^(1/4)` for `δ > 0`, written as two square roots.
Its derivative has square-root weighted square at most `1 / (4 * sqrt s)`
for `s > 0`. The reciprocal-square-root integral bounds the energy by
`sqrt τ / 2`. Subtract the initial value and divide by the endpoint difference;
as `δ` tends to zero, this difference tends to `sqrt τ`. Continuity chooses a
positive parameter giving any prescribed excess above the sharp bound.
-/

open Real MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace intervalIntegral

private def profile (δ s : ℝ) : ℝ := √(√(s ^ 2 + δ))
private def speed (δ s : ℝ) : ℝ := s / (2 * √(√(s ^ 2 + δ)) * √(s ^ 2 + δ))

private theorem profile_smooth {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (profile δ) := by
  apply ContDiff.sqrt
  · apply ContDiff.sqrt
    · exact (contDiff_id.pow 2).add contDiff_const
    · intro s; positivity
  · intro s; positivity

private theorem profile_deriv {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    HasDerivAt (profile δ) (speed δ s) s := by
  have hp : 0 < s ^ 2 + δ := by positivity
  have h := (((hasDerivAt_id s).pow 2).add_const δ).sqrt (ne_of_gt hp)
  have hh := h.sqrt (ne_of_gt (sqrt_pos.2 hp))
  convert hh using 1 <;> first | rfl | (dsimp [speed]; ring)

private theorem speed_energy_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    √s * (speed δ s) ^ 2 ≤ (√s)⁻¹ / 4 := by
  have hp : 0 < s ^ 2 + δ := by positivity
  have hr : 0 < √(s ^ 2 + δ) := sqrt_pos.2 hp
  have hq : 0 < √(√(s ^ 2 + δ)) := sqrt_pos.2 hr
  have ht : 0 < √s := sqrt_pos.2 hs
  have hr2 := sq_sqrt hp.le
  have hq2 := sq_sqrt hr.le
  have ht2 := sq_sqrt hs.le
  have hsr : s ≤ √(s ^ 2 + δ) := by nlinarith
  have hc : s ^ 3 ≤ (√(s ^ 2 + δ)) ^ 3 := pow_le_pow_left₀ hs.le hsr 3
  dsimp [speed]
  field_simp
  nlinarith

private theorem speed_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (speed δ) := by
  unfold speed
  apply continuous_id.div
  · fun_prop
  · intro s; positivity

private theorem profile_energy_le {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) :
    ∫ s in (0 : ℝ)..τ, √s * (speed δ s) ^ 2 ≤ √τ / 2 := by
  have he : IntervalIntegrable (fun s => √s * (speed δ s) ^ 2) volume 0 τ :=
    (continuous_sqrt.mul ((speed_continuous hδ).pow 2)).intervalIntegrable _ _
  have hi := integral_mono_on_of_le_Ioo hτ.le he
    ((intervalIntegrable_inv_sqrt 0 τ).div_const 4)
    (fun s hs => speed_energy_le hδ hs.1)
  rw [integral_div, integral_inv_sqrt] at hi
  linarith

private theorem exists_parameter {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < profile δ τ - profile δ 0 ∧
      (√τ / 2) / (profile δ τ - profile δ 0) ^ 2 < 1 / (2 * √τ) + ε := by
  let D := fun δ => profile δ τ - profile δ 0
  have hD : Continuous D := by unfold D profile; fun_prop
  have hD0 : D 0 = √τ := by simp [D, profile, sqrt_sq hτ.le]
  have hpos : 0 < √τ := sqrt_pos.2 hτ
  have hne : D 0 ^ 2 ≠ 0 := by rw [hD0]; positivity
  have hF : ContinuousAt (fun δ => (√τ / 2) / D δ ^ 2) 0 :=
    continuousAt_const.div (hD.continuousAt.pow 2) hne
  have hval : (√τ / 2) / D 0 ^ 2 = 1 / (2 * √τ) := by
    rw [hD0]
    field_simp
  have hlim : Tendsto (fun δ => (√τ / 2) / D δ ^ 2) (𝓝 0)
      (𝓝 (1 / (2 * √τ))) := by simpa only [hval] using hF.tendsto
  have he := hlim.eventually_lt_const (lt_add_of_pos_right _ hε)
  have hd : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < D δ :=
    (hD.continuousAt (x := 0)).tendsto.eventually_const_lt (by simpa only [hD0] using hpos)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ 0 < D δ ∧
      (√τ / 2) / D δ ^ 2 < 1 / (2 * √τ) + ε := by
    filter_upwards [self_mem_nhdsWithin, hd.filter_mono nhdsWithin_le_nhds,
      he.filter_mono nhdsWithin_le_nhds] with δ hδ hd he
    exact ⟨hδ, hd, he⟩
  exact hev.exists

public theorem exists_smooth_sqrt_energy_approx {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ f 0 = 0 ∧ f τ = 1 ∧
      (∫ s in (0 : ℝ)..τ, √s * (deriv f s) ^ 2) < 1 / (2 * √τ) + ε := by
  obtain ⟨δ, hδ, hD, hbound⟩ := exists_parameter hτ hε
  let D := profile δ τ - profile δ 0
  let f := fun s => (profile δ s - profile δ 0) / D
  have hd (s : ℝ) : deriv f s = speed δ s / D :=
    (((profile_deriv hδ s).sub_const (profile δ 0)).div_const D).deriv
  refine ⟨f, ((profile_smooth hδ).sub contDiff_const).div_const D, ?_, ?_, ?_⟩
  · simp [f]
  · exact div_self (ne_of_gt hD)
  · calc
      (∫ s in (0 : ℝ)..τ, √s * (deriv f s) ^ 2) =
          (∫ s in (0 : ℝ)..τ, √s * (speed δ s) ^ 2) / D ^ 2 := by
        simp_rw [hd, div_pow, ← mul_div_assoc]
        exact integral_div _ _
      _ ≤ (√τ / 2) / D ^ 2 := div_le_div_of_nonneg_right
        (profile_energy_le hδ hτ) (sq_nonneg D)
      _ < 1 / (2 * √τ) + ε := hbound
end intervalIntegral
