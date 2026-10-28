module
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Dini comparison with interior derivative hypotheses

This module proves a fencing inequality for continuous real functions on a closed
interval. A strict initial inequality allows the slope and boundary derivative
hypotheses to be imposed only on the open interval, so no derivative at the
initial endpoint is needed.

The proof uses continuity to choose a point strictly after the initial endpoint
where the initial inequality still holds. Mathlib's
`image_le_of_liminf_slope_right_lt_deriv_boundary'` then compares the functions
on the remaining interval. This is an endpoint variant of the one-dimensional
fencing inequalities in `Mathlib.Analysis.Calculus.MeanValue`.
-/

open Set Filter
open scoped Topology

/-- A strict initial inequality and an interior Dini slope bound prevent a
continuous function from crossing a continuous differentiable boundary. -/
public theorem image_le_of_liminf_slope_right_lt_deriv_boundary_interior
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a < B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ioo a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ioo a b, f x = B x → f' x < B' x) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · exact ha.le
  have hab : a < b := hax.trans_le hx.2
  have hstrict : ∀ᶠ y in 𝓝[Icc a b] a, f y < B y :=
    (hf.prodMk hB) a ⟨le_rfl, hab.le⟩
      (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) ha)
  have hstrict_right : ∀ᶠ y in 𝓝[>] a, f y < B y :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl, hab⟩) hstrict
  obtain ⟨c, hc, hac, hcx⟩ :=
    (hstrict_right.and (Ioc_mem_nhdsGT hax)).exists
  have hsub : Icc c b ⊆ Icc a b := fun y hy => ⟨hac.le.trans hy.1, hy.2⟩
  have hsub' : Ico c b ⊆ Ioo a b := fun y hy => ⟨hac.trans_le hy.1, hy.2⟩
  exact image_le_of_liminf_slope_right_lt_deriv_boundary'
    (hf.mono hsub) (fun y hy => hf' y (hsub' hy)) hc.le (hB.mono hsub)
    (fun y hy => hB' y (hsub' hy)) (fun y hy => bound y (hsub' hy)) ⟨hcx, hx.2⟩
