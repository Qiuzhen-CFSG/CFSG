module
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Continuous evaluation of parametric manifold derivatives

For a smooth family `f(p, x)` and a smooth base map `g(p)`, the derivative in
`x`, evaluated on a continuous tangent vector along `g`, is continuous as a
vector in the target tangent bundle. This local statement does not require
a globally chosen norm on tangent fibres or a smooth input vector field.

Mathlib proves smoothness of the parametric derivative in tangent coordinates.
Its continuous bundle-evaluation theorem then applies to the given vector.
The result supplies joint continuity of slice-energy densities for smooth
sweepouts in Colding–Minicozzi §1.1.
-/

open Bundle
open scoped Manifold ContDiff
namespace Manifold
variable {E E' F H H' K M M' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' M'] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ F K}
  [IsManifold I ∞ M] [IsManifold I' ∞ M'] [IsManifold J ∞ N]

public theorem continuousAt_parametric_mfderiv_apply
    (f : N → M → M') (g : N → M) (v : ∀ p, TangentSpace I (g p)) (p : N)
    (hf : ContMDiffAt (J.prod I) I' ∞ (Function.uncurry f) (p, g p))
    (hg : ContMDiffAt J I ∞ g p)
    (hv : ContinuousAt (fun q => TotalSpace.mk' E (g q) (v q)) p) :
    ContinuousAt (fun q => TotalSpace.mk' E' (f q (g q))
      (mfderiv I I' (f q) (g q) (v q))) p := by
  have hD := (hf.mfderiv f g hg (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)).continuousAt
  have hbase : ContinuousAt (fun q => f q (g q)) p := by
    exact hf.continuousAt.comp (f := fun q : N => (q, g q)) (continuousAt_id.prodMk hg.continuousAt)
  exact ContinuousAt.clm_apply_of_inCoordinates hD hv hbase
end Manifold
