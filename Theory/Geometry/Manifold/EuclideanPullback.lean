module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Euclidean inner products pulled back to tangent bundles

For a smooth map from a real smooth manifold to an inner product space, the
ambient inner product of its two differential images is a smooth tangent
bilinear form. No injectivity or finite-dimensionality hypothesis is needed
for this smoothness assertion. An immersion makes the form positive definite;
in particular this construction supplies the usual round metric on a sphere.

The proof uses Mathlib's `ContMDiffAt.mfderiv_const`: in a tangent chart the
differential is a smooth operator-valued function `A`. The bilinear form in
the induced Hom-bundle chart is obtained by composing the ambient inner
product with `A` in each argument, so smoothness follows from smooth operator
composition. We use continuous linear precomposition, which does not require
choosing a norm on the tangent fibres.
-/

namespace Manifold

open Bundle Set
open scoped Manifold Bundle ContDiff Topology

noncomputable section

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private def ambientInner : F →L[ℝ] F →L[ℝ] ℝ :=
  (innerSL ℝ (E := F)).bilinearComp (.id ℝ F) (.id ℝ F)

/-- The ambient Euclidean inner product pulled back by the differential. -/
public def euclideanPullbackForm (f : M → F) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mvfderiv I f x)).comp
    (ambientInner.comp (mvfderiv I f x))

@[simp]
public theorem euclideanPullbackForm_apply (f : M → F) (x : M)
    (v w : TangentSpace I x) :
    euclideanPullbackForm f x v w = inner ℝ (mvfderiv I f x v) (mvfderiv I f x w) := by
  simp [euclideanPullbackForm, ambientInner, ContinuousLinearMap.precomp_apply]

/-- Pulling back an inner product by a smooth map gives a smooth section of
the tangent bilinear-form bundle. -/
public theorem contMDiff_euclideanPullbackForm [IsManifold I ∞ M]
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (euclideanPullbackForm (I := I) f x)) := by
  intro x
  apply contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_id, ?_⟩
  let A := fun y => (mvfderiv I f y).comp
    ((trivializationAt E (TangentSpace I) x).symmL ℝ y)
  have hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ A x := by
    have h := (hf x).mfderiv_const (m := ∞) (by simp)
    apply h.congr_of_eventuallyEq
    filter_upwards [] with y
    ext v
    simp [A, inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
      NormedSpace.fromTangentSpace]
    rfl
  have hq : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun y => (ContinuousLinearMap.precomp ℝ (A y)).comp
        (ambientInner.comp (A y))) x :=
    (hA.clm_precomp (F₃ := ℝ)).clm_comp
      ((contMDiffAt_const (c := (ambientInner : F →L[ℝ] F →L[ℝ] ℝ))).clm_comp hA)
  apply hq.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem]
  · simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.comp_apply]
    rfl
  · simpa using hy

end
end Manifold
