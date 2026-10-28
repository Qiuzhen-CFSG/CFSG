/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormDiscriminant.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianWeightedNorm

/-!
# IcosianNormDiscriminant

The discriminant norm of a quaternion norm is nonnegative. A rational
sum-of-squares identity proves the bound, which restricts the golden
coefficient when the real integral norm is one or two.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormDiscriminant.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

/-- Positivity at the two golden embeddings, expressed without choosing real
embeddings: the discriminant norm is a sum of seven rational squares. -/
theorem icosianNorm_discriminant_nonneg (x : IcosianQuaternion) :
    0 ≤ (icosianNorm x).re^2+(icosianNorm x).re*(icosianNorm x).im-
      (icosianNorm x).im^2 := by
  let p := x.re.re^2+x.imI.re^2+x.imJ.re^2+x.imK.re^2
  let q := x.re.im^2+x.imI.im^2+x.imJ.im^2+x.imK.im^2
  let r := x.re.re*x.re.im+x.imI.re*x.imI.im+x.imJ.re*x.imJ.im+x.imK.re*x.imK.im
  have he : (icosianNorm x).re^2+(icosianNorm x).re*(icosianNorm x).im-
      (icosianNorm x).im^2 = (p-q+r)^2+5*((x.re.re*x.imI.im-x.imI.re*x.re.im)^2+
      (x.re.re*x.imJ.im-x.imJ.re*x.re.im)^2+
      (x.re.re*x.imK.im-x.imK.re*x.re.im)^2+
      (x.imI.re*x.imJ.im-x.imJ.re*x.imI.im)^2+
      (x.imI.re*x.imK.im-x.imK.re*x.imI.im)^2+
      (x.imJ.re*x.imK.im-x.imK.re*x.imJ.im)^2) := by
    simp [icosianNorm_coordinates,p,q,r,pow_two]
    ring
  rw [he]
  positivity

theorem icosianIntegralNorm_discriminant_nonneg (x : icosianOrder) :
    0 ≤ (icosianIntegralNorm x).re^2+
      (icosianIntegralNorm x).re*(icosianIntegralNorm x).im-
      (icosianIntegralNorm x).im^2 := by
  have h := icosianNorm_discriminant_nonneg x.val
  rw [← icosianIntegralNorm_spec] at h
  change (0 : ℚ) ≤ ((icosianIntegralNorm x).re : ℚ)^2+
    ((icosianIntegralNorm x).re : ℚ)*(icosianIntegralNorm x).im-
    ((icosianIntegralNorm x).im : ℚ)^2 at h
  exact_mod_cast h

theorem icosianIntegralNorm_real_nonneg (x : icosianOrder) :
    0 ≤ (icosianIntegralNorm x).re := by
  have h := icosianWeightedNorm_nonneg x.val
  rw [icosianWeightedNorm_integral] at h
  exact_mod_cast h

theorem icosianIntegralNorm_real_zero (x : icosianOrder) :
    (icosianIntegralNorm x).re=0 ↔ x=0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply (icosianWeightedNorm_eq_zero x.val).mp
    rw [icosianWeightedNorm_integral,h]
    norm_num
  · rintro rfl
    have h := icosianIntegralNorm_spec (0 : icosianOrder)
    have hr := congrArg QuadraticAlgebra.re h
    simpa [icosianNorm_coordinates,goldenIntegerToRational] using hr

theorem icosianIntegralNorm_im_of_real_one (x : icosianOrder)
    (hx : (icosianIntegralNorm x).re=1) :
    (icosianIntegralNorm x).im=0 ∨ (icosianIntegralNorm x).im=1 := by
  have h := icosianIntegralNorm_discriminant_nonneg x
  rw [hx] at h
  have hb : 0 ≤ (icosianIntegralNorm x).im ∧ (icosianIntegralNorm x).im ≤ 1 := by
    constructor <;> nlinarith
  omega

theorem icosianIntegralNorm_im_of_real_two (x : icosianOrder)
    (hx : (icosianIntegralNorm x).re=2) :
    -1 ≤ (icosianIntegralNorm x).im ∧ (icosianIntegralNorm x).im ≤ 3 := by
  have h := icosianIntegralNorm_discriminant_nonneg x
  rw [hx] at h
  constructor <;> nlinarith

end Atlas.Algebra
