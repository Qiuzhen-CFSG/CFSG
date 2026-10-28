/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianWeightedNorm.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianIntegralNorm

/-!
# IcosianWeightedNorm

The rational part of the reduced norm is a positive definite rational
quadratic form, integral on the icosian order. Coordinate identities give
its real-coordinate bound and its behavior under translation.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianWeightedNorm.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

def icosianWeightedNorm (x : IcosianQuaternion) : ℚ := goldenFunctional (icosianNorm x)

theorem icosianWeightedNorm_eq (x : IcosianQuaternion) :
    icosianWeightedNorm x=icosianFunctional (star x*x) := by
  rw [Quaternion.star_mul_self]
  rfl

theorem icosianWeightedNorm_nonneg (x : IcosianQuaternion) : 0 ≤ icosianWeightedNorm x := by
  rw [icosianWeightedNorm_eq]
  exact icosianFunctional_star_mul_self_nonneg x

theorem icosianWeightedNorm_eq_zero (x : IcosianQuaternion) :
    icosianWeightedNorm x=0 ↔ x=0 := by
  rw [icosianWeightedNorm_eq]
  exact icosianFunctional_star_mul_self_eq_zero x

theorem icosianWeightedNorm_real_bound (x : IcosianQuaternion) :
    (goldenFunctional x.re)^2 ≤ icosianWeightedNorm x := by
  rw [icosianWeightedNorm_eq,icosianFunctional_star_mul_self]
  simp [goldenFunctional,pow_two]
  nlinarith [sq_nonneg x.re.im,sq_nonneg x.imI.re,sq_nonneg x.imI.im,
    sq_nonneg x.imJ.re,sq_nonneg x.imJ.im,sq_nonneg x.imK.re,sq_nonneg x.imK.im]

theorem icosianWeightedNorm_add_one (x : IcosianQuaternion) :
    icosianWeightedNorm (x+1)=icosianWeightedNorm x+2*goldenFunctional x.re+1 := by
  simp [icosianWeightedNorm,icosianNorm_coordinates,goldenFunctional,Quaternion.re_add,
    pow_two]
  ring

theorem icosianNorm_one_add_two (x : IcosianQuaternion) :
    icosianNorm (1+2*x)=1+4*x.re+4*icosianNorm x := by
  rw [icosianNorm_coordinates,icosianNorm_coordinates]
  simp [pow_two,QuaternionAlgebra.re_ofNat,QuaternionAlgebra.imI_ofNat,QuaternionAlgebra.imJ_ofNat,QuaternionAlgebra.imK_ofNat]
  ring

theorem icosianWeightedNorm_integral (x : icosianOrder) :
    icosianWeightedNorm x.val=((icosianIntegralNorm x).re : ℚ) := by
  rw [icosianWeightedNorm,← icosianIntegralNorm_spec]
  rfl

end Atlas.Algebra
