/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianIntegralNorm.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianIntegralCoordinates

/-!
# IcosianIntegralNorm

The reduced norm of an integral icosian is a golden integer. An explicit
quadratic polynomial in the four basis coefficients gives the integral norm
and proves compatibility with the quaternion norm.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianIntegralNorm.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped QuadraticAlgebra Quaternion

def icosianCoefficientNorm {R : Type*} [CommRing R] (t : R) (a : Fin 4 → R) : R :=
  (a 0)^2+(a 1)^2+(a 2)^2+(a 3)^2+a 0*a 2+(t-1)*a 0*a 3+(1-t)*a 1*a 2+a 1*a 3

theorem icosianNorm_coefficients (x : IcosianQuaternion) :
    icosianNorm x=icosianCoefficientNorm goldenTau (icosianBasisCoefficients x) := by
  ext <;> simp [icosianNorm_coordinates,icosianCoefficientNorm,icosianBasisCoefficients,
    goldenTau,goldenSigma,QuadraticAlgebra.omega,pow_two] <;> ring

def icosianIntegralNorm (x : icosianOrder) : GoldenInteger :=
  icosianCoefficientNorm QuadraticAlgebra.omega (icosianIntegralCoefficients x)

theorem icosianIntegralNorm_spec (x : icosianOrder) :
    goldenIntegerToRational (icosianIntegralNorm x)=icosianNorm x.val := by
  rw [icosianNorm_coefficients]
  have ht : goldenIntegerToRational (QuadraticAlgebra.omega : GoldenInteger)=goldenTau := rfl
  simp [icosianIntegralNorm,icosianCoefficientNorm,ht,icosianIntegralCoefficients_spec]

theorem icosianIntegralNorm_eq_one (x : icosianOrder) :
    icosianIntegralNorm x=1 ↔ icosianNorm x.val=1 := by
  rw [← icosianIntegralNorm_spec,← map_one goldenIntegerToRational]
  exact goldenIntegerToRational_injective.eq_iff.symm

end Atlas.Algebra
